{-# LANGUAGE GADTs #-}

{- | The @value@ constant: cardano-uplc against plutus-core.

A value is converted to plutus-core's type and back, so the comparison is on
values as well as on bytes. Three families:

* values from the package's generator, which plutus-core must write as the
  same bytes and read back as the same value;
* values built on plutus-core's side from its own smart constructors, which
  cardano-uplc must read back as the same value;
* hand-built programs that break each rule of the type, for the decoders to
  compare through the same check as every other family.
-}
module Value (valueReport, valueCases) where

import Cardano.UPLC.Constant (Constant (CValue))
import Cardano.UPLC.Flat qualified as U
import Cardano.UPLC.Name qualified as U
import Cardano.UPLC.Term qualified as U
import Cardano.UPLC.Value qualified as U
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Numeric (showHex)
import Numeric.Natural (Natural)
import PlutusCore.Default (DefaultFun, DefaultUni (..))
import PlutusCore.Flat (flat, unflat)
import PlutusCore.Value qualified as P
import Test.QuickCheck (Gen, choose, elements, generate, oneof, vectorOf)
import Universe (Some (..), ValueOf (..))
import UntypedPlutusCore qualified as P

import Bits
import Convert (fromPlutusValue, toPlutusValue)
import Gen (genValue)

type Ref = P.UnrestrictedProgram P.DeBruijn DefaultUni DefaultFun ()

theirProgram :: P.Value -> Ref
theirProgram v = P.UnrestrictedProgram (P.Program () (P.Version 1 1 0) (P.Constant () (Some (ValueOf DefaultUniValue v))))

cuProgram :: U.Value -> U.Program U.DeBruijn ()
cuProgram v = U.Program () (U.Version 1 1 0) (U.Constant () (CValue v))

hex :: ByteString -> String
hex = concatMap (\w -> let s = showHex w "" in if length s == 1 then '0' : s else s) . BS.unpack

-- Values built on plutus-core's side, through its own constructors, with
-- the same edges as the package's generator.
genTheirs :: Gen P.Value
genTheirs = do
  currencies <- choose (0, 4)
  entries <- vectorOf currencies ((,) <$> genKey <*> (choose (0, 4) >>= flip vectorOf ((,) <$> genKey <*> genQty)))
  pure (P.pack (Map.fromList [(c, Map.fromList ts) | (c, ts) <- entries]))
  where
    genKey = do
      len <- elements [0, 1, 1, 2, 31, 32]
      fromJust . P.k . BS.pack <$> vectorOf len (elements [0, 1, 0xff])
    genQty =
      fromJust . P.quantity
        <$> oneof
          [ choose (-3, 3)
          , choose (2 ^ (63 :: Int) - 2, 2 ^ (63 :: Int) + 2)
          , choose (2 ^ (127 :: Int) - 3, 2 ^ (127 :: Int) - 1)
          , choose (-(2 ^ (127 :: Int)), -(2 ^ (127 :: Int)) + 2)
          ]

valueReport :: Int -> IO Bool
valueReport n = do
  cus <- generate (vectorOf n genValue)
  theirs <- generate (vectorOf n genTheirs)
  let fromCu v =
        let b = U.encodeProgram (cuProgram v)
            ref = flat (theirProgram (toPlutusValue v))
         in if b /= ref
              then Just ("encoders differ: " <> hex b <> " and " <> hex ref)
              else case either (Left . show) Right (unflat b) :: Either String Ref of
                Left e -> Just ("plutus-core refuses cardano-uplc's bytes " <> hex b <> ": " <> take 120 (show e))
                Right (P.UnrestrictedProgram (P.Program _ _ (P.Constant _ (Some (ValueOf DefaultUniValue w))))) | fromPlutusValue w /= v -> Just ("plutus-core reads " <> hex b <> " as another value")
                _ -> Nothing
      fromTheirs v =
        let b = flat (theirProgram v)
         in case U.decodeProgram b of
              Left e -> Just ("cardano-uplc refuses " <> hex b <> ": " <> show e)
              Right (U.Program _ _ (U.Constant _ (CValue w))) | toPlutusValue w == v -> Nothing
              Right _ -> Just ("cardano-uplc reads " <> hex b <> " as another value")
      bad1 = [m | Just m <- map fromCu cus]
      bad2 = [m | Just m <- map fromTheirs theirs]
  putStrLn $ "value constants, cardano-uplc to plutus-core: " <> show n <> " values, " <> show (length bad1) <> " disagreements"
  putStrLn $ "value constants, plutus-core to cardano-uplc: " <> show n <> " values, " <> show (length bad2) <> " disagreements"
  mapM_ (putStrLn . ("  DISAGREE " <>)) (take 10 (bad1 <> bad2))
  pure (null bad1 && null bad2)

-- A program holding a value, from the bytes plutus-core's flat writes for
-- that value on its own: after the first byte the two are the same bytes, so
-- long as the list is not empty.
valueProgram :: ByteString -> ByteString
valueProgram alone = BS.pack [0x01, 0x01, 0x00, 0x4e, 0xa1] <> BS.drop 1 alone

zigzag :: Integer -> Natural
zigzag n = fromInteger (if n >= 0 then 2 * n else -2 * n - 1)

-- One program whose value list is written as given: currency keys and token
-- names as bytes, quantities with a count of extra zero groups.
build :: [(ByteString, [(ByteString, Integer, Int)])] -> ByteString
build cs = toBytes (filler 0 (foldl currency start cs ++ [False]))
  where
    start = natPadded 0 1 ++ natPadded 0 1 ++ natPadded 0 0 ++ bits 4 4 ++ concatMap (\t -> True : bits 4 t) [13] ++ [False]
    currency acc (c, ts) = foldl token (key (acc ++ [True]) c) ts ++ [False]
    token acc (t, q, extra) = key (acc ++ [True]) t ++ natPadded extra (zigzag q)
    key acc k = filler 0 acc ++ chunks [k]

-- Programs that break each rule of the type, and some that do not, built
-- with the separate bit writer so they may be malformed in ways the
-- package's writer cannot be.
valueCases :: [(String, ByteString)]
valueCases = written <> shapes
  where
    written =
      [ (label, valueProgram (unhex bytes))
      | (label, bytes) <-
          [ ("flat: currency of 32 bytes", "8120" <> concat (replicate 32 "01") <> "00810174000201")
          , ("flat: zero quantity", "81016300810174000001")
          , ("flat: quantity 2^127", "81016300810174008080808080808080808080808080808080800401")
          , ("flat: quantity -2^127-1", "81016300810174008180808080808080808080808080808080800401")
          , ("flat: empty inner list", "8101630001")
          , ("flat: currencies descending", "81016200810174000241016100810174000201")
          , ("flat: tokens repeated", "810163008101610002810161000401")
          , ("flat: shorter key first", "8101610081017400024102610000810174000201")
          , ("flat: padded 5", "81016300810174008a0001")
          , ("flat: padded 0", "8101630081017400800001")
          ]
      ]
    keys = [BS.empty, BS.pack [0x61], BS.pack [0x61, 0x00], BS.pack [0x62], BS.replicate 32 0xff, BS.replicate 33 0xff]
    qtys = [0, 1, -1, 2 ^ (127 :: Int) - 1, 2 ^ (127 :: Int), -(2 ^ (127 :: Int)), -(2 ^ (127 :: Int)) - 1]
    t1 = BS.pack [0x74]
    shapes =
      [("one coin, currency " <> hex c <> " token " <> hex t <> " quantity " <> show q <> " +" <> show e, build [(c, [(t, q, e)])]) | c <- keys, t <- keys, q <- qtys, e <- [0, 1]]
        <> [("two currencies " <> hex a <> " " <> hex b, build [(a, [(t1, 1, 0)]), (b, [(t1, 1, 0)])]) | a <- keys, b <- keys]
        <> [("two tokens " <> hex a <> " " <> hex b, build [(t1, [(a, 1, 0), (b, 1, 0)])]) | a <- keys, b <- keys]
        <> [("empty token list for " <> hex c, build [(c, [])]) | c <- keys]
        <> [("an empty token list in the middle", build [(BS.pack [0x61], [(t1, 1, 0)]), (BS.pack [0x62], []), (BS.pack [0x63], [(t1, 1, 0)])])]
        <> [("no currencies", build [])]
    unhex s = BS.pack (go s)
      where
        go (a : b : r) = fromIntegral (read ['0', 'x', a, b] :: Int) : go r
        go _ = []
