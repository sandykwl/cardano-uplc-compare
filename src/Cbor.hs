{- | Data as CBOR: cardano-uplc against plutus-core.

Both sides read a byte string as one whole value: cardano-uplc's decodeData,
and plutus-core's own decoder with the rest required to be empty. Reading a
value with bytes after it, as plutus-core does for a data constant, is
compared through flat programs instead.
-}
module Cbor (cborReport) where

import Cardano.UPLC.Data qualified as U
import Cardano.UPLC.Data.Cbor (decodeData, encodeData)
import Convert (toPlutusData)
import Gen (genData)
import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.Serialise (decode, serialise)
import Control.Monad (forM)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Numeric (readHex)
import PlutusCore.Data qualified as P
import Test.QuickCheck (Gen, generate, resize, vectorOf)

theirEncode :: P.Data -> ByteString
theirEncode = BSL.toStrict . serialise

theirDecode :: ByteString -> Either String P.Data
theirDecode bs = case deserialiseFromBytes decode (BSL.fromStrict bs) of
  Left e -> Left (show e)
  Right (rest, d)
    | BSL.null rest -> Right d
    | otherwise -> Left ("bytes after the value: " <> show (BSL.length rest))

data Outcome = Agree | Disagree String

-- Encoding: both sides write the value; the bytes must be equal.
compareEncode :: U.Data -> Outcome
compareEncode d
  | encodeData d == theirEncode (toPlutusData d) = Agree
  | otherwise = Disagree "the two encoders wrote different bytes"

-- Decoding: both sides read the bytes. They must agree on accepting, and
-- when both accept, on the value.
compareDecode :: ByteString -> Outcome
compareDecode bs = case (decodeData bs, theirDecode bs) of
  (Left _, Left _) -> Agree
  (Right v, Right p)
    | toPlutusData v == p -> Agree
    | otherwise -> Disagree "both accept, with different values"
  (Right _, Left e) -> Disagree ("cardano-uplc accepts, plutus-core refuses: " <> take 120 e)
  (Left e, Right _) -> Disagree ("cardano-uplc refuses (" <> show e <> "), plutus-core accepts")

-- The middle count is either what plutus-core accepts or, for the writers,
-- how many of its own encodings it reads back.
report :: String -> String -> [(String, Outcome)] -> [Bool] -> IO Bool
report name counted outcomes theirs = do
  let bad = [(l, w) | (l, Disagree w) <- outcomes]
  putStrLn $
    name <> ": " <> show (length outcomes) <> " inputs; " <> counted <> " "
      <> show (length (filter id theirs)) <> "; " <> show (length bad) <> " disagreements"
  mapM_ (\(l, w) -> putStrLn ("  DISAGREE " <> l <> ": " <> w)) (take 10 bad)
  pure (null bad)

unhex :: String -> ByteString
unhex = BS.pack . go . filter (/= ' ')
  where
    go (a : b : rest) = fst (head (readHex [a, b])) : go rest
    go _ = []

-- Each form of the writer, at both sides of its boundary.
writingRules :: [(String, U.Data)]
writingRules =
  [("Constr " <> show i, U.Constr i []) | i <- [0, 6, 7, 127, 128, 2 ^ (64 :: Int) - 1, 2 ^ (64 :: Int), -1]]
    <> [ ("Constr 0 with a field", U.Constr 0 [U.I 1])
       , ("empty list", U.List [])
       , ("one-item list", U.List [U.I 1])
       , ("empty map", U.Map [])
       , ("map with a duplicate key", U.Map [(U.I 1, U.I 2), (U.I 1, U.I 3)])
       ]
    <> [("I " <> show n, U.I n) | n <- [0, 23, 24, 255, 256, 65535, 65536, 2 ^ (64 :: Int) - 1, 2 ^ (64 :: Int), -1, -24, -25, -(2 ^ (64 :: Int)), -(2 ^ (64 :: Int)) - 1, 2 ^ (512 :: Int) - 1, 2 ^ (512 :: Int), -(2 ^ (512 :: Int)) - 1]]
    <> [("B of " <> show n <> " bytes", U.B (BS.replicate n 0xab)) | n <- [0, 1, 23, 24, 64, 65, 128, 129]]

-- Inputs the reader must accept or refuse as plutus-core does, including
-- forms plutus-core never writes: long heads, definite lists, indefinite
-- maps, small indices under tag 102.
readingRules :: [(String, ByteString)]
readingRules =
  map (fmap unhex) $
    [ ("I 1, minimal", "01")
    , ("I 1, head padded to 1 byte", "1801")
    , ("I 1, head padded to 8 bytes", "1b0000000000000001")
    , ("I -1, head padded", "3800")
    , ("I 2^64 as a big integer", "c249010000000000000000")
    , ("I 1 as a big integer", "c24101")
    , ("I 1 as a big integer, leading zero", "c2420001")
    , ("big-integer tag written long", "d8024101")
    , ("big integer, indefinite payload", "c25f4101ff")
    , ("big integer, 65-byte payload", "c25841" <> concat (replicate 65 "01"))
    , ("B of 65 bytes, definite", "5841" <> concat (replicate 65 "ab"))
    , ("B of 64 bytes, definite", "5840" <> concat (replicate 64 "ab"))
    , ("B in chunks 1 and 2", "5f41ab42abcdff")
    , ("B, indefinite with an empty chunk", "5f40ff")
    , ("B, indefinite with a 65-byte chunk", "5f5841" <> concat (replicate 65 "ab") <> "ff")
    , ("text string", "6161")
    , ("empty list, definite", "80")
    , ("empty list, indefinite", "9fff")
    , ("one-item list, definite", "8101")
    , ("one-item list, indefinite", "9f01ff")
    , ("list length head padded", "980101")
    , ("empty map, definite", "a0")
    , ("empty map, indefinite", "bfff")
    , ("one-pair map, indefinite", "bf0102ff")
    , ("map with a duplicate key", "a201020103")
    , ("Constr 0 []", "d87980")
    , ("Constr 0 [], indefinite fields", "d8799fff")
    , ("Constr 0 [I 1], definite fields", "d8798101")
    , ("Constr 0 [], tag written long", "d9007980")
    , ("Constr 7 [] (tag 1280)", "d9050080")
    , ("Constr 127 [] (tag 1400)", "d9057880")
    , ("tag 1401", "d9057980")
    , ("tag 120", "d87880")
    , ("tag 128", "d88080")
    , ("Constr 0 under tag 102", "d866820080")
    , ("Constr 128 under tag 102", "d86682188080")
    , ("tag 102, indefinite pair", "d8669f188080ff")
    , ("tag 102, three items", "d8668318808000")
    , ("tag 102, negative index", "d866822080")
    , ("tag 102, index 2^64", "d86682c24901000000000000000080")
    , ("bytes after a complete value", "0000")
    , ("true", "f5")
    , ("a half-precision float", "f93c00")
    , ("undefined", "f7")
    , ("nothing at all", "")
    ]

-- | Run every CBOR family. Mutation is passed in so the flat families and
-- these share one definition of it.
cborReport :: Int -> (ByteString -> Gen (String, ByteString)) -> IO Bool
cborReport n mutate = do
  values <- generate (vectorOf n (resize 20 genData))
  -- The generator must stay inside what plutus-core reads back, or the
  -- comparisons below would be measuring the generator.
  let unreadable = [d | d <- values, theirDecode (theirEncode (toPlutusData d)) /= Right (toPlutusData d)]
  putStrLn $ "Data, generated values that plutus-core cannot read back: " <> show (length unreadable)
  ok1 <- report "Data, encoding generated values" "plutus-core reads back its own encoding of" [("generated", compareEncode d) | d <- values]
           [either (const False) (const True) (theirDecode (theirEncode (toPlutusData d))) | d <- values]
  ok2 <- report "Data, each form of the writer" "plutus-core reads back its own encoding of" [(l, compareEncode d) | (l, d) <- writingRules]
           [either (const False) (const True) (theirDecode (theirEncode (toPlutusData d))) | (_, d) <- writingRules]
  ok3 <- report "Data, what the reader accepts and refuses" "plutus-core accepts" [(l, compareDecode b) | (l, b) <- readingRules]
           [either (const False) (const True) (theirDecode b) | (_, b) <- readingRules]
  muts <- generate (forM (map (theirEncode . toPlutusData) values) mutate)
  ok4 <- report "Data, mutated encodings" "plutus-core accepts" [(l, compareDecode b) | (l, b) <- muts]
           [either (const False) (const True) (theirDecode b) | (_, b) <- muts]
  pure (null unreadable && and [ok1, ok2, ok3, ok4])
