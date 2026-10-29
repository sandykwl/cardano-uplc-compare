{- | cardano-uplc's codecs and machine against plutus-core's, on the same inputs.

Both decoders read the same bytes and must agree on whether to accept them.
When both accept, they must have read the same program, and re-encode it to
the same bytes. When only plutus-core accepts, the refusal must be a known gap,
something cardano-uplc does not handle yet; anything else is a failure.
The machines are compared in "Eval", on terms rather than bytes, and the
builtins in "Family" and "Shape".

Usage:
  cardano-uplc-compare [CASES]          everything, CASES per random family
                                        (default 10000)
  cardano-uplc-compare corpus DIR       every .flat file under DIR
  cardano-uplc-compare builtins CASES   the builtins alone, CASES applications
                                        of each
  cardano-uplc-compare shapes           the builtins' forces and arities alone
-}
module Main (main) where

import Cardano.UPLC.Constant (Constant (CInteger, CValue))
import Cardano.UPLC.Flat qualified as U
import Cardano.UPLC.Name qualified as U
import Cardano.UPLC.Term qualified as U
import Control.Monad (filterM, forM, replicateM, unless)
import Data.Bits (xor, shiftL)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BC
import Data.Char (digitToInt, isDigit, isHexDigit, isSpace)
import Data.List (foldl', sortOn)
import Data.Map.Strict qualified as Map
import Data.Word (Word64, Word8)
import Numeric (showHex)
import Numeric.Natural (Natural)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Flat (flat, unflat)
import System.Directory (doesDirectoryExist, listDirectory, pathIsSymbolicLink)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Read (readMaybe)
import System.FilePath (takeExtension, (</>))
import Test.QuickCheck (Gen, arbitrary, choose, elements, generate, resize, vectorOf)
import UntypedPlutusCore qualified as P

import Bits
import Cbor (cborReport)
import Convert (fromPlutusProgram, lacksBuiltin)
import Eval (evalReport)
import Family (familyReport)
import Gen (Encodable (Encodable), Nested (Nested), genValue)
import Shape (shapeReport)
import Value (valueCases, valueReport)

type Ref = P.UnrestrictedProgram P.DeBruijn DefaultUni DefaultFun ()

refDecode :: ByteString -> Either String Ref
refDecode = either (Left . show) Right . unflat

refEncode :: Ref -> ByteString
refEncode = flat

data Outcome = BothAccept | BothRefuse | Gap String | Disagree String
  deriving stock (Show)

compareDecoders :: ByteString -> Outcome
compareDecoders bs = case (U.decodeProgram bs, refDecode bs) of
  (Left _, Left _) -> BothRefuse
  (Right p, Right q)
    | fromPlutusProgram (P.unUnrestrictedProgram q) /= Just p -> Disagree "both accept, with different programs"
    | b /= refEncode q -> Disagree ("both accept; re-encoded as " <> hex b <> " and " <> hex (refEncode q))
    | otherwise -> BothAccept
    where
      b = U.encodeProgram p
  (Right _, Left e) -> Disagree ("cardano-uplc accepts, plutus-core refuses: " <> take 200 e)
  (Left e, Right q) -> maybe (Disagree ("cardano-uplc refuses with " <> show e <> ", plutus-core accepts")) Gap (knownGap e q)

-- What cardano-uplc does not handle yet: builtins after tag 93. A refusal is
-- counted as a gap only when plutus-core's program really calls one, so a
-- misread that happens to land on that error is still a disagreement.
knownGap :: U.DecodeError -> Ref -> Maybe String
knownGap e (P.UnrestrictedProgram p) = case e of
  U.BadBuiltinTag t _ | t >= 94 && t <= 105, lacksBuiltin p -> Just ("builtin tag " <> show t)
  _ -> Nothing

hex :: ByteString -> String
hex = concatMap (\w -> let s = showHex w "" in if length s == 1 then '0' : s else s) . BS.unpack

-- Results per family --------------------------------------------------------

data Tally = Tally {tAccept :: !Int, tRefuse :: !Int, tGaps :: !(Map.Map String Int), tBad :: ![(String, ByteString, String)]}

emptyTally :: Tally
emptyTally = Tally 0 0 Map.empty []

record :: Tally -> (String, ByteString) -> Tally
record t (label, bs) = case compareDecoders bs of
  BothAccept -> t {tAccept = tAccept t + 1}
  BothRefuse -> t {tRefuse = tRefuse t + 1}
  Gap why -> t {tGaps = Map.insertWith (+) why 1 (tGaps t)}
  Disagree why -> t {tBad = (label, bs, why) : tBad t}

report :: String -> [(String, ByteString)] -> IO Bool
report name cases = do
  let t = foldl' record emptyTally cases
      total = length cases
  putStrLn $ name <> ": " <> show total <> " inputs: both accept " <> show (tAccept t) <> ", both refuse " <> show (tRefuse t) <> ", "
    <> show (sum (tGaps t)) <> " known gaps, " <> show (length (tBad t)) <> " disagreements"
  unless (Map.null (tGaps t)) $
    putStrLn $ "  gaps: " <> concatMap (\(k, v) -> k <> " " <> show v <> "; ") (sortOn byNumber (Map.toList (tGaps t)))
  mapM_ (\(l, b, w) -> putStrLn ("  DISAGREE " <> l <> " " <> hex b <> ": " <> w)) (take 10 (reverse (tBad t)))
  pure (null (tBad t))

-- Sort "builtin tag 94" before "builtin tag 100".
byNumber :: (String, Int) -> (String, Maybe Int)
byNumber (k, _) = (filter (not . isDigit) k, readMaybe (filter isDigit k))

-- Encoder agreement ---------------------------------------------------------

-- plutus-core reads the bytes cardano-uplc writes, and writes the same bytes back.
encoderAgreement :: String -> [U.Program U.DeBruijn ()] -> IO Bool
encoderAgreement name progs = do
  let check p =
        let b = U.encodeProgram p
         in case refDecode b of
              Left e -> Just ("plutus-core refuses cardano-uplc's bytes " <> hex b <> ": " <> take 200 e)
              Right q
                | fromPlutusProgram (P.unUnrestrictedProgram q) /= Just p -> Just ("plutus-core reads " <> hex b <> " as a different program")
                | refEncode q /= b -> Just ("plutus-core re-encodes " <> hex b <> " as " <> hex (refEncode q))
                | otherwise -> Nothing
      bad = [m | Just m <- map check progs]
  putStrLn $ name <> ": " <> show (length progs) <> " programs, " <> show (length bad) <> " disagreements"
  mapM_ (putStrLn . ("  DISAGREE " <>)) (take 10 bad)
  pure (null bad)

-- Mutations of valid encodings ----------------------------------------------

mutate :: ByteString -> Gen (String, ByteString)
mutate bs = do
  let n = BS.length bs
  i <- choose (0, max 0 (n - 1))
  w <- arbitrary :: Gen Word8
  k <- choose (0, 7 :: Int)
  elements
    [ ("flip bit", BS.take i bs <> BS.singleton (BS.index bs i `xor` (1 `shiftL` k)) <> BS.drop (i + 1) bs)
    , ("replace byte", BS.take i bs <> BS.singleton w <> BS.drop (i + 1) bs)
    , ("delete byte", BS.take i bs <> BS.drop (i + 1) bs)
    , ("insert byte", BS.take i bs <> BS.singleton w <> BS.drop i bs)
    , ("truncate", BS.take i bs)
    , ("append byte", bs <> BS.singleton w)
    ]

-- Hand-built edge cases, one family per reading rule -------------------------

v110, v100 :: Bits
v110 = natPadded 0 1 ++ natPadded 0 1 ++ natPadded 0 0
v100 = natPadded 0 1 ++ natPadded 0 0 ++ natPadded 0 0

prog :: Bits -> ByteString
prog = toBytes . filler 0

termTag :: Integer -> Bits
termTag = bits 4

constantOf :: [Integer] -> Bits
constantOf tags = termTag 4 ++ concatMap (\t -> True : bits 4 t) tags ++ [False]

zigzag :: Integer -> Natural
zigzag n = fromInteger (if n >= 0 then 2 * n else -2 * n - 1)

bigValues :: [Natural]
bigValues = [0, 1, 127, 128, 300, 2 ^ (63 :: Int), fromIntegral (maxBound :: Word64), 2 ^ (64 :: Int), 2 ^ (70 :: Int)]

edgeCases :: [(String, [(String, ByteString)])]
edgeCases =
  [ ( "padded naturals"
    , [ ("index " <> show n <> " +" <> show k, prog (v110 ++ termTag 0 ++ natPadded k n)) | n <- bigValues, k <- [0 .. 12] ]
        ++ [ ("constr " <> show n <> " +" <> show k, prog (v110 ++ termTag 8 ++ natPadded k n ++ [False])) | n <- bigValues, k <- [0 .. 12] ]
        ++ [ ("version part " <> show i <> " = " <> show n <> " +" <> show k, prog (version i n k ++ termTag 6))
           | i <- [0 .. 2 :: Int], n <- [0, 1, 2 ^ (64 :: Int)], k <- [0 .. 12] ]
        ++ [ ("integer " <> show v <> " +" <> show k, prog (v110 ++ constantOf [0] ++ natPadded k (zigzag v)))
           | v <- [0, 5, -5, 2 ^ (70 :: Int), -(2 ^ (70 :: Int))], k <- [0 .. 6] ]
    )
  , ( "padding and the end of input"
    , [ ("error, padding +" <> show k, toBytes (filler k (v110 ++ termTag 6))) | k <- [0 .. 3] ]
        ++ [ ("error, then " <> show pre <> " then 1 then pad", toBytes (v110 ++ termTag 6 ++ pre ++ [True])) | pre <- map (`replicate` False) [0 .. 12] ]
        ++ [ ("error, padding, " <> show n <> " trailing bytes", toBytes (filler 0 (v110 ++ termTag 6)) <> BS.replicate n t)
           | n <- [1, 2], t <- [0x00, 0x01, 0x80] ]
    )
  , ( "byte strings"
    , [ (label, toBytes (filler 0 (filler pad (v110 ++ constantOf [1]) ++ chunks cs)))
      | (label, cs) <- chunkings, pad <- [0, 1] ]
        ++ [ ("chunk runs past the end", toBytes (filler 0 (v110 ++ constantOf [1])) <> BS.pack [5, 0x61, 0x62]) ]
    )
  , ( "strings"
    , [ ("string " <> hex s, toBytes (filler 0 (filler 0 (v110 ++ constantOf [2]) ++ chunks (filter (not . BS.null) [s])))) | s <- utf8Cases ]
    )
  , ( "term tags"
    , [ ("v" <> show vi <> " tag " <> show t <> " tail " <> show ti, prog (v ++ termTag t ++ tl))
      | (vi, v) <- [(100 :: Int, v100), (110, v110)], t <- [0 .. 15], (ti, tl) <- zip [0 :: Int ..] termTails ]
    )
  , ( "data constants, including bytes after the value"
    , [ ("data payload " <> hex d, toBytes (filler 0 (filler 0 (v110 ++ constantOf [8]) ++ chunks (filter (not . BS.null) [d])))) | d <- dataPayloads ]
    )
  , ( "every type-tag list up to four tags"
    , [ (show tags <> " tail " <> show ti, tailed (v110 ++ constantOf tags) tl)
      | n <- [0 .. 4], tags <- replicateM n [0 .. 15], (ti, tl) <- zip [0 :: Int ..] valueTails ]
    )
  , ( "builtin tags"
    , [ ("builtin " <> show t, prog (v110 ++ termTag 7 ++ bits 7 t)) | t <- [0 .. 127] ]
    )
  , ("value constants, hand-built", valueCases)
  ]
  where
    version i n k = concat [natPadded (if j == i then k else 0) (if j == i then n else [1, 1, 0] !! j) | j <- [0 .. 2]]
    chunkings =
      [ ("empty", [])
      , ("abcdef whole", [BC.pack "abcdef"])
      , ("abcdef 1+5", [BC.pack "a", BC.pack "bcdef"])
      , ("abcdef 2+2+2", map BC.pack ["ab", "cd", "ef"])
      , ("abcdef by byte", map BC.singleton "abcdef")
      , ("300 as 255+45", [BS.replicate 255 7, BS.replicate 45 7])
      , ("300 as 100+200", [BS.replicate 100 7, BS.replicate 200 7])
      ]
    -- plutus-core reads one CBOR value and ignores what follows it.
    dataPayloads =
      map BS.pack [[], [0x00], [0x00, 0x00], [0x00, 0xff], [0xd8, 0x79, 0x80], [0x9f, 0x01, 0xff], [0x61, 0x61], [0x58, 0x41]]
        <> [BS.pack [0x58, 0x41] <> BS.replicate 65 0xab, BS.pack [0x58, 0x40] <> BS.replicate 64 0xab]
    utf8Cases = map BS.pack [[], [0x61], [0xc3, 0xa9], [0xff], [0xc0, 0x80], [0xed, 0xa0, 0x80], [0xf4, 0x90, 0x80, 0x80], [0xe2, 0x82]]
    termTails = [[], [False], bits 8 1, bits 8 1 ++ [False], bits 8 0x81 ++ bits 8 0 ++ [False]]
    -- Enough value shapes to let every accepted type decode: nothing (unit),
    -- one 0 bit (bool, empty list), one 1 bit (bool), a natural (integer),
    -- and an empty byte string (bytestring, string).
    valueTails = [Left [], Left [False], Left [True], Left (bits 8 4), Right ()]
    tailed acc (Left tl) = toBytes (filler 0 (acc ++ tl))
    tailed acc (Right ()) = toBytes (filler 0 (filler 0 acc ++ chunks []))

-- A corpus of real programs ---------------------------------------------------

-- Every .flat file under a directory, such as the conformance tests in the
-- plutus repository. A file may hold the bytes themselves or, as amaru's
-- tests do, the bytes written out in hex.
corpus :: FilePath -> IO ()
corpus dir = do
  files <- flatFiles dir
  contents <- mapM BS.readFile files
  let hexFiles = length (filter isHexText contents)
  putStrLn (show (length files) <> " .flat files, " <> show hexFiles <> " of them hex text")
  if null files
    then putStrLn "no .flat files found" >> exitFailure
    else report ("corpus " <> dir) (zip files (map fromHexText contents)) >>= finish

flatFiles :: FilePath -> IO [FilePath]
flatFiles dir = do
  entries <- map (dir </>) <$> listDirectory dir
  dirs <- filterM (\e -> (&&) <$> doesDirectoryExist e <*> (not <$> pathIsSymbolicLink e)) entries
  nested <- concat <$> mapM flatFiles dirs
  pure ([f | f <- entries, takeExtension f == ".flat", f `notElem` dirs] <> nested)

-- A program's first byte is its major version, 1, which is neither a hex digit
-- nor a space, so raw bytes are never mistaken for hex.
isHexText :: ByteString -> Bool
isHexText bs = not (BS.null digits) && BC.all isHexDigit digits && even (BS.length digits)
  where
    digits = BC.filter (not . isSpace) bs

fromHexText :: ByteString -> ByteString
fromHexText bs
  | isHexText bs = BS.pack (pairs (BC.unpack (BC.filter (not . isSpace) bs)))
  | otherwise = bs
  where
    pairs (a : b : rest) = fromIntegral (digitToInt a * 16 + digitToInt b) : pairs rest
    pairs _ = []

-- Main ----------------------------------------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["corpus", dir] -> corpus dir
    ["builtins", s] | Just n <- readMaybe s, n > 0 -> familyReport n >>= finish
    ["shapes"] -> shapeReport >>= finish
    [s] | Just n <- readMaybe s, n > 0 -> generated n
    [] -> generated 10000
    _ -> putStrLn "usage: cardano-uplc-compare [CASES] | corpus DIR | builtins CASES | shapes" >> exitFailure

finish :: Bool -> IO ()
finish ok = do
  putStrLn (if ok then "RESULT: no disagreements" else "RESULT: disagreements found")
  unless ok exitFailure

generated :: Int -> IO ()
generated n = do
  putStrLn ("cardano-uplc against plutus-core, " <> show n <> " cases per random family")
  progs <- generate (vectorOf n (resize 30 arbitrary))
  nested <- generate (vectorOf n arbitrary)
  let programs = [p | Encodable p <- progs]
      constants = [U.Program () (U.Version 1 1 0) (U.Constant () c) | Nested c <- nested]
  ok1 <- encoderAgreement "encoder, generated programs" programs
  ok2 <- encoderAgreement "encoder, constants at nested types" (constants ++ [U.Program () (U.Version 1 1 0) (U.Constant () (CInteger (2 ^ (700 :: Int))))])
  let encoded = map U.encodeProgram programs
  muts <- generate (forM encoded mutate)
  ok3 <- report "decoder, mutated encodings" muts
  tails <- generate . vectorOf n $ do
    v <- elements [BS.pack [1, 1, 0], BS.pack [1, 0, 0]]
    len <- choose (1, 16)
    rest <- BS.pack <$> vectorOf len arbitrary
    pure ("random tail", v <> rest)
  ok4 <- report "decoder, random bytes after a version" tails
  values <- generate (vectorOf n genValue)
  valueMuts <- generate (forM [U.encodeProgram (U.Program () (U.Version 1 1 0) (U.Constant () (CValue v))) | v <- values] mutate)
  ok5 <- report "decoder, mutated value constants" valueMuts
  okV <- valueReport n
  oks <- mapM (uncurry report) edgeCases
  okC <- cborReport n mutate
  okE <- evalReport n
  okS <- shapeReport
  okF <- familyReport n
  finish (and (ok1 : ok2 : ok3 : ok4 : ok5 : okV : okC : okE : okS : okF : oks))
