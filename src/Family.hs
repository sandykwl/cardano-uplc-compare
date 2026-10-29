{- | The integer, bytestring and bitwise builtins and ifThenElse, applied to
arguments at the edges of their ranges, evaluated by both machines under each
of the five semantics variants.

Every application is run five times, once per variant, and the two machines
must agree on the result or on the error and the term that caused it. Most
terms are saturated applications with the right argument types. The rest have
a wrong argument type, the wrong number of forces or arguments, or an
argument bound by a lambda. The edge values are the limits
plutus-core checks: the 64-bit range of an index, 2^8191 for expModInteger,
8192 bytes for integerToByteString, and the 2^262143 and 65536-byte bounds of
variants D and E.
-}
module Family (familyReport) where

import Cardano.UPLC.Builtin (DefaultFun (..))
import Cardano.UPLC.Constant (Constant (..))
import Cardano.UPLC.Machine (SemanticsVariant (..))
import Cardano.UPLC.Name (DeBruijn (DeBruijn))
import Cardano.UPLC.Term (Term (..))
import Cardano.UPLC.Ty (Ty (TyInteger))
import Control.Monad (foldM, forM_)
import Data.ByteString qualified as BS
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Eval (Outcome (..), compareUnder)
import Test.QuickCheck (Gen, arbitrary, choose, elements, frequency, generate, oneof, vectorOf)

type T = Term DeBruijn ()

-- What an argument position takes. The kinds name where its edge values come
-- from, since the edges of an index depend on the byte string beside it.
data Kind
  = KInt -- any integer
  | KMod -- expModInteger's modulus, where 1 and 0 are answered before the bounds
  | KByteVal -- consByteString's first argument, and replicateByte's second
  | KCount -- replicateByte's length
  | KIdx -- a position in the byte string beside it
  | KWidth -- integerToByteString's width
  | KShift -- a shift or rotation
  | KBytes
  | KBool
  | KIntList -- writeBits' positions
  | KAny -- ifThenElse's branches

-- Forces, then argument kinds. Only ifThenElse takes a force.
signature :: DefaultFun -> (Int, [Kind])
signature = \case
  AddInteger -> (0, [KInt, KInt])
  SubtractInteger -> (0, [KInt, KInt])
  MultiplyInteger -> (0, [KInt, KInt])
  DivideInteger -> (0, [KInt, KInt])
  QuotientInteger -> (0, [KInt, KInt])
  RemainderInteger -> (0, [KInt, KInt])
  ModInteger -> (0, [KInt, KInt])
  EqualsInteger -> (0, [KInt, KInt])
  LessThanInteger -> (0, [KInt, KInt])
  LessThanEqualsInteger -> (0, [KInt, KInt])
  ExpModInteger -> (0, [KInt, KInt, KMod])
  AppendByteString -> (0, [KBytes, KBytes])
  ConsByteString -> (0, [KByteVal, KBytes])
  SliceByteString -> (0, [KIdx, KIdx, KBytes])
  LengthOfByteString -> (0, [KBytes])
  IndexByteString -> (0, [KBytes, KIdx])
  EqualsByteString -> (0, [KBytes, KBytes])
  LessThanByteString -> (0, [KBytes, KBytes])
  LessThanEqualsByteString -> (0, [KBytes, KBytes])
  IntegerToByteString -> (0, [KBool, KWidth, KInt])
  ByteStringToInteger -> (0, [KBool, KBytes])
  AndByteString -> (0, [KBool, KBytes, KBytes])
  OrByteString -> (0, [KBool, KBytes, KBytes])
  XorByteString -> (0, [KBool, KBytes, KBytes])
  ComplementByteString -> (0, [KBytes])
  ReadBit -> (0, [KBytes, KIdx])
  WriteBits -> (0, [KBytes, KIntList, KBool])
  ReplicateByte -> (0, [KCount, KByteVal])
  ShiftByteString -> (0, [KBytes, KShift])
  RotateByteString -> (0, [KBytes, KShift])
  CountSetBits -> (0, [KBytes])
  FindFirstSetBit -> (0, [KBytes])
  IfThenElse -> (1, [KBool, KAny, KAny])
  f -> error ("not compared here: " <> show f)

builtins :: [DefaultFun]
builtins =
  [ AddInteger, SubtractInteger, MultiplyInteger, DivideInteger, QuotientInteger
  , RemainderInteger, ModInteger, EqualsInteger, LessThanInteger, LessThanEqualsInteger
  , ExpModInteger
  , AppendByteString, ConsByteString, SliceByteString, LengthOfByteString, IndexByteString
  , EqualsByteString, LessThanByteString, LessThanEqualsByteString
  , IntegerToByteString, ByteStringToInteger
  , AndByteString, OrByteString, XorByteString, ComplementByteString, ReadBit, WriteBits
  , ReplicateByte, ShiftByteString, RotateByteString, CountSetBits, FindFirstSetBit
  , IfThenElse
  ]

-- Values --------------------------------------------------------------------

pow :: Int -> Integer
pow = (2 ^)

int64Edges, bigEdges :: [Integer]
int64Edges = [pow 63 - 1, pow 63, negate (pow 63), negate (pow 63) - 1, pow 64 - 1, pow 64, pow 64 + 1]
-- expModInteger's limit, 2^8191, integerToByteString's input limit, 2^65536,
-- and the D and E bound on an integer, 2^262143.
bigEdges =
  [ pow 8191 - 1, pow 8191, negate (pow 8191), pow 8192
  , pow 65535, pow 65536 - 1, pow 65536
  , pow 262143 - 1, pow 262143, negate (pow 262143), negate (pow 262143) - 1, pow 262144
  ]

smallEdges :: [Integer]
smallEdges = [0, 1, -1, 2, -2, 3, 7, 8, 9, 127, 128, 255, 256, 257, -255, -256, -257, 65535, 65536]

genInteger :: Gen Integer
genInteger =
  frequency
    [ (10, elements smallEdges)
    , (4, choose (-20, 20))
    , (3, elements int64Edges)
    , (1, elements bigEdges)
    , (1, choose (negate (pow 100), pow 100))
    ]

genLength :: Gen Int
genLength =
  frequency
    [ (3, pure 0), (3, pure 1), (3, pure 2), (3, pure 64), (2, pure 4096), (2, pure 4097)
    , (1, pure 65536), (1, pure 65537), (5, choose (0, 130))
    ]

genBytes :: Int -> Gen BS.ByteString
genBytes m
  | m > 5000 = elements [BS.replicate m 0, BS.replicate m 0xff, BS.replicate m 0x55]
  | otherwise =
      oneof
        [ pure (BS.replicate m 0)
        , pure (BS.replicate m 0xff)
        , pure (BS.pack (take m (cycle [0x01, 0x80, 0x55])))
        , BS.pack <$> vectorOf m arbitrary
        ]

constant :: Constant -> T
constant = Constant ()

-- Positions around a byte string of length len, in bytes and in bits.
genIndex :: Int -> Gen Integer
genIndex len =
  frequency
    [ (8, elements [0, 1, 2, l - 1, l, l + 1, 8 * l - 1, 8 * l, 8 * l + 1, -1, -l, -8 * l])
    , (4, choose (-3, 8 * l + 3))
    , (2, elements int64Edges)
    , (1, elements [negate (pow 63), pow 63 - 1])
    ]
  where
    l = toInteger len

genArg :: Int -> Kind -> Gen T
genArg len = \case
  KInt -> constant . CInteger <$> genInteger
  KMod -> constant . CInteger <$> frequency [(2, elements [1, 0, -1, 2]), (3, genInteger)]
  KByteVal ->
    constant . CInteger
      <$> frequency
        [ (6, elements [0, 1, 127, 128, 254, 255, 256, 257, -1, -2, -255, -256, -257, pow 64 + 1])
        , (3, choose (0, 255))
        , (1, elements bigEdges)
        ]
  KCount ->
    constant . CInteger
      <$> frequency
        [ (8, elements [0, 1, 2, 64, 4096, 4097, 8192, 8193, 65536, 65537, -1])
        , (2, choose (0, 20))
        , (2, elements (pow 31 : pow 63 : int64Edges))
        ]
  KIdx -> constant . CInteger <$> genIndex len
  KWidth ->
    constant . CInteger
      <$> frequency
        [ (8, elements [0, 1, 2, 8, 64, 4096, 4097, 8191, 8192, 8193, 65536, -1, pow 29, pow 63, pow 64])
        , (3, choose (0, 20))
        ]
  KShift ->
    constant . CInteger
      <$> frequency
        [ (6, elements [0, 1, -1, 7, 8, 9, -7, -8, -9, 8 * toInteger len, negate (8 * toInteger len), 8 * toInteger len + 1])
        , (3, choose (-20, 20))
        , (3, elements int64Edges)
        , (1, elements bigEdges)
        ]
  KBytes -> do
    m <- frequency [(7, pure len), (3, genLength)]
    constant . CByteString <$> genBytes m
  KBool -> constant . CBool <$> elements [False, True]
  KIntList -> do
    n <- frequency [(2, pure 0), (6, choose (1, 4)), (1, choose (5, 60))]
    constant . CList TyInteger . map CInteger <$> vectorOf n (genIndex len)
  KAny ->
    frequency
      [ (5, constant <$> genConstantAny)
      , (2, pure (LamAbs () (DeBruijn 0) (Var () (DeBruijn 1))))
      , (1, pure (Delay () (Error ())))
      , (1, pure (Builtin () AddInteger))
      , (1, pure (Error ()))
      ]

genConstantAny :: Gen Constant
genConstantAny = oneof [CInteger <$> choose (-3, 3), CBool <$> elements [False, True], pure CUnit, CByteString <$> genBytes 2]

-- An argument of the wrong type, or no constant at all.
genJunk :: Gen T
genJunk =
  oneof
    [ constant . CInteger <$> genInteger
    , constant . CBool <$> elements [False, True]
    , pure (constant CUnit)
    , constant . CByteString <$> (genLength >>= genBytes . min 100)
    , pure (constant (CList TyInteger [CInteger 1]))
    , pure (LamAbs () (DeBruijn 0) (Var () (DeBruijn 1)))
    , pure (Delay () (constant (CInteger 1)))
    , pure (Builtin () AddInteger)
    , pure (Error ())
    ]

-- Applications ---------------------------------------------------------------

applyTo :: Int -> DefaultFun -> [T] -> T
applyTo forces f = foldl (Apply ()) (iterate (Force ()) (Builtin () f) !! forces)

genCase :: DefaultFun -> Gen T
genCase f = do
  let (k, kinds) = signature f
      n = length kinds
  len <- genLength
  args <- mapM (genArg len) kinds
  let saturated = applyTo k f args
  frequency
    [ (58, pure saturated)
    , (14, do
        i <- choose (0, n - 1)
        junk <- genJunk
        pure (applyTo k f (take i args <> [junk] <> drop (i + 1) args)))
    , (6, do
        forces <- elements ([0 .. k + 1] `without` k)
        m <- choose (0, n)
        pure (applyTo forces f (take m args)))
    , (8, do
        m <- choose (0, n - 1)
        trailing <- elements [False, True]
        let partial = applyTo k f (take m args)
        pure (if trailing then Force () partial else partial))
    , (4, pure (Apply () saturated (constant (CInteger 1))))
    , (10, do
        i <- choose (0, n - 1)
        pure (Apply () (LamAbs () (DeBruijn 0) (applyTo k f (take i args <> [Var () (DeBruijn 1)] <> drop (i + 1) args))) (args !! i)))
    ]
  where
    without xs x = filter (/= x) xs

-- The run -------------------------------------------------------------------

variants :: [SemanticsVariant]
variants = [minBound .. maxBound]

-- Agreed, skipped for plutus-core's budget, disagreed.
data Counts = Counts !Int !Int !Int

instance Semigroup Counts where
  Counts a b c <> Counts a' b' c' = Counts (a + a') (b + b') (c + c')

instance Monoid Counts where
  mempty = Counts 0 0 0

data Tally = Tally
  { perCell :: !(Map.Map (DefaultFun, SemanticsVariant) Counts)
  , perKind :: !(Map.Map (SemanticsVariant, String) Int)
  , failures :: ![(DefaultFun, SemanticsVariant, T, String)]
  }

familyReport :: Int -> IO Bool
familyReport n = do
  tally <- foldM run (Tally Map.empty Map.empty []) [(f, i) | f <- builtins, i <- [1 .. n]]
  putStrLn $
    "builtins, " <> show n <> " applications of each of " <> show (length builtins)
      <> " builtins under each of 5 variants: " <> show (length builtins * n * 5) <> " evaluations, "
      <> show (length (failures tally)) <> " disagreements"
  putStrLn "  per builtin, agree/skipped for plutus-core's budget/disagree, under A B C D E:"
  forM_ builtins $ \f ->
    putStrLn $
      "  " <> padTo 26 (show f)
        <> intercalate " | " [cell (Map.findWithDefault mempty (f, v) (perCell tally)) | v <- variants]
  putStrLn "  per variant, what both machines reached:"
  forM_ variants $ \v ->
    putStrLn $
      "  " <> show v <> ": "
        <> concat [k <> " " <> show c <> "; " | ((v', k), c) <- Map.toList (perKind tally), v' == v]
  mapM_
    (\(f, v, t, w) -> putStrLn ("  DISAGREE " <> show f <> " " <> show v <> " " <> take 700 (show t) <> ": " <> w))
    (reverse (failures tally))
  pure (null (failures tally))
  where
    cell (Counts a s b) = show a <> "/" <> show s <> "/" <> show b
    padTo k s = s <> replicate (k - length s) ' '
    run tally (f, _) = do
      t <- generate (genCase f)
      foldM (one f t) tally variants
    one f t tally v = do
      o <- compareUnder v t
      pure $ case o of
        Agree k -> tally {perCell = bump (Counts 1 0 0), perKind = Map.insertWith (+) (v, k) 1 (perKind tally)}
        Skipped -> tally {perCell = bump (Counts 0 1 0)}
        Disagree w -> tally {perCell = bump (Counts 0 0 1), failures = (f, v, t, w) : failures tally}
        Unrun w -> tally {perCell = bump (Counts 0 0 1), failures = (f, v, t, "not run by cardano-uplc: " <> w) : failures tally}
      where
        bump c = Map.insertWith (<>) (f, v) c (perCell tally)
