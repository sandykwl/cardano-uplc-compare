{-# LANGUAGE GADTs #-}

{- | cardano-uplc's CEK machine against plutus-core's, on generated terms.

Both machines evaluate the same term. They must agree on the result term, or
fail the same way, with the same offending value where one is reported. The
terms use only what cardano-uplc's machine runs: variables, lambdas,
application, delay, force, simple constants and error. A few hand-built terms
return closures with constr and case in their bodies, never run, so discharge
of those is compared too. Untyped terms can loop
forever and cardano-uplc's machine has no budget, so plutus-core runs first
with one, and a term it does not finish within that budget is skipped.
-}
module Eval (evalReport) where

import Cardano.UPLC.Constant (Constant (..))
import Cardano.UPLC.Machine qualified as U
import Cardano.UPLC.Name qualified as U
import Cardano.UPLC.Term qualified as U
import Control.Exception (evaluate)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Vector qualified as Vector
import Data.Text qualified as T
import Data.Word (Word64)
import PlutusCore.Default (DefaultFun, DefaultUni (..))
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.Evaluation.Machine.Exception (MachineError (..))
import System.Timeout (timeout)
import Test.QuickCheck (Gen, choose, elements, frequency, generate, oneof, resize, sized, vectorOf)
import Universe (Esc, Some (..), ValueOf (..))
import UntypedPlutusCore qualified as P
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as Cek

type NTerm = P.Term P.NamedDeBruijn DefaultUni DefaultFun ()

-- Generated terms -----------------------------------------------------------

-- `depth` lambdas enclose the term. Variables mostly point at one of them;
-- now and then at index 0 or one past them, to reach the free-variable error.
genTerm :: Word64 -> Gen (U.Term U.DeBruijn ())
genTerm depth = sized $ \n ->
  if n <= 0
    then leaf
    else frequency [(2, leaf), (5, branch)]
  where
    leaf =
      frequency
        [ (6, if depth == 0 then constant else U.Var () . U.DeBruijn <$> choose (1, depth))
        , (3, constant)
        , (1, U.Var () . U.DeBruijn <$> elements [0, depth + 1])
        , (1, pure (U.Error ()))
        ]
    branch =
      oneof
        [ U.LamAbs () (U.DeBruijn 0) <$> half (genTerm (depth + 1))
        , -- A lambda applied to an argument, so bodies run with something bound.
          U.Apply () . U.LamAbs () (U.DeBruijn 0) <$> half (genTerm (depth + 1)) <*> half (genTerm depth)
        , U.Apply () <$> half (genTerm depth) <*> half (genTerm depth)
        , U.Delay () <$> half (genTerm depth)
        , U.Force () <$> half (genTerm depth)
        ]
    half g = sized (\n -> resize (n `div` 2) g)
    constant =
      U.Constant ()
        <$> oneof
          [ CInteger <$> choose (-3, 3)
          , CBool <$> elements [False, True]
          , pure CUnit
          , CByteString . BS.pack <$> vectorOf 2 (choose (0, 255))
          ]

-- plutus-core's side ---------------------------------------------------------

toPlutus :: U.Term U.DeBruijn () -> NTerm
toPlutus = \case
  U.Var _ (U.DeBruijn i) -> P.Var () (name i)
  U.LamAbs _ _ body -> P.LamAbs () (name 0) (toPlutus body)
  U.Apply _ f x -> P.Apply () (toPlutus f) (toPlutus x)
  U.Delay _ body -> P.Delay () (toPlutus body)
  U.Force _ body -> P.Force () (toPlutus body)
  U.Error _ -> P.Error ()
  U.Constant _ c -> P.Constant () (constantToPlutus c)
  U.Constr _ i fields -> P.Constr () i (map toPlutus fields)
  U.Case _ s branches -> P.Case () (toPlutus s) (fmap toPlutus branches)
  t -> error ("not generated: " <> show t)
  where
    name i = P.NamedDeBruijn (T.pack "i") (P.Index i)

constantToPlutus :: Constant -> Some (ValueOf DefaultUni)
constantToPlutus = \case
  CInteger n -> Some (ValueOf DefaultUniInteger n)
  CBool b -> Some (ValueOf DefaultUniBool b)
  CUnit -> Some (ValueOf DefaultUniUnit ())
  CByteString b -> Some (ValueOf DefaultUniByteString b)
  c -> error ("not generated: " <> show c)

fromPlutus :: NTerm -> Maybe (U.Term U.DeBruijn ())
fromPlutus = \case
  P.Var _ (P.NamedDeBruijn _ (P.Index i)) -> Just (U.Var () (U.DeBruijn i))
  P.LamAbs _ _ body -> U.LamAbs () (U.DeBruijn 0) <$> fromPlutus body
  P.Apply _ f x -> U.Apply () <$> fromPlutus f <*> fromPlutus x
  P.Delay _ body -> U.Delay () <$> fromPlutus body
  P.Force _ body -> U.Force () <$> fromPlutus body
  P.Error _ -> Just (U.Error ())
  P.Constant _ (Some (ValueOf uni x)) -> U.Constant () <$> constantFromPlutus uni x
  P.Constr _ i fields -> U.Constr () i <$> traverse fromPlutus fields
  P.Case _ s branches -> U.Case () <$> fromPlutus s <*> traverse fromPlutus branches
  _ -> Nothing

constantFromPlutus :: DefaultUni (Esc a) -> a -> Maybe Constant
constantFromPlutus uni x = case uni of
  DefaultUniInteger -> Just (CInteger x)
  DefaultUniBool -> Just (CBool x)
  DefaultUniUnit -> Just CUnit
  DefaultUniByteString -> Just (CByteString x)
  _ -> Nothing

-- What plutus-core's machine said, in cardano-uplc's terms. Nothing when it
-- ran out of budget or failed in a way this machine has no name for.
data Theirs = Finished (U.Term U.DeBruijn ()) | Failed (Either U.EvalError String) | OutOfBudget

theirs :: U.Term U.DeBruijn () -> Theirs
theirs t =
  case Cek._cekReportResult (Cek.runCekDeBruijn defaultCekParametersForTesting Cek.restrictingLarge Cek.noEmitter (toPlutus t)) of
    Cek.CekSuccessConstant (Some (ValueOf uni x)) -> maybe (Failed (Right "an unexpected constant")) (Finished . U.Constant ()) (constantFromPlutus uni x)
    Cek.CekSuccessNonConstant r -> maybe (Failed (Right "an unexpected term")) Finished (fromPlutus r)
    Cek.CekFailure (Cek.ErrorWithCause err cause) -> case err of
      Cek.OperationalError (Cek.CekOutOfExError _) -> OutOfBudget
      Cek.OperationalError Cek.CekEvaluationFailure -> Failed (Left U.ErrorTerm)
      Cek.StructuralError OpenTermEvaluatedMachineError -> case cause of
        Just (P.Var _ (P.NamedDeBruijn _ (P.Index i))) -> Failed (Left (U.FreeVariable i))
        _ -> Failed (Right "a free variable with no variable as its cause")
      Cek.StructuralError NonFunctionalApplicationMachineError -> withCause U.NotAFunction cause
      Cek.StructuralError NonPolymorphicInstantiationMachineError -> withCause U.NotDelayed cause
      e -> Failed (Right (show e))
  where
    withCause k cause = maybe (Failed (Right "a failure with no cause")) (Failed . Left . k) (fromPlutus =<< cause)

-- The comparison ------------------------------------------------------------

data Outcome = Agree String | Skipped | Disagree String

compareMachines :: U.Term U.DeBruijn () -> IO Outcome
compareMachines t = case theirs t of
  OutOfBudget -> pure Skipped
  Failed (Right why) -> pure (Disagree ("plutus-core failed in an unexpected way: " <> why))
  expected -> do
    -- plutus-core finished, so this machine must too; the timeout only turns a
    -- hang into a report.
    ours <- timeout 5000000 (evaluate (forceResult (U.evaluate t)))
    pure $ case (ours, expected) of
      (Nothing, _) -> Disagree "cardano-uplc did not finish"
      (Just (Right r), Finished r') | r == r' -> Agree (kind r)
      (Just (Left e), Failed (Left e')) | e == e' -> Agree (head (words (show e)))
      (Just o, _) -> Disagree ("cardano-uplc gave " <> show o <> ", plutus-core " <> describe expected)
  where
    forceResult r = length (show r) `seq` r
    kind = \case
      U.Constant {} -> "a constant"
      U.LamAbs {} -> "a lambda"
      U.Delay {} -> "a delay"
      _ -> "another term"
    describe = \case
      Finished r -> "returned " <> show r
      Failed e -> "failed with " <> either show id e
      OutOfBudget -> "ran out of budget"

evalReport :: Int -> IO Bool
evalReport n = do
  generated <- generate (vectorOf n (resize 24 (genTerm 0)))
  -- One term that never finishes, so the budget path is taken at least once.
  let selfApply = U.LamAbs () (U.DeBruijn 0) (U.Apply () (U.Var () (U.DeBruijn 1)) (U.Var () (U.DeBruijn 1)))
      lam = U.LamAbs () (U.DeBruijn 0)
      var = U.Var () . U.DeBruijn
      five = U.Constant () (CInteger 5)
      -- Closures returned, never run, with constr and case in their bodies.
      unrun =
        [ U.Apply () (lam (lam (U.Constr () 0 [var 1, var 2]))) five
        , U.Apply () (lam (lam (U.Case () (var 2) (Vector.fromList [var 1, lam (var 3)])))) five
        , U.Apply () (lam (U.Delay () (U.Constr () 1 [var 1, U.Case () (var 1) mempty]))) five
        ]
      terms = U.Apply () selfApply selfApply : unrun <> generated
  outcomes <- mapM (\t -> (,) t <$> compareMachines t) terms
  let agree = length [() | (_, Agree _) <- outcomes]
      kinds = Map.toList (Map.fromListWith (+) [(k, 1 :: Int) | (_, Agree k) <- outcomes])
      skipped = length [() | (_, Skipped) <- outcomes]
      bad = [(t, w) | (t, Disagree w) <- outcomes]
  putStrLn $
    "machine, generated terms: " <> show (length terms) <> " terms, " <> show agree <> " agree, "
      <> show skipped <> " skipped for plutus-core's budget, " <> show (length bad) <> " disagreements"
  putStrLn ("  agreed on: " <> concatMap (\(k, c) -> k <> " " <> show c <> "; ") kinds)
  mapM_ (\(t, w) -> putStrLn ("  DISAGREE " <> show t <> ": " <> w)) (take 10 bad)
  -- The self-applied term must have been skipped, or the budget path is untested.
  pure (null bad && skipped >= 1)
