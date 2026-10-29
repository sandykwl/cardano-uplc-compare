{- | The force count and arity this package uses for every builtin, checked
against plutus-core's by running both machines.

The package's table is internal, so it is read through behaviour. For each
builtin, a grid of terms: up to three forces, then up to seven unit arguments,
then optionally one more force. A wrong count anywhere changes where the
builtin turns from a value into an error, and the two machines then disagree
on a term of the grid. Wherever plutus-core returns a partial application,
cardano-uplc must return the same term. Elsewhere, a builtin cardano-uplc does
not run yet may stop with NotSupported.
-}
module Shape (shapeReport) where

import Cardano.UPLC.Builtin (DefaultFun)
import Cardano.UPLC.Constant (Constant (CUnit))
import Cardano.UPLC.Machine (SemanticsVariant (VariantE))
import Cardano.UPLC.Name (DeBruijn)
import Cardano.UPLC.Term (Term (..))
import Control.Monad (forM)
import Data.Map.Strict qualified as Map
import Eval (Outcome (..), compareUnder)

probes :: DefaultFun -> [Term DeBruijn ()]
probes f =
  [ trailing (foldl (Apply ()) (iterate (Force ()) (Builtin () f) !! k) (replicate n (Constant () CUnit)))
  | k <- [0 .. 3 :: Int]
  , n <- [0 .. 7 :: Int]
  , trailing <- [id, Force ()]
  ]

shapeReport :: IO Bool
shapeReport = do
  results <- forM [minBound .. maxBound] $ \f -> forM (probes f) $ \t -> (,) (f, t) <$> compareUnder VariantE t
  let outcomes = concat results
      agreed = Map.fromListWith (+) [(k, 1 :: Int) | (_, Agree k) <- outcomes]
      unrun = length [() | (_, Unrun _) <- outcomes]
      bad = [(f, t, w) | ((f, t), o) <- outcomes, Just w <- [why o]]
      why = \case
        Disagree w -> Just w
        Skipped -> Just "plutus-core ran out of budget"
        _ -> Nothing
  putStrLn $
    "builtin shapes: " <> show (length results) <> " builtins, " <> show (length outcomes) <> " probes, "
      <> show (sum agreed) <> " agree, " <> show unrun <> " stop at a builtin this release does not run, "
      <> show (length bad) <> " disagreements"
  putStrLn ("  agreed on: " <> concatMap (\(k, c) -> k <> " " <> show c <> "; ") (Map.toList agreed))
  mapM_ (\(f, t, w) -> putStrLn ("  DISAGREE " <> show f <> " " <> take 300 (show t) <> ": " <> w)) bad
  pure (null bad)
