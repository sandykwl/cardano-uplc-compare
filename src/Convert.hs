{-# LANGUAGE GADTs #-}

{- | plutus-core's programs and data, turned into cardano-uplc's.

Comparing re-encoded bytes alone misses a mistake made the same way in both
directions, such as two builtins with swapped tags: the bytes still match.
Turning plutus-core's decoded program into cardano-uplc's types, and comparing
values, catches it. Builtins are matched by name, never by tag.
-}
module Convert (fromPlutusProgram, fromPlutusData, toPlutusData, fromPlutusValue, toPlutusValue, lacksBuiltin) where

import Cardano.UPLC.Builtin qualified as U
import Cardano.UPLC.Constant (Constant (..))
import Cardano.UPLC.Data qualified as UD
import Cardano.UPLC.Name qualified as U
import Cardano.UPLC.Term qualified as U
import Cardano.UPLC.Ty (Ty (..))
import Cardano.UPLC.Value qualified as UV
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Vector qualified as Vector
import PlutusCore.Data qualified as PD
import PlutusCore.Default (DefaultFun, DefaultUni (..))
import PlutusCore.Value qualified as PV
import PlutusCore.Version qualified as P
import Universe (Esc, Some (..), ValueOf (..))
import UntypedPlutusCore qualified as P

-- | 'Nothing' when the program holds something cardano-uplc has no type for,
-- such as a builtin it lacks.
fromPlutusProgram :: P.Program P.DeBruijn DefaultUni DefaultFun () -> Maybe (U.Program U.DeBruijn ())
fromPlutusProgram (P.Program _ (P.Version a b c) t) = U.Program () (U.Version a b c) <$> fromTerm t

fromTerm :: P.Term P.DeBruijn DefaultUni DefaultFun () -> Maybe (U.Term U.DeBruijn ())
fromTerm = \case
  P.Var _ (P.DeBruijn (P.Index i)) -> Just (U.Var () (U.DeBruijn i))
  P.LamAbs _ _ body -> U.LamAbs () (U.DeBruijn 0) <$> fromTerm body
  P.Apply _ f x -> U.Apply () <$> fromTerm f <*> fromTerm x
  P.Delay _ body -> U.Delay () <$> fromTerm body
  P.Force _ body -> U.Force () <$> fromTerm body
  P.Constant _ (Some (ValueOf uni x)) -> U.Constant () <$> fromValue uni x
  P.Builtin _ f -> U.Builtin () <$> Map.lookup (show f) builtins
  P.Error _ -> Just (U.Error ())
  P.Constr _ i fields -> U.Constr () i <$> traverse fromTerm fields
  P.Case _ s branches -> U.Case () <$> fromTerm s <*> traverse fromTerm branches

builtins :: Map.Map String U.DefaultFun
builtins = Map.fromList [(show f, f) | f <- [minBound .. maxBound]]

-- | Whether the program calls a builtin cardano-uplc does not have.
lacksBuiltin :: P.Program P.DeBruijn DefaultUni DefaultFun () -> Bool
lacksBuiltin (P.Program _ _ t) = any (\f -> Map.notMember (show f) builtins) (termBuiltins t)

termBuiltins :: P.Term P.DeBruijn DefaultUni DefaultFun () -> [DefaultFun]
termBuiltins t = [f | P.Builtin _ f <- subterms t]

subterms :: P.Term P.DeBruijn DefaultUni DefaultFun () -> [P.Term P.DeBruijn DefaultUni DefaultFun ()]
subterms t = t : case t of
  P.LamAbs _ _ body -> subterms body
  P.Apply _ f x -> subterms f <> subterms x
  P.Delay _ body -> subterms body
  P.Force _ body -> subterms body
  P.Constr _ _ fields -> concatMap subterms fields
  P.Case _ s branches -> subterms s <> concatMap subterms (Vector.toList branches)
  _ -> []

fromValue :: DefaultUni (Esc a) -> a -> Maybe Constant
fromValue uni x = case uni of
  DefaultUniInteger -> Just (CInteger x)
  DefaultUniByteString -> Just (CByteString x)
  DefaultUniString -> Just (CString x)
  DefaultUniUnit -> Just CUnit
  DefaultUniBool -> Just (CBool x)
  DefaultUniData -> Just (CData (fromPlutusData x))
  DefaultUniValue -> Just (CValue (fromPlutusValue x))
  DefaultUniApply DefaultUniProtoList a -> CList <$> fromType a <*> traverse (fromValue a) x
  DefaultUniApply DefaultUniProtoArray a -> CArray <$> fromType a <*> traverse (fromValue a) x
  DefaultUniApply (DefaultUniApply DefaultUniProtoPair a) b ->
    CPair <$> fromType a <*> fromType b <*> fromValue a (fst x) <*> fromValue b (snd x)
  _ -> Nothing

fromType :: DefaultUni (Esc a) -> Maybe Ty
fromType = \case
  DefaultUniInteger -> Just TyInteger
  DefaultUniByteString -> Just TyByteString
  DefaultUniString -> Just TyString
  DefaultUniUnit -> Just TyUnit
  DefaultUniBool -> Just TyBool
  DefaultUniData -> Just TyData
  DefaultUniBLS12_381_G1_Element -> Just TyBLS12_381_G1_Element
  DefaultUniBLS12_381_G2_Element -> Just TyBLS12_381_G2_Element
  DefaultUniBLS12_381_MlResult -> Just TyBLS12_381_MlResult
  DefaultUniValue -> Just TyValue
  DefaultUniApply DefaultUniProtoList a -> TyList <$> fromType a
  DefaultUniApply DefaultUniProtoArray a -> TyArray <$> fromType a
  DefaultUniApply (DefaultUniApply DefaultUniProtoPair a) b -> TyPair <$> fromType a <*> fromType b
  _ -> Nothing

fromPlutusData :: PD.Data -> UD.Data
fromPlutusData = \case
  PD.Constr i fs -> UD.Constr i (map fromPlutusData fs)
  PD.Map ps -> UD.Map [(fromPlutusData k, fromPlutusData v) | (k, v) <- ps]
  PD.List xs -> UD.List (map fromPlutusData xs)
  PD.I n -> UD.I n
  PD.B b -> UD.B b

toPlutusData :: UD.Data -> PD.Data
toPlutusData = \case
  UD.Constr i fs -> PD.Constr i (map toPlutusData fs)
  UD.Map ps -> PD.Map [(toPlutusData k, toPlutusData v) | (k, v) <- ps]
  UD.List xs -> PD.List (map toPlutusData xs)
  UD.I n -> PD.I n
  UD.B b -> PD.B b

-- Both sides check keys and quantities on the way in, so a value one side
-- holds always fits the other's.
fromPlutusValue :: PV.Value -> UV.Value
fromPlutusValue v = UV.pack (Map.fromList [(key c, Map.fromList [(key t, qty q) | (t, q) <- Map.toList ts]) | (c, ts) <- Map.toList (PV.unpack v)])
  where
    key = fromJust . UV.k . PV.unK
    qty = fromJust . UV.quantity . PV.unQuantity

toPlutusValue :: UV.Value -> PV.Value
toPlutusValue v = PV.pack (Map.fromList [(key c, Map.fromList [(key t, qty q) | (t, q) <- Map.toList ts]) | (c, ts) <- Map.toList (UV.unpack v)])
  where
    key = fromJust . PV.k . UV.unK
    qty = fromJust . PV.quantity . UV.unQuantity
