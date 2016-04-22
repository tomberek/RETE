{-# LANGUAGE TemplateHaskell #-}

module Derive (smartRep
    ) where
    
import Language.Haskell.TH hiding (Cxt)
import Control.Monad
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Term
import Data.Rewriting.Rules

smartRep fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname (name, args) = do
                let bname = nameBase name
                genSmartConstr' targs tname (mkName $ 'r' : bname) name args
              genSmartConstr' targs tname sname name args = do
                varNs <- newNames args "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    val = foldl appE (conE name) vars
                    sig = genSig targs tname sname args
                    function = [funD sname [clause pats (normalB [|toRep $ inject $val|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname 0 = (:[]) $ do
                let fvar = mkName "f"
                    hvar = mkName "h"
                    avar = mkName "a"
                    targs' = init targs
                    vars = fvar:hvar:avar:targs'
                    f = varT fvar
                    h = varT hvar
                    a = varT avar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = foldl appT (conT ''(:<:)) [ftype, f]
                    typ = foldl appT (conT ''Cxt) [h, f, a]
                    typeSig = forallT (map PlainTV vars) (sequence [constr]) typ
                sigD sname typeSig
              genSig _ _ _ _ = []
              
              
                 {-
instance (Rep f, MAJOR :<: PF f) => Major f where
    english = toRep iEnglish
    math = toRep iMath
    physics = toRep iPhysics
    -} 