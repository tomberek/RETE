{-# LANGUAGE TemplateHaskell #-}

module Derive1 (smartRep
    ) where
    
import Language.Haskell.TH hiding (Cxt)
import Control.Monad
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Term
import Data.Rewriting.Rules
import Data.Maybe

smartRep fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    cons <- mapM normalConExp constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname con = do
                let bname = nameBase $ fst con
                genSmartConstr' targs tname (mkName $ 'r' :bname) con
              genSmartConstr' targs tname sname con@(name,args) = do
                varNs <- newNames (length args) "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    vars2' = [| fromRep |]
                    vars2 = map (appE vars2') vars
                    vars3 = zipWith varFunc vars args
                    varFunc v (VarT a) | elem a (init targs) = v
                                       | otherwise           = [| fromRep $v |]
                    varFunc v _ = v
                    val = foldl appE (conE name) vars3
                    sig = genSig targs tname sname (length args) args
                    function = [funD sname [clause pats (normalB [|toRep $ inject $val|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname num args = (:[]) $ do
                let 
                    rvar = mkName "r"
                    avar = mkName "a"
                    targs' = init targs
                    vars = rvar:avar:targs
                    r = varT rvar
                    a = varT avar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = foldl appT (conT ''(:<:)) [ftype, appT (conT ''PF) r]
                    constr2 = appT (conT ''Rep) r
                    typ = foldr appT (appT r a) $ map typFun args
                    typFun a@(VarT e) | elem e (init targs) = appT arrowT $ return a
                                      | otherwise = appT arrowT (appT r $ tupleT 0)
                    typFun a@(ConT _) = appT arrowT $ return a
                    typFun a = appT arrowT $ return a
                    typeSig = forallT (map PlainTV vars) (sequence [constr,constr2]) typ
                sigD sname typeSig
      