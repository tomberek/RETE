{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module RETE.Derive1 (smartRep,smartRep',Rep'(..)
    ) where
    
import Language.Haskell.TH hiding (Cxt)
import Control.Monad
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Term
import Data.Rewriting.Rules
import Data.Maybe

class Rep' r
  where
    type PF' r :: * -> *
    type PHOLE' r :: *
    type PHOLE'' r :: *
    toRep'   :: Cxt (PHOLE'' r) (PF' r) (PHOLE' r) -> r a
    fromRep' :: r a -> Cxt (PHOLE'' r) (PF' r) (PHOLE' r)

smartRep' fname = do
    TyConI (DataD _cxt tname targs mkind constrs _deriving) <- abstractNewtypeQ $ reify fname
    cons <- mapM normalConExp constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname con = do
                let bname = nameBase $ fst con
                genSmartConstr' targs tname (mkName $ 's' :bname) con
              genSmartConstr' targs tname sname con@(name,args) = do
                varNs <- newNames (length args) "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    vars2' = [| fromRep |]
                    vars2 = map (appE vars2') vars
                    vars3 = zipWith varFunc vars args
                    varFunc v (VarT a) | elem a (init targs) = v
                                       | otherwise           = [| fromRep' $v |]
                    varFunc v _ = [| fromRep' $v |]
                    val = foldl appE (conE name) vars3
                    sig = genSig targs tname sname (length args) args
                    function = [funD sname [clause pats (normalB [|toRep' $ inject $val|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname num args = (:[]) $ do
                varNs <- newNames (length args +1) "a"
                let 
                    rvar = mkName "r"
                    avar = mkName "a"
                    targs' = init targs
                    vars = rvar:avar:targs ++ varNs
                    r = varT rvar
                    a = varT avar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = foldl appT (conT ''(:<:)) [ftype, appT (conT ''PF') r]
                    constr2 = appT (conT ''Rep') r
                    typ = foldr appT (appT r a) $ map (typFun) $ zip varNs args
                    typFun (v,a@(VarT e)) | elem e (targs') = appT arrowT $ varT e
                                      | otherwise = appT arrowT (appT r $ varT v)
                    typFun (v,a@(ConT _)) = appT arrowT $ return a
                    typFun (v,a@(AppT app e'@(VarT e))) | elem e (targs') = appT arrowT $ appT r $ appT (return app) $ return e'
                    typFun (_,a2) = appT arrowT $ appT r $ a
                    typeSig = forallT (map PlainTV vars) (sequence [constr,constr2]) typ
                sigD sname typeSig
       
smartRep fname = do
    TyConI (DataD _cxt tname targs mkind constrs _deriving) <- abstractNewtypeQ $ reify fname
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
                    varFunc v _ = [| fromRep $v |]
                    val = foldl appE (conE name) vars3
                    sig = genSig targs tname sname (length args) args
                    function = [funD sname [clause pats (normalB [|toRep $ inject $val|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname num args = (:[]) $ do
                varNs <- newNames (length args +1) "a"
                let 
                    rvar = mkName "r"
                    avar = mkName "a"
                    targs' = init targs
                    vars = rvar:avar:targs ++ varNs
                    r = varT rvar
                    a = varT avar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = foldl appT (conT ''(:<:)) [ftype, appT (conT ''PF) r]
                    constr2 = appT (conT ''Rep) r
                    typ = foldr appT (appT r a) $ map (typFun) $ zip varNs args
                    typFun (v,a@(VarT e)) | elem e (targs') = appT arrowT $ varT e
                                      | otherwise = appT arrowT (appT r $ varT v)
                    typFun (v,a@(ConT _)) = appT arrowT $ return a
                    typFun (v,a@(AppT app e'@(VarT e))) | elem e (targs') = appT arrowT $ appT r $ appT (return app) $ return e'
                    typFun (_,a2) = appT arrowT $ appT r $ a
                    typeSig = forallT (map PlainTV vars) (sequence [constr,constr2]) typ
                sigD sname typeSig
      