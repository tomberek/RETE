{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Derive1 (smartRep
    ) where
    
import Language.Haskell.TH hiding (Cxt)
import Control.Monad
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Term
import Data.Rewriting.Rules

smartRep fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    cons <- mapM normalConExp constrs
    reportError $ show cons
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname con = do
                let (name,_) = con
                let bname = nameBase name
                genSmartConstr' targs tname (mkName $ 'r' : 'r' : bname) name con
              genSmartConstr' targs tname sname name con = do
                let (_,args) = con
                reportError $ show con
                reportError $ show name
                reportError $ show args
                varNs <- newNames (length args) "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    vars2' = [| fromRep |]
                    vars2 = map (appE vars2') vars
                    val = foldl appE (conE name) vars2
                    sig = genSig targs tname sname (length args) args
                    function = [funD sname [clause pats (normalB [|toRep $ inject $val|]) []]]
                f <- sequence function
                reportError $ show f
                sequence $ sig ++ function
              genSig targs tname sname num args = (:[]) $ do
                --names <- sequence $ take args $ repeat (newName "temp")
                let fvar = mkName "f"
                    hvar = mkName "h"
                    avar = mkName "a"
                    targs' = init targs
                    vars = fvar:hvar:avar:targs'
                    f = varT fvar
                    h = varT hvar
                    a = varT avar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = foldl appT (conT ''(:<:)) [ftype, appT (conT ''PF) f]
                    constr2 = foldl appT (conT ''Rep) [f]
                    constr3 = foldl appT (conT ''Functor) [appT (conT ''PF) f]
                    typ = foldr appT (appT f a) $ map (appT arrowT) $ map return args
                    --typ = foldl appT (f) [a]
                    --typ = foldl appT (conT ''Cxt) [h, f, a]
                    --typ = foldr appT (appT f a) $ (map (appT arrowT) $ map (appT f . varT) names)
                    typeSig = forallT (map PlainTV vars) (sequence [constr,constr2,constr3]) typ
                sigD sname typeSig
              genSig _ _ _ _ _ = []
              
                 {-
 class St f where
    st :: f Int -> f String -> f Float -> f (MAJOR a) -> f a
instance (Rep (r f),Functor (PF (r f)),STUDENT :<: PF (r f),f :<: SIG) => St (r f) where
    st a b c d = toRep $ toCxt $ iStudent (prep a) (prep b) (prep c) (prep d)
        where prep = fmap (const ()) . deepInject . fromRep
    
                 
instance (Rep f, MAJOR :<: PF f) => Major f where
    english = toRep iEnglish
    math = toRep iMath
    physics = toRep iPhysics
    -} 