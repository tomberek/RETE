{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Lib
    ( ) where

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Render
import Data.Comp.TermRewriting (reduce)
import Data.Rewriting.Rules
import Data.Rewriting.FirstOrder (bottomUp)
import Data.Rewriting.HigherOrder
import Data.String(IsString(..))
import Data.Maybe(fromMaybe)
import qualified Data.Set as Set
import Derive1

import Control.Monad (guard,(>=>))

data STUDENT a = Student a a a a deriving Show
data MAJOR a = English | Math | Physics deriving Show
newtype LIT b a = L {unL ::b} deriving Show
data NUM a = Plus a a | Minus a a | Times a a | Negate a | Divide a a deriving Show

--[
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeOrdF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR,''NUM])
$(derive [makeEqF,makeShowF,smartConstructors,makeShowConstr] [''WILD])
$(derive [smartRep] [''STUDENT,''LIT,''MAJOR]) 
$(derive [makeOrdF] [''VAR,''LAM,''APP])
--]

type SIG = NUM :+: STUDENT :+: MAJOR :+: LIT Int :+: LIT String :+: LIT Float :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.
newtype Expr f a = Expr {unExpr :: Term f} deriving Functor

-- Restricted smart constructors [
student :: (Rep r,STUDENT :<: PF r) => r Int -> r String -> r Int -> r (MAJOR b) -> r b
student = rStudent

l :: (LIT a :<: PF r, Rep r) => a -> r a
l = rL
--]

deriving instance Functor (LHS f)
deriving instance Functor (RHS f)

instance (LIT a :<: PF (r f),Functor (r f),Num a,Rep (r f)) => Num (r (f :: * -> *) a) where
    fromInteger = l . fromInteger
    abs (fromRep -> a) = l $ fromMaybe 0 $ do 
        a' <- project a
        return $ abs $ unL a'
instance (LIT a :<: PF (r f),Functor (r f),Fractional a,Rep (r f)) => Fractional (r (f :: * -> *) a) where
    fromRational = l . fromRational
instance (LIT String :<: PF (r f),Functor (r f),Rep (r f)) => IsString (r (f :: * -> *) String) where
    fromString = l . fromString
    
rewrite' --[
    :: ( VAR :<: f
       , LAM :<: f
       , APP :<: f
       , VAR :<: PF (LHS' f)
       , LAM :<: PF (LHS' f)
       , VAR :<: PF (RHS f)
       , LAM :<: PF (RHS f)
       , Traversable f, EqF f,OrdF f,Render f
       , g ~ (f :&: Set.Set Name)
       )
    => (Term g -> Term g -> Term g)  -- ^ Application operator
    -> Rule (LHS' f) (RHS f)
    -> Term g
    -> Maybe (Term g)
rewrite' app (Rule lhs'@(LHS' conds lhs) rhs) t = do
    subst <- match lhs t
    case conds of
        Nothing -> return ()
        Just c -> do
            cont <- unBOOL (unTerm c) subst
            guard cont
    substitute app subst rhs --]

-- Render and Show and Rep Expr [
instance Render NUM
instance Render STUDENT
instance Show b => Render (LIT b)
instance Render MAJOR
instance Render WILD
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep
    
instance Rep (Expr f) where
    type PF (Expr f) = f
    toRep = Expr
    fromRep = unExpr
    
instance Rep (LHS' f)
  where
    type PF (LHS' f) = WILD :+: META (LHS f) :+: f
    toRep  = LHS'' . LHS
    fromRep = unLHS . unLHS'   
--]

data LHS' f a = LHS' { unC :: Maybe (Conditional f), unLHS' :: LHS f a } --Term (WILD :+: (META (LHS' f) :+: f))}
pattern LHS'' a = LHS' Nothing a

guarded a b = LHS' (Just b) a

data BOOL f a = Boolean {unBOOL :: Data.Rewriting.Rules.Subst (f :&: Set.Set Name) -> Maybe Bool}
            | a :&& a
            | a :|| a
type Conditional f = Term (BOOL f)

boolHelper boolFun f g = Term $ Boolean $ \subs -> do
    f' <- unBOOL (unTerm f) subs
    g' <- unBOOL (unTerm g) subs
    return (f' `boolFun` g')
(.&&) = boolHelper (&&)
(.||) = boolHelper (||)
infixr 4 .&& , .||
notB f = Boolean $ unBOOL f >=> return . not
    
ordHelp :: (Traversable f,Ord a,VAR :<: f,LAM :<: f,VAR :<: PF (RHS f),LAM :<: PF (RHS f),APP :<: f,OrdF f)
    => [Ordering] -> RHS f a -> RHS f a -> Term (BOOL f)
ordHelp ords a b = Term $ Boolean $ \subs -> do
    a' <- substitute app subs a
    b' <- substitute app subs b
    return $ elem (compareF (stripAnn a') (stripAnn b')) ords
    
(.<) = ordHelp [LT]
(.>) = ordHelp [GT]
(.>=) = ordHelp [GT,EQ]
(.<=) = ordHelp [LT,EQ]
(.==) = ordHelp [EQ]
  
(.|) = guarded
infixr 2 .|

ex :: Expr SIG a
ex = student 1 "NOT matched" 2 rEnglish

--student_rule3 :: _ => MetaId Int -> Rule (LHS' f) rhs
student_rule x y= student (meta x) __ (meta y) __ .| meta x .<= 1 .&&
                                                      meta x .> 0  .&&
                                                      meta y .> meta x
                    ===>
                  student 99999 "matched!" 2 rEnglish
                  
student_rule2 x = student (meta x) __ __ __ .| meta x .> 1
                    ===>
                  student 99999 "matched!" 2 rMath

main = do
    let e = unExpr ex
    drawTerm $  rewriteWith (reduce $ rewrite' app $ quantify student_rule) e
    drawTerm $  rewriteWith (reduce $ rewrite' app $ quantify student_rule2) e
