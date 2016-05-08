{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
-- {-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
module Lib
    ( ) where

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Ops
import Data.Comp.Render
import Data.Comp.Matching
import Data.Rewriting.Rules
import Data.Rewriting.HigherOrder
import Data.String(IsString(..))
import Data.Maybe(fromMaybe)
import Data.Function (on)
import Data.Monoid
import Data.Proxy
import Data.Ord
import qualified Data.Set as Set
import Derive1

import Control.Monad.Reader
import Control.Monad.Writer
import Data.List (groupBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable

import Debug.Trace

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

b :: Expr SIG Int
b = 1
b2 :: Expr SIG a
b2 = student 1 "hi" 2 rEnglish
class (Rep f,STUDENT :<: PF f) => Student f where
    student :: f Int -> f String -> f Int -> f (MAJOR a) -> f b
    student a b c d = toRep $ iStudent (fromRep a) (fromRep b) (fromRep c) (fromRep d)
instance (Rep r,STUDENT :<: PF r) => Student r

deriving instance Functor (LHS f)
deriving instance Functor (RHS f)

instance (LIT a :<: PF (r f),Functor (r f),Num a,Rep (r f)) => Num (r (f :: * -> *) a) where
    fromInteger = rL . (id :: a -> a) . fromInteger
    abs (fromRep -> a) = rL $ maybe (0::a) id $ do 
        a' <- project a
        return $ abs $ unL a'
instance (LIT a :<: PF (r f),Functor (r f),Fractional a,Rep (r f)) => Fractional (r (f :: * -> *) a) where
    fromRational = rL . (id :: a -> a) . fromRational
instance (LIT String :<: PF (r f),Functor (r f),Rep (r f)) => IsString (r (f :: * -> *) String) where
    fromString = rL . (id :: String -> String) . fromString
    
    {-
instance (Functor f,NUM :<: f,Num b,LIT b :<: f) => Num (Expr f b) where
    fromInteger = Expr . iL . (id :: b -> b) . fromInteger
    signum (Expr a) = Expr . iL $ maybe (0::b) id $ do 
        a' <- project a
        return $ signum $ unL a'
    abs (Expr a) = Expr . iL $ maybe (0::b) id $ do 
        a' <- project a
        return $ abs $ unL a'
    Expr a + Expr b = Expr $ iPlus a b
    Expr a - Expr b = Expr $ iMinus a b
    Expr a * Expr b = Expr $ iTimes a b
instance (Functor f,NUM :<: f,Fractional b,LIT b :<: f) => Fractional (Expr f b) where
    fromRational = Expr . iL . (id :: b -> b) . fromRational
instance (Functor f,NUM :<: f,LIT String :<: f) => IsString (Expr f String) where
    fromString = Expr . iL . (id :: String -> String) . fromString
    -}

matchM' (LHS' _ lhs) = matchM lhs
    
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
rewrite' app (Rule lhs@(LHS' conds _) rhs) t = do
    subst <- match' lhs t
    case conds of
        Nothing -> return ()
        Just c -> do
            cont <- evalBoolean c subst
            guard cont
    substitute app subst rhs --]

match' --[
    :: ( VAR :<: f , LAM :<: f
       , VAR :<: PF (LHS' f) , LAM :<: PF (LHS' f)
       , Functor f, Foldable f, EqF f,OrdF f
       )
    => LHS' f a -> Term (f :&: Set.Set Name) -> Maybe (Data.Rewriting.Rules.Subst (f :&: Set.Set Name))
match' lhs = solveSubstAlpha <=< execWriterT . flip runReaderT oEmpty . matchM' lhs --]

-- Render and Show and Rep Cxt [
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
     --]
    
instance Rep (LHS' f) --[
  where
    type PF (LHS' f) = WILD :+: META (LHS f) :+: f
    toRep  = LHS'' . LHS
    fromRep = unLHS . unLHS'   
--]

data LHS' f a = LHS' { unC :: Maybe (BOOL f a), unLHS' :: LHS f a } --Term (WILD :+: (META (LHS' f) :+: f))}
pattern LHS'' a = LHS' Nothing a

guarded a b = LHS' (Just b) a

data BOOL f a = Boolean (Data.Rewriting.Rules.Subst (f :&: Set.Set Name) -> Maybe Bool)
boolHelper :: (Bool -> Bool -> Bool) -> BOOL f a -> BOOL f b -> BOOL f c
boolHelper boolFun f g = Boolean $ \subs -> do
    f' <- evalBoolean f subs
    g' <- evalBoolean g subs
    return (f' `boolFun` g')
(.&&) = boolHelper (&&)
(.||) = boolHelper (||)
notB f = Boolean $ \subs -> do
    f' <- evalBoolean f subs
    return (not f')
infixr 4 .&& , .||
    
data COND f a = forall b. Cond (COND f b) (COND f b) (f b -> f b -> Ordering) [Ordering] | R (RHS f a)

evalBoolean :: BOOL f a -> Data.Rewriting.Rules.Subst (f :&: Set.Set Name) -> Maybe Bool
evalBoolean (Boolean arg) subs = arg subs
    
ordHelp :: (Traversable f,Ord a,VAR :<: f,LAM :<: f,VAR :<: PF (RHS f),LAM :<: PF (RHS f),APP :<: f,OrdF f)
    => [Ordering] -> RHS f a -> RHS f a -> BOOL f a
ordHelp ords a b = Boolean $ \subs -> do
    a' <- substitute app subs a
    b' <- substitute app subs b
    --trace (showTerm $ stripAnn $ b') (Just undefined)
    return $ any (== compareF (stripAnn a') (stripAnn b')) ords
(.<) :: (Traversable f,Ord a,VAR :<: f,LAM :<: f,VAR :<: PF (RHS f),LAM :<: PF (RHS f),APP :<: f,OrdF f) => RHS f a -> RHS f a -> BOOL f a
(.<) = ordHelp [LT]
(.>) = ordHelp [GT]
(.>=) = ordHelp [GT,EQ]
(.<=) = ordHelp [LT,EQ]
(.==) = ordHelp [EQ]
  
(.|) = guarded
infixr 2 .|

ex :: Expr SIG a
ex = student 1 "NOT matched" 2 rEnglish

{-
            (Fractional (rhs Float),
               Num (rhs Int),
               IsString (rhs String),
               Traversable f,
               OrdF f,
               VAR :<: f,
               VAR :<: PF (RHS f),
               LAM :<: f,
               LAM :<: PF (RHS f),
               APP :<: f,
               LIT Int :<: PF (RHS f),
               Student rhs,
               MAJOR :<: PF rhs,
               Student (LHS f))
               -}
--student_rule3 :: _ => MetaId Int -> Rule (LHS' f) rhs
student_rule3 x y= student (meta x) __ (meta y) __ .| meta x .<= 1 .&&
                                                      meta x .> 0  .&&
                                                      meta y .> meta x
                    ===>
                  student 99999 "matched!" 2 rEnglish
                  
student_rule2 x = student (meta x) __ __ __ .| meta x .> 1
                    ===>
                  student 99999 "matched!" 2 rMath

main = do
    let e = unExpr ex
    putStrLn $ show e
    drawTerm $ maybe e id $ fmap stripAnn $ rewrite' app (quantify (student_rule3 )) $ prepare e
    drawTerm $ maybe e id $ fmap stripAnn $ rewrite' app (quantify (student_rule2 )) $ prepare e
