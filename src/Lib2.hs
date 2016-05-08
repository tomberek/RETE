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
--{-# OPTIONS_GHC -fno-warn-missing-methods #-}
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
data LIT b a = L {unL ::b} deriving Show
data NUM a = Plus a a | Minus a a | Times a a | Negate a | Divide a a

--[
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeOrdF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR,''NUM])
$(derive [makeEqF,makeShowF,smartConstructors,makeShowConstr] [''WILD])
$(derive [smartRep] [''STUDENT,''LIT,''MAJOR]) 
$(derive [makeOrdF] [''VAR,''LAM,''APP])
--]
type SIG = STUDENT :+: MAJOR :+: LIT Int :+: LIT String :+: LIT Float :+: ADDONS

type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.


data Expr f a = Expr {unExpr :: Term f}
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

--[
compareMod :: (OrdF f, Functor f, Foldable f) => f a -> f b -> Ordering -> Maybe [(a,b)]
compareMod s t ordering
    | compareF (unit s) (unit' t) == ordering = Just args
    | otherwise = Nothing
    where unit = fmap (const ())
          unit' = fmap (const ())
          args = toList s `zip` toList t
matchM' :: forall f a --[
    .  ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS' f)
       , LAM :<: PF (LHS' f)
       , Functor f, Foldable f, EqF f
       , OrdF f
       )
    => LHS' f a
    -> Term (f :&: Set.Set Name)
    -> ReaderT AlphaEnv (WriterT (Data.Rewriting.Rules.Subst (f :&: Set.Set Name)) Maybe) ()
matchM' (LHS' cond (LHS lhs)) t = go lhs t 
  where
    go (Term (Inl WildCard)) _ = return ()
    
    go (Term (Inr (Inl (Meta mv)))) t = ReaderT $ \env -> goo env mv t
      where
        goo :: AlphaEnv
            -> MetaExp (LHS f) b
            -> Term (f :&: Set.Set Name)
            -> WriterT (Data.Rewriting.Rules.Subst (f :&: Set.Set Name)) Maybe ()
        goo env (MVar (MetaId m)) t
            | Set.null (Set.intersection boundInPatt freeIn_t) = tell [(m,t)]
            | otherwise = fail "Variables would escape"
          where
            boundInPatt = Map.keysSet $ snd env
            freeIn_t    = getAnn t
        goo env (MApp mv (Var v)) t = do
          let Just w = oLookupL v env
                -- Lookup failure is a bug rather than a matching failure
          goo env mv (Term (inj (Lam w t) :&: Set.delete w (getAnn t)))
              
    go p (Term (g :&: _))
      | Just (Var v) <- project p
      , Just (Var w) <- proj g
      = do
          env <- ask
          guard ((v,w) `oMember` env)
            -- Rules should be closed, so `w` can't be free

    go p (Term (g :&: _))
      | Just (Lam v a) <- project p
      , Just (Lam w b) <- proj g
      = local (oInsert (v,w)) $ go a b

    go (Term (Inr (Inr (f)))) (Term (g :&: _))
      | Just subs <- eqMod f g
      = mapM_ (uncurry go) subs
      
    go _ _ = fail "No match" --]
    
type instance Var (LHS' f) = VAR
instance (VAR :<: PF (LHS' f), LAM :<: PF (LHS' f), Functor f, Foldable f) =>
    Bind (LHS' f)
  where
    var = LHS'' . LHS . inject . Var . toInteger
    lam = mkLam id

    
rewrite' --[
    :: forall f g. ( VAR :<: f
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
    (subst :: forall . Data.Rewriting.Rules.Subst (f :&: Set.Set Name)) <- match' lhs t
    c <- conds
    cont <- evalBoolean c subst
    guard cont
    substitute app subst rhs --]

match' --[
    :: ( VAR :<: f
       , LAM :<: f
       , VAR :<: PF (LHS' f)
       , LAM :<: PF (LHS' f)
       , Functor f, Foldable f, EqF f,OrdF f
       )
    => LHS' f a -> Term (f :&: Set.Set Name) -> Maybe (Data.Rewriting.Rules.Subst (f :&: Set.Set Name))
match' lhs = solveSubstAlpha <=< execWriterT . flip runReaderT oEmpty . matchM' lhs --]

-- Render and Show and Rep Cxt [
instance Render STUDENT
instance Show b => Render (LIT b)
instance Render MAJOR
instance Render WILD
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep
instance Functor f => Rep (Cxt NoHole f) where
    type PF (Cxt NoHole f) = f
    toRep = toCxt
    fromRep = fmap (const ()) --]
    
-- Num, Fractional, IsString [
extract def = maybe def unL . proj . (\(Term m) -> m) . fromRep
fun = (\(Term m) -> m) . fromRep 
instance (Rep (r f),f :<: PF (r f),LIT Int :<: PF (r f)) => Num (r f a) where
    fromInteger = toRep . iL . (id :: Int -> Int) . fromInteger
    signum (extract (0::Int) -> a) = toRep $ iL (signum a)
    abs (extract (0::Int) -> a) = toRep $ iL (abs a)
    (extract (0::Int) -> a) + (extract (0::Int) -> b) = toRep $ iL $ a + b
    (extract (1::Int) -> a) * (extract (1::Int) -> b) = toRep $ iL $ a * b
    (extract (0::Int) -> a) - (extract (0::Int) -> b) = toRep $ iL $ a - b
instance (Rep (r f),f :<: PF (r f),LIT Float :<: PF (r f),LIT Int :<: PF (r f))
        => Fractional (r f a) where
    fromRational = toRep . iL . (id :: Float -> Float ) . fromRational
    recip (extract (1::Float) -> a) = toRep $ iL $ recip a
instance (Rep (r f),f :<: PF (r f),LIT String :<: PF (r f)) => IsString (r f a) where
    fromString = toRep . iL . (id :: String -> String) . fromString --]

instance Rep (LHS' f)
  where
    type PF (LHS' f) = WILD :+: META (LHS f) :+: f
    toRep  = LHS'' . LHS
    fromRep = unLHS . unLHS'   
--]
e :: Term SIG
e = rStudent 1 "NOT matched" 1.2 rEnglish

data LHS' f a = LHS' { unC :: Maybe (BOOL f a), unLHS' :: LHS f a } --Term (WILD :+: (META (LHS' f) :+: f))}
pattern LHS'' a = LHS' Nothing a

guarded a b = LHS' (Just b) a

data BOOL f a = Boolean (Data.Rewriting.Rules.Subst (f :&: Set.Set Name) -> Maybe Bool)
data COND f a = forall b. Cond (COND f b) (COND f b) (f b -> f b -> Ordering) [Ordering] | R (RHS f a)
a = Cond (R $ RHS $ iL (4 ::Int)) (R $ RHS $ iL (5::Int)) (compareF :: LIT Int Int -> LIT Int Int -> Ordering) [LT]

evalBoolean :: (Render f,Traversable f,OrdF f,VAR :<: f,LAM :<: f,VAR :<: PF (RHS f), LAM :<: PF (RHS f),APP :<: f) =>
    BOOL f a -> Data.Rewriting.Rules.Subst (f :&: Set.Set Name) -> Maybe Bool
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
infixr 7 .|

student_rule x = rStudent (meta x) __ __ __ .| meta x .<= rL (1::Int) ===> rStudent 99999 "matched" 1.2 rMath
student_rule2 x = rStudent (meta x) __ __ __ .| meta x .> rL (1::Int) ===> rStudent 99999 "matched" 1.2 rMath

main = do
    drawTerm $ maybe e id $ fmap stripAnn $ rewrite' app (quantify (student_rule  )) $ prepare e
    drawTerm $ maybe e id $ fmap stripAnn $ rewrite' app (quantify (student_rule2  )) $ prepare e
