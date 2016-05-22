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
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module RETE.Lib6
    ( ) where

import Data.Comp.Multi
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Ops
import Data.Comp.Multi.TermRewriting
import Data.Comp.Multi.Matching
import Data.Comp.Multi.Ordering
import Data.Comp.Multi.Equality
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Render

--import Data.Comp.TermRewriting (matchRules,matchRule,appRule,reduce,appTRS,parallelStep,parTopStep,Step,Rule)
import Data.String(IsString(..))
import Data.Maybe(fromMaybe,fromJust)
import qualified Data.Set as Set
import Data.Map

import Control.Monad (guard,(>=>),(<=<))
import Control.Monad.Reader
import Control.Monad.Writer
import Debug.Trace
import Unsafe.Coerce
import Data.Map as Map

data STUDENT a i where
    Student :: a Int -> a String -> a Int -> a Major -> STUDENT a i
data Major
data MAJOR (a:: * -> *) i where
    English :: MAJOR a i
    Math :: MAJOR a i
    Physics :: MAJOR a i
data LIT b (a:: * -> *) i where
    L :: b -> LIT b a b
data NUM a i where
    Plus :: a i -> a i -> NUM a i
    Minus :: a i -> a i -> NUM a i
    Times :: a i -> a i -> NUM a i
    Negate :: a i -> NUM a i
    Divide :: a i -> a i -> NUM a i

instance KOrd (Hole2 f a) where
    H a _ `kcompare` H b _ = a `compare` b
    Wild `kcompare` _ = LT
    _ `kcompare` Wild = GT
instance KEq (Hole2 f a) where
    H a _ `keq` H b _ = a == b
    Wild `keq` _ = True
    _ `keq` _ = False

instance (HFunctor f,ShowHF f) => KShow (Hole2 f a) where
    kshow (H s b) = K $ "Hole2 " ++ show s ++ show b
    kshow (Wild) = K "Wild"
instance Ord b => OrdHF (LIT b) where
    L a `compareHF` L b = a `compare` b
    
__ :: Cxt Hole f (Hole2 f a) i
__ = Hole Wild


data Hole2 f (a :: * -> *) i = H String [([Ordering],Cxt Hole f (Hole2 f a) i)] | Wild
data Wild i = W
type SIG = STUDENT :+: NUM :+: MAJOR :+: LIT Int :+: LIT String :+: LIT Float
--[
$(derive [makeHFunctor,makeHTraversable,makeHFoldable,makeShowConstr,
          makeEqHF,makeOrdHF,makeShowHF,smartConstructors] [''STUDENT,''MAJOR,''NUM])
$(derive [makeHFunctor,makeHTraversable,makeHFoldable,
          makeEqHF,makeShowHF,smartConstructors] [''LIT])
--]
s :: (LIT i :<: f) => i -> Cxt h f a i
s = iL
--]
instance (LIT i :<: f,Num i) => Num (Cxt h f a i) where
    fromInteger = s . fromInteger
instance (LIT String :<: f) => IsString (Cxt h f a String) where
    fromString = s . fromString

lhs2 :: Num b => HoledCxt Hole SIG a b
lhs2 = iStudent ("id" .< 3) ("s" .< "hi") __ __

type HoledCxt h f a i = Cxt h f (Hole2 f a) i

v2 a func term = Hole (H a [(func,term)])
h2 a = Hole (H a [])
(.<),(.=),(.>),(.!=) :: (HFunctor f,HTraversable f) => String -> HoledCxt Hole f a i -> HoledCxt Hole f a i
a .< b = v2 a [LT] $ b
a .= b = v2 a [EQ] $ b
a .> b = v2 a [GT] $ b
a .!= b = v2 a [LT,GT] $ b

(===>) = (,)
instance Show a => Render (LIT a)
instance Render MAJOR
instance Render NUM
instance Render STUDENT 
instance Show a => ShowConstr (LIT a) where
    showConstr (L a) = "L " ++ show a
example :: Rule SIG SIG (Hole2 SIG a) i
example = iStudent ("x" .< 2) "hi" (h2 "x") __ ===> iStudent (h2 "x") "MATCHED" (h2 "x") iEnglish

main :: IO ()
main = do
    --drawTerm $ reduce (parallelStep [(g,g2),(f,f2)]) f3
    --putStr "\ESC[2J" -- clear screen
    print "hi"
    --drawTerm (iMath :: Term SIG i)
    --drawTerm $ (iStudent 1 "hi" 0 iMath :: Cxt NoHole SIG a i)
    drawTerm $ reduce (appRule' example)  (iStudent 1 "hi" 1 iMath :: Term SIG i)
    print "finish"
    
appRule' :: (HFoldable g, EqHF g,OrdHF g) => Rule g g (Hole2 g t) i
                  -> Cxt h g (K ()) i -> Maybe ( (Cxt h g (K ()) i) )
appRule' rule t = do
    (res, subst) <- matchRule rule t
    if filterConditions subst
    then return ()
    else Nothing
    let res2 = flip substHoles'' subst res
    case res2 of 
        E a -> do 
            Just $ unsafeCoerce a

filterConditions subst = and x where
    func x = case x of
            (E (H v conds),b) -> fmap (\(ords,cond) -> elem (compare b (substHoles' cond subst)) ords ) conds
            (E Wild,b) -> []
    x = concatMap func $ toList subst

substHoles'' :: (HFunctor f, HFunctor g, f :<: g, KOrd v) =>
    Cxt h' f v i -> Map (E v) (E (Cxt h g a)) -> E (Cxt Hole g a)
substHoles'' c m = E $ substHoles (t' m) c

t' :: (KOrd v) => Map (E v) (E (Cxt h g a)) -> (v :-> Cxt Hole g a)
t' m v = (\case {E a -> unsafeCoerce a}) $ fromJust $ Map.lookup (E v) m












-- | Variable identifier
type Name = Integer

-- | Typed meta-variable identifiers
newtype MetaId a = MetaId Name
  deriving (Eq, Show, Ord, Num, Enum, Real, Integral)

-- | Rules that may take a number of meta-variables as arguments. Those meta-variables are
-- implicitly forall-quantified.
class Quantifiable rule
  where
    -- | Rule type after quantification
    type RuleType rule

    -- | Quantify a rule starting from the provided variable identifier
    quantify' :: Name -> rule -> RuleType rule

-- | Base case: no meta-variables
instance Quantifiable (Rule f f a i)
  where
    type RuleType (Rule f f a i) = Rule f f a i
    quantify' _ = id

-- | Recursive case: one more meta-variable
instance (Quantifiable rule, m ~ MetaId a) => Quantifiable (m -> rule)
  where
    type RuleType (m -> rule) = RuleType rule
    quantify' i rule = quantify' (i+1) (rule (MetaId i))

-- | Forall-quantify the meta-variable arguments of a rule
quantify :: (Quantifiable rule, RuleType rule ~ Rule f f a i) => rule -> Rule f f a i
quantify = quantify' 0