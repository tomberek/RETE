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
-- {-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
-- {-# OPTIONS_GHC -fno-warn-missing-methods #-}
module Lib
    ( 
    ) where

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
import qualified Data.Set as Set

import Derive

data STUDENT a = Student a a a a deriving Show
--data LIT t (a :: *) = L {unL :: t} deriving Show
data LIT a t where
    L :: a -> LIT a t
unL :: LIT a t -> a
unL (L a) = a
deriving instance Show a => Show (LIT a a)
data MAJOR a = English | Math | Physics deriving (Show,Eq)
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR])
$(derive [smartRep] [''MAJOR])
$(derive [makeEqF,makeShowF,smartConstructors,makeShowConstr] [''WILD])
instance Render STUDENT
instance Show t => Render (LIT t)
instance Render WILD
instance Render MAJOR
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep
type SIG = MAJOR :+: STUDENT :+: LIT String :+: LIT Int :+: LIT Float :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.

class Major f where
    english :: f a
    math :: f a
    physics :: f a
class St f where
    rStudent :: f Int -> f String -> f Float -> f (MAJOR a) -> f a
instance (Rep (r f),Functor (PF (r f)),STUDENT :<: PF (r f),f :<: SIG) => St (r f) where
    rStudent a b c d = toRep $ toCxt $ iStudent (prep a) (prep b) (prep c) (prep d)
        where prep = fmap (const ()) . deepInject . fromRep
        
extract def = maybe def unL . proj . (\(Term m) -> m) . fromRep
instance (Rep (r f),LIT a :<: PF (r f),LIT a :<: f,Num a) => Num (r f a) where
    fromInteger = toRep . iL . (id :: a -> a) . fromInteger
    signum (extract (0::a) -> a) = toRep $ iL (signum a)
    abs (extract (0::a) -> a) = toRep $ iL (abs a)
    (extract (0::a) -> a) + (extract (0::a) -> b) = toRep $ iL $ a + b
    (extract (1::a) -> a) * (extract (1::a) -> b) = toRep $ iL $ a * b
    (extract (0::a) -> a) - (extract (0::a) -> b) = toRep $ iL $ a - b
instance (Rep (r f),LIT a :<: PF (r f),LIT a :<: f,Fractional a) => Fractional (r f a) where
    fromRational = toRep . iL . (id :: a -> a) . fromRational
    recip (extract (1::a) -> a) = toRep $ iL $ recip a
   -- -}
instance (Rep (r f),LIT a :<: PF (r f),LIT a :<: f,IsString a) => IsString (r f a) where
    fromString = toRep . iL . (id :: a -> a) . fromString

instance Functor f => Rep (Cxt NoHole f) where
    type PF (Cxt NoHole f) = f
    toRep = toCxt
    fromRep = fmap (const ())
    
e3 :: Term SIG
e3 = rStudent 3 "hi" 2 rEnglish

e4 :: Term SIG
e4 = rStudent 3 "hi" 2.0 (toCxt $ deepInject e3)

student_rule :: MetaId String -> Rule (LHS SIG) (RHS SIG)
student_rule x = rStudent 3 (meta x) __ rEnglish ===> rStudent 4 "matched" 3 rMath
a ==> b = toRep a ===> toRep b
main = do
    drawTerm e3
    drawTerm $ stripAnn $ applyFirst app [quantify (student_rule) ] $ prepare e3
    print "hi"
