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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
-- {-# OPTIONS_GHC -fno-warn-missing-methods #-}
module Lib
    ( 
    ) where

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Render
import Data.Rewriting.Rules
import Data.Rewriting.HigherOrder
import Data.String(IsString(..))
import Data.Maybe(fromMaybe)
import Data.Function (on)
import Data.Monoid

data STUDENT a = Student a a a a deriving Show
data LIT t (a :: k) = L {unL :: t} deriving Show
data MAJOR a = English | Math | Physics deriving Show
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR])
instance Render STUDENT
instance Show t => Render (LIT t)
instance Render MAJOR
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep

type SIG = STUDENT :+: LIT String :+: LIT Int :+: LIT Float :+: MAJOR :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.
newtype Expr a = Expr {unExpr::Term SIG}

instance Rep Expr where
    type PF Expr = SIG
    toRep = Expr
    fromRep = unExpr
    
-- Constructors in a "Finally Tagless style"
class Major f where
    english :: f a
    math :: f a
    physics :: f a
    
instance (MAJOR :<: f) => Major (Cxt h f) where
    english = inject English
    math = inject Math
    physics = inject Physics
    
class Student f where
    student :: LIT Int (f a) -> LIT String (f a) -> LIT Float (f a) -> MAJOR (f a) -> f a
    
instance (LIT Int :<: f,LIT Float :<: f,LIT String :<: f,MAJOR :<: f,STUDENT :<: f) => Student (Cxt h f) where
    student a b c d = inject $ Student (inject a) (inject b) (inject c) (inject d)

--p2 = iStudent (0+3) "hi" 2.1 iEnglish
instance (LIT Int :<: f,LIT Float :<: f,Functor f) => Fractional (Cxt NoHole f a) where
    fromRational = toCxt . fromRational
instance (LIT Int :<: f,Functor f) => Num (Cxt NoHole f a) where
    --fromInteger = toCxt . fromInteger
    fromInteger = inject . L . (id :: Int -> Int) . fromInteger
    
instance {-# OVERLAPPING #-} (LIT String :<: PF f,LIT String :<: f, Rep f) => IsString (f a) where
    fromString  =  toRep . inject . L . (id :: String -> String) . fromString

    {-
instance (LIT String :<: f,Functor f) => IsString (Cxt h f a) where
    fromString = toCxt . fromString
    
instance (LIT String :<: f) => IsString (f (Cxt NoHole f a)) where
    fromString = unTerm . inject . L . (id :: String -> String) . fromString
    -}

instance Num a => Num (LIT a b) where
    fromInteger = L . fromInteger
    abs (L a) = L (abs a)
    signum (L a) = L (signum a)
    L a + L b = L $ a + b
    L a * L b = L $ a * b
    L a - L b = L $ a - b
instance Fractional a => Fractional (LIT a b) where
    fromRational = L . fromRational
    recip (L a) = L $ recip a
instance IsString a => IsString (LIT a b) where
    fromString = L . fromString

c :: Term SIG
c = iStudent (0+1) "hi" 1.2 iEnglish

a :: Term (LIT Int)
a = 0 + 1

student_rule = iStudent __ __ __ iEnglish ====> iStudent 1 "world" 1.5 iMath

a ====> b = on (===>) unTerm a b
main = do
    drawTerm c
    -- drawTerm $ stripAnn $ applyFirst app [quantify student_rule] $ prepare c
   ---} 
    {-
data S a = S a a
$(derive [makeFunctor,makeFoldable,makeTraversable,smartConstructors] [''S])
class Stud r where
    stud :: LIT Int (r a) -> LIT Float (r a) -> r a -- is f Term? no, Cxt h f a
instance (LIT Int :<: f,LIT Float :<: f,S :<: f) => Stud (Cxt h f) where
    stud a b = inject $ S (inject a) (inject b)

    
z :: Term (S :+: LIT Int :+: LIT Float :+: VAR)
z = stud 2 2.3

z2 = stud 2 1.3 ===> stud 2 1.0
---}