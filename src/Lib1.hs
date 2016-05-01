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
import qualified Data.Set as Set
import Derive1

data STUDENT a = Student a a a a deriving Show
data MAJOR a = English | Math | Physics deriving Show
data LIT a = I Int | F Float | S String deriving Show

$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR])
$(derive [makeEqF,makeShowF,smartConstructors,makeShowConstr] [''WILD])
instance Render STUDENT
instance Render LIT
instance Render MAJOR
instance Render WILD
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep
instance Functor f => Rep (Cxt NoHole f) where
    type PF (Cxt NoHole f) = f
    toRep = toCxt
    fromRep = fmap (const ())
    
$(derive [smartRep] [''STUDENT])

e2 :: LHS SIG a
e2 = rStudent __ "gj" 1.3 rMath

rF a = toRep $ iF a
rS a = toRep $ iS a
rEnglish = toRep iEnglish
rMath = toRep iMath
rPhysics = toRep iPhysics

type SIG = LIT :+: STUDENT :+: MAJOR :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.

--extract def = maybe def unL . proj . (\(Term m) -> m) . fromRep
instance (Rep (r f),LIT :<: PF (r f),LIT  :<: f) => Num (r f a) where
    fromInteger = toRep . iI . fromInteger
    {-
    signum (extract (0::a) -> a) = toRep $ iL (signum a)
    abs (extract (0::a) -> a) = toRep $ iL (abs a)
    (extract (0::a) -> a) + (extract (0::a) -> b) = toRep $ iL $ a + b
    (extract (1::a) -> a) * (extract (1::a) -> b) = toRep $ iL $ a * b
    (extract (0::a) -> a) - (extract (0::a) -> b) = toRep $ iL $ a - b
    -}
instance (Rep (r f),LIT :<: PF (r f),LIT :<: f) => Fractional (r f a) where
    fromRational = toRep . iF . fromRational
    --recip (extract (1::a) -> a) = toRep $ iL $ recip a
   -- -}
instance (Rep (r f),LIT :<: PF (r f),LIT :<: f) => IsString (r f a) where
    fromString = toRep . iS . fromString

e4 :: Term SIG
e4 = rEnglish

e5 :: Term LIT
e5 = rI 3

e :: Term SIG
e = rStudent 1 "hi" 1.2 rEnglish

rI :: (LIT :<: PF r,Rep r) => Int -> r a
rI a = toRep $ iI $ a

--rStudent :: (STUDENT :<: PF r,Rep r) => r Int -> r String -> r Float -> r (MAJOR a) -> r a
rStudent :: (STUDENT :<: PF r,Rep r) => r () -> r () -> r () -> r () -> r a
rStudent a b c d= toRep $ iStudent (fromRep a) (fromRep b) (fromRep c) (fromRep d)

student_rule = rStudent 1 "hi" 1.2 rEnglish ===> rStudent 3 "matched!" 1.2 rMath
student_rule' x = rStudent __ __ __ rEnglish ===> rStudent 3 "matched!2" 1.2 rEnglish 
a ==> b = toRep a ===> toRep b

main = do
    drawTerm e5
    drawTerm (unLHS e2)
    drawTerm $ stripAnn $ applyFirst app [quantify student_rule ] $ prepare e
    drawTerm $ stripAnn $ applyFirst app [quantify (student_rule' :: MetaId _ -> _ ) ] $ prepare e
    print "hi"

{-
instance MetaVar (Cxt h f) where
    type MetaRep (Cxt h f) = MetaId
    type MetaArg (Cxt h f) = Var (Cxt h f)
    metaExp = inject . Meta
type instance Var (Cxt h (WILD :+: (META (LHS f) :+: f))) = VAR
type instance Var (Cxt h (META (RHS f) :+: f)) = VAR
-}