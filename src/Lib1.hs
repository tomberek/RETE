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

data STUDENT a = Student a a a a deriving Show
data LIT t (a :: *) = L {unL :: t} deriving Show
data MAJOR a = English | Math | Physics deriving Show
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR])
$(derive [makeEqF,makeShowF,smartConstructors,makeShowConstr] [''WILD])
instance Render STUDENT
instance Show t => Render (LIT t)
instance Render MAJOR
instance Render WILD
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep
    
i :: (
        Rep (f (LIT Int)),
        Rep (f (LIT Float)),
        Rep (f (LIT String)),
        Rep (f (MAJOR)),
        Rep (f (STUDENT)),
        Rep (f (SIG)),
        PF (f (LIT Int)) :<: PF (f SIG),
        Functor (PF (f (LIT Int))),
        PF (f (LIT String)) :<: PF (f SIG),
        Functor (PF (f (LIT String))),
        PF (f (LIT Float)) :<: PF (f SIG),
        Functor (PF (f (LIT Float))),
        PF (f MAJOR) :<: PF (f SIG),
        Functor (PF (f MAJOR)),
        Functor (PF (f SIG))
        ,STUDENT :<: PF (f SIG)
        ) => f (LIT Int) a -> f ( (LIT String)) a -> f ( (LIT Float)) a ->
                    f (MAJOR) a -> f SIG a
i a b c d = toRep $ inject $ Student (toRep $ deepInject $ fromRep a)
                    (toRep $ deepInject $ fromRep b)
                    (toRep $ deepInject $ fromRep c)
                    (toRep $ deepInject $ fromRep d)
instance (f:<:g,Functor f,Functor g) => Subsume e (WILD :+: f) (WILD :+: g) where
    inj' e (Inr a) = Inr $ inj a
    inj' e (Inl a) = Inl $ inj a
    prj' e (Inr a) = fmap Inr $ proj a
instance (
        (WILD :+: META (LHS f) :+: f) :<: 
        (WILD :+: META (LHS g) :+: g) ,
        f:<:g,Functor f,Functor g) => Subsume e (LHS f) (LHS g) where
    inj' e (LHS a) = LHS $ deepInject a
instance (
        (META (RHS f) :+: f) :<: 
        (META (RHS g) :+: g) ,
        f:<:g,Functor f,Functor g) => Subsume e (RHS f) (RHS g) where
    inj' e (RHS a) = RHS $ deepInject a
instance (f :<: g,MetaRep (LHS g) ~ MetaId,MetaRep (LHS f) ~ MetaId, Functor f,Functor g) =>
        Subsume e ((META (LHS f)) :+: f) ((META (LHS g)) :+: g) where
    inj' e (Inr a) =  Inr $ inj a
    inj' e (Inl (Meta (MVar a))) =  Inl $ Meta $ MVar a
instance (f :<: g,MetaRep (RHS g) ~ MetaId,Functor f,Functor g) =>
        Subsume e ((META (RHS f)) :+: f) ((META (RHS g)) :+: g) where
    inj' e (Inr a) =  Inr $ inj a
    inj' e (Inl (Meta (MVar a))) =  Inl $ Meta $ MVar a
    
    
e3 :: Term SIG
e3 = i (1+1) "jh" 1.2 english
e4 :: LHS SIG a
e4 = i 2 __ 1.2 english
e5 :: MetaRep (RHS (LIT Int)) a -> RHS SIG a
e5 x = i 2 "hi" 1.2 english

english :: (Rep (f g),MAJOR :<: g,MAJOR :<: PF (f g)) => f g a
english = toRep $ iEnglish

instance Functor f => Rep (Cxt NoHole f) where
    type PF (Cxt NoHole f) = f
    toRep = toCxt
    fromRep = fmap (const ())

type SIG = STUDENT :+: MAJOR :+: LIT String :+: LIT Int :+: LIT Float :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.

extract def = maybe def unL . proj . (\(Term m) -> m) . fromRep
instance {-# OVERLAPPING #-} (LIT d :<: PF (r (LIT d)),Rep (r (LIT d)),Num d) => Num (r (LIT d) a) where
    fromInteger =  toRep . iL . (id :: d -> d) . fromInteger
    signum (extract (0::d) -> a) = toRep $ iL (signum a)
    abs (extract (0::d) -> a) = toRep $ iL (abs a)
    (extract (0::d) -> a) + (extract (0::d) -> b) = toRep $ iL $ a + b
    (extract (1::d) -> a) * (extract (1::d) -> b) = toRep $ iL $ a * b
    (extract (0::d) -> a) - (extract (0::d) -> b) = toRep $ iL $ a - b
instance {-# OVERLAPPING #-} (LIT d :<: PF (r (LIT d)),Rep (r (LIT d)),Fractional d) => Fractional (r (LIT d) a) where
    fromRational = toRep . iL . (id :: d -> d ) . fromRational
    recip (extract (0::d) -> a) = toRep $ iL $ recip a
instance {-# OVERLAPPING #-} (LIT d :<: PF (r (LIT d)),Rep (r (LIT d)),IsString d) => IsString (r (LIT d) a) where
    fromString = toRep . iL . (id :: d -> d) . fromString

instance (WILD :<: f) => WildCard (Cxt h f) where
    __ = iWildCard
instance MetaVar (Cxt h (WILD :+: (META (LHS f) :+: f))) where
    type MetaRep (Cxt h (WILD :+: (META (LHS f) :+: f))) = MetaId
    type MetaArg (Cxt h (WILD :+: (META (LHS f) :+: f))) = Var (Cxt h (WILD :+: (META (LHS f) :+: f)))
    metaExp =  Term . Inr . Inl . Meta . go
        where
            go :: MetaExp (Cxt h (WILD :+: (META (LHS f) :+: f))) a -> MetaExp (LHS f) a
            go (MVar r) = MVar r
            go (MApp e (Var a)) = MApp (go e) (Var a)
type instance Var (Cxt h (WILD :+: (META (LHS f) :+: f))) = VAR

instance Functor f => MetaVar (Cxt NoHole (META (RHS f) :+: f)) where
    type MetaRep (Cxt NoHole (META (RHS f) :+: f)) = MetaId
    type MetaArg (Cxt NoHole (META (RHS f) :+: f)) = Cxt NoHole (META (RHS f) :+: f)
    metaExp =  Term . Inl . Meta . go
        where
            go :: Functor f => MetaExp (Cxt NoHole (META (RHS f) :+: f)) a -> MetaExp (RHS f) a
            go (MVar r) = MVar r
            go (MApp e a) = MApp (go e) (RHS $ fmap (const ()) a)
type instance Var (Cxt h (META (RHS f) :+: f)) = VAR

e :: Cxt NoHole SIG a
e = i 1 "hi" 1.2 english
e2 :: Cxt NoHole SIG a
e2 = i 1 "matching" 1.1 iMath
meta' = toRep . meta
student_rule x = iStudent (meta x) "hi" __ __ ==> iStudent (meta x) "matched!" 1.2 iMath
student_rule' :: MetaId Int -> Rule (LHS SIG) (RHS SIG)
student_rule' x = i (meta x) __ __ english ===> i (meta x) "matched!2" 1.2 (meta x)
a ==> b = toRep a ===> toRep b

main = do
    drawTerm e3
    drawTerm (unLHS e4)
    drawTerm $ stripAnn $ applyFirst app [quantify (student_rule' ) ] $ prepare e
    print "hi"
