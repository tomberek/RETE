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
{-
instance (MetaRep f ~ MetaId) => Render (META f)
instance (MetaRep f ~ MetaId) => ShowConstr (META f) where
    showConstr (Meta (MVar (MetaId rep))) = show rep
i :: forall h f a g. (Functor f,LIT Int :<: Cxt h g,LIT String :<: Cxt h g,LIT Float :<: Cxt h g
    ,MAJOR :<: Cxt h g,STUDENT :<: g,f :<: g) =>
     f (LIT Int ( a)) -> f (LIT String ( a))
    -> f (LIT Float ( a)) -> f (MAJOR ( a)) -> Cxt h g a
--i a b c d = iStudent (e a) (e b) (e c) (f d)
    where
        e :: (LIT d :<: Cxt h g,Functor f) =>f (LIT d a) -> Cxt h g a
        e e2 = inject $ fmap (inj) e2 
        f :: (MAJOR :<: Cxt h g,Functor f) => f (MAJOR ( a)) -> Cxt h g a
        f e2 = inject $ fmap (inj) e2
-- g can be LHS f or Cxt NoHole f,  where f is Term (LIT Int)
    ---}
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
    prj' e (Inr a) = fmap Inr $ proj a
instance (f :<: g,MetaRep x ~ MetaId,MetaRep y ~ MetaId,Functor f,Functor g) => Subsume e ((META x) :+: f) ((META y) :+: g) where
    inj' e (Inr a) =  Inr $ inj a
    prj' e (Inr a) = fmap Inr $ proj a
    
e3 :: Term SIG
e3 = i (1+1) "jh" 1.2 english
e4 :: LHS SIG a
e4 = i 2 __ 1.2 english

english :: (Rep (f g),MAJOR :<: g,MAJOR :<: PF (f g)) => f g a
english = toRep $ iEnglish

instance Functor f => Rep (Cxt NoHole f) where
    type PF (Cxt NoHole f) = f
    toRep = toCxt
    fromRep = fmap (const ())
    {-
instance Num a => Num (Term (LIT a)) where
    fromInteger = Term . L . fromInteger
instance Fractional a => Fractional (Term (LIT a)) where
    fromRational = Term . L . fromRational
instance IsString (Term (LIT String)) where
    fromString = Term . L . fromString
    ---}

type SIG = MAJOR :+: STUDENT :+: LIT String :+: LIT Int :+: LIT Float :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.

instance {-# OVERLAPPING #-} (LIT d :<: PF (r (LIT d)),Rep (r (LIT d)),Num d) => Num (r (LIT d) a) where
    fromInteger =  toRep . iL . (id :: d -> d) . fromInteger
instance {-# OVERLAPPING #-} (LIT d :<: PF (r (LIT d)),Rep (r (LIT d)),Fractional d) => Fractional (r (LIT d) a) where
    fromRational = toRep . iL . (id :: d -> d ) . fromRational
instance {-# OVERLAPPING #-} (LIT d :<: PF (r (LIT d)),Rep (r (LIT d)),IsString d) => IsString (r (LIT d) a) where
    fromString = toRep . iL . (id :: d -> d) . fromString
{-
instance {-# OVERLAPPING #-} (Num d) => Num (Cxt h (LIT d) a) where
    fromInteger = iL . (id :: d -> d) . fromInteger
    abs (extract (0::d) -> a) = iL (abs a)
    signum (extract (0::d) -> a) = iL (signum a)
    (extract (0::Int) -> a) + (extract (0::Int) -> b) = iL $ a + b
    (extract (0::Int) -> a) * (extract (0::Int) -> b) = iL $ a * b
    (extract (0::Int) -> a) - (extract (0::Int) -> b) = iL $ a - b
--instance {-# OVERLAPPING #-} (LIT Float :<: f,LIT Int :<: f) => Fractional (Cxt h f b) where
instance {-# OVERLAPPING #-} Fractional (Cxt h (LIT Float) b) where
    fromRational = iL . (id :: Float -> Float) . fromRational
    recip (extract (0::Float) -> a) = iL $ recip a
instance (LIT String :<: f) => IsString (Cxt h f b) where
    fromString = iL . (id :: String -> String) . fromString
    ---}

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

{-
e :: Cxt h SIG a
e = iStudent 1 "hi" 1.2 iEnglish
e2 :: Cxt h SIG a
e2 = iStudent 1 "matching" 1.1 iMath
---}

student_rule x = iStudent (meta x) "hi" 1.2 __ ==> iStudent (meta x) "matched!" (meta x) iMath
a ==> b = toRep a ===> toRep b

main = do
    -- drawTerm e3
    --drawTerm $ stripAnn $ applyFirst app [quantify (student_rule)] $ prepare e
    print "hi"
