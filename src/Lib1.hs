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
type SIG = STUDENT :+: MAJOR :+: LIT String :+: LIT Int :+: LIT Float :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.

instance (LIT Int :<: f) => Num (Term f) where
    fromInteger = inject . L . (id :: Int -> Int) . fromInteger

class St f where
    st :: f Int -> f String -> f Float -> f (MAJOR a) ->f a
instance St (LHS SIG) where
    st (LHS a) (LHS b) (LHS c) (LHS d) = LHS $ iStudent a b c d
instance St (RHS SIG) where
    st (RHS a) (RHS b) (RHS c) (RHS d) = RHS $ iStudent a b c d
instance St (Cxt NoHole SIG) where
    st a b c d = iStudent (inj a) (inj b) (inj c) (_ d)
main = do
    --drawTerm e3
    --drawTerm (unLHS e4)
    --drawTerm $ stripAnn $ applyFirst app [quantify (student_rule' ) ] $ prepare e3
    print "hi"
    

