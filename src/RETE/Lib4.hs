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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module Lib
    ( ) where

import Data.Comp
import Data.Comp.Derive
import Data.Comp.Ops
import Data.Comp.Render
import Data.Comp.TermRewriting (matchRules,matchRule,appRule,reduce,appTRS,parallelStep,parTopStep,Step,Rule)
import Data.Rewriting.Rules
import Data.Rewriting.FirstOrder (bottomUp)
import Data.Rewriting.HigherOrder
import Data.String(IsString(..))
import Data.Maybe(fromMaybe)
import qualified Data.Set as Set
import Data.Map
import Derive1

import Control.Monad (guard,(>=>),(<=<))
import Control.Monad.Reader
import Control.Monad.Writer
import Debug.Trace

data STUDENT a = Student a a a a deriving Show
data MAJOR a = English | Math | Physics deriving Show
newtype LIT b a = L {unL ::b} deriving Show
data NUM a = Plus a a | Minus a a | Times a a | Negate a | Divide a a deriving Show
data LIST a = NIL | CONS a a deriving (Show,Eq,Ord)

--[
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeOrdF,makeShowF,smartConstructors,makeShowConstr] [''STUDENT,''LIT,''MAJOR,''NUM])
$(derive [makeFunctor,makeTraversable,makeFoldable,
          makeEqF,makeOrdF,makeShowF,smartConstructors,makeShowConstr] [''LIST])
$(derive [makeEqF,makeShowF,smartConstructors,makeShowConstr] [''WILD])
$(derive [smartRep] [''STUDENT,''LIT,''MAJOR,''LIST]) 
$(derive [smartRep'] [''STUDENT,''LIT,''MAJOR,''LIST]) 
$(derive [makeOrdF] [''VAR,''LAM,''APP])
 
--]

type SIG = LIST :+: NUM :+: STUDENT :+: MAJOR :+: LIT Int :+: LIT String :+: LIT Float :+: ADDONS
type ADDONS = VAR :+: LAM :+: APP -- Not needed as written, but allow higher order rewrite rules.
newtype Expr f a = Expr {unExpr :: Term f} deriving Functor

-- Restricted smart constructors [
student :: (Rep r,STUDENT :<: PF r) => r Int -> r String -> r Int -> r (MAJOR b) -> r b
student = rStudent

l :: (LIT a :<: PF r, Rep r) => a -> r a
l = rL
s :: (LIT a :<: PF' r, Rep' r) => a -> r a
s = sL
--]

deriving instance Functor (LHS f)
deriving instance Functor (RHS f)

instance (LIT a :<: PF' (r f),Functor (r f),Num a,Rep' (r f)) => Num (r (f :: * -> *) a) where --[
    fromInteger = s . fromInteger
    abs (fromRep' -> a) = s $ fromMaybe 0 $ do 
        a' <- project a
        return $ abs $ unL a'
instance (LIT a :<: PF' (r f),Functor (r f),Fractional a,Rep' (r f)) => Fractional (r (f :: * -> *) a) where
    fromRational = s . fromRational
instance (LIT String :<: PF' (r f),Functor (r f),Rep' (r f)) => IsString (r (f :: * -> *) String) where
    fromString = s . fromString --]
    
type STUFF f = (VAR :<: f,LAM :<: f,APP :<: f,VAR :<: PF (LHS f),LAM :<: PF (LHS f))
matchML :: (Functor f,Foldable f,EqF f,STUFF f) => [LHS f a] -> Term (f :&: Set.Set Name) -> ReaderT AlphaEnv (WriterT (Subst (f :&: Set.Set Name)) Maybe) ()
matchML lhss t = do
    mapM_ (\x -> matchM x t) lhss

matchL :: (Functor f,Foldable f,EqF f, STUFF f) => [LHS f a] -> Term (f :&: Set.Set Name) -> Maybe (Subst (f :&: Set.Set Name))
matchL lhs = solveSubstAlpha <=< execWriterT . flip runReaderT oEmpty . matchML lhs

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
    -> Data.Rewriting.Rules.Rule (LHS' f) (RHS f)
    -> Term g
    -> Maybe (Term g) --]
rewrite' app (Rule lhs'@(LHS' conds lhss) rhs) t = do
    subst <- matchL lhss t
    --trace (showTerm $ unLHS $ head $ lhss) (Just undefined)
    case conds of
        Nothing -> return ()
        Just c -> do
            cont <- unBOOL (unTerm c) subst
            guard cont
    substitute app subst rhs

-- Render and Show and Rep Expr [
instance Render NUM
instance Render LIST
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
    toRep  = LHS'' . (:[]) . LHS
    fromRep = unLHS . head . unLHS'   
--]

data LHS' f a = LHS' { unC :: Maybe (Conditional f), unLHS' :: [LHS f a] } --Term (WILD :+: (META (LHS' f) :+: f))}
pattern LHS'' a = LHS' Nothing a

data BOOL f a = Boolean {unBOOL :: Data.Rewriting.Rules.Subst (f :&: Set.Set Name) -> Maybe Bool}
            | a :&& a
            | Not a
type Conditional f = Term (BOOL f)

--[
guarded a b = LHS' (Just b) a

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
-- ]

{-
ex :: Expr SIG a
ex = student 2 "NOT matched" 2 rEnglish
-}

--student_rule3 :: _ => MetaId Int -> Rule (LHS' f) rhs
student_rule x y= [student (meta x) __ (meta y) rEnglish ] .| 
                                                      meta x .> 0  .&&
                                                      meta y .> meta x
                    ===>
                    student (meta x) "matched!" (meta x) rMath
                  
student_rule2 x y= [student (meta x) __ (meta y) rEnglish
                  ,student 2 __ (meta x) rEnglish] .| meta x .== meta y
                    ===>
                  student (meta x) "matched!" (meta x) rMath
instance Functor f => Rep (Cxt NoHole f) where
    type PF (Cxt NoHole f) = f
    toRep = toCxt
    fromRep r = fmap (const ()) r
f,f2 :: Cxt Hole SIG String
f = iStudent (Hole "num") (Hole "only") (iL (2::Int)) iEnglish
--f = iStudent (Hole "num") (Hole "only") (iL (2::Int)) iEnglish
f2 = iStudent (iL (9::Int)) (iCONS (Hole "only") (Hole "only")) (Hole "num") iEnglish
f3 :: Cxt NoHole SIG ()
f3 = iStudent (iL (5::Int)) (iL ("start"::String)) (iL (2::Int)) iEnglish
g = iL (5 ::Int)
g2 = iL (7 ::Int)
m r cxt conds = do
    (c,mapping) <- matchRule r cxt
    guard $ conds mapping 
    return (c,mapping)
m2 r cxt = do
    (c,mapping) <- matchRule r cxt
    guard $ and $ fmap (\(a@(V t f),_) -> f mapping) $ toList mapping
    return (c,mapping)
g3 = iL (5 ::Int)
g4,g5 :: Cxt Hole (LIT Int) (V Hole (LIT Int) String Int)
g4 = iL (7 ::Int)
g5 = iL (7 ::Int)
--g5 = v "num" (< iL (5::Int))
data V h f v a = V v (Map (V h f v a) (Cxt h f a) -> Bool)   
pattern Stud a b c d <- Term (proj -> Just ((Student a b c d)))
_s,_id :: (SIG :<: f,STUDENT :<: f,Functor f) => Cxt h f a -> Cxt h f a -> Cxt h f a
Stud _ b c d `_id` (deepProject -> Just (a:: Cxt h SIG a)) = iStudent (prep a) (prep b) (prep c) (prep d)
Stud _ b c d `_s` (deepProject  -> Just (a:: Cxt h SIG a)) = iStudent (prep a) (prep b) (prep c) (prep d)
-- _s :: LHS' SIG a -> LHS' SIG a -> LHS' SIG a
prep = deepInject
data Expr2 h f a b = Expr2 {unExpr2 :: Cxt h f a} deriving Show

data Hole2 h f a = H String [([Ordering],Cxt h f (Hole2 h f a))] | Wild
instance Eq (Hole2 h f a) where
    H a _ == H b _ = a == b
instance Ord (Hole2 h f a) where
    H a _ `compare` H b _ = a `compare` b
instance (ShowF f,Functor f) => Show (Hole2 h f a) where show (H s b) = "Hole2 " ++ show s ++ " " ++ show b
--type LHS2 h f a b = LHS2 {unLHS2 :: Cxt h f (Hole2 h f a)} deriving Show
newtype LHS2 h a f b = LHS2 {unLHS2 :: Cxt h f (Hole2 h f a)} deriving (Show,Functor)

sstudent :: (STUDENT :<: PF' r,Rep' r) => r Int -> r String -> r Int -> r (MAJOR a) -> r a
sstudent = sStudent
lhs2 :: LHS2 Hole a SIG b
lhs2 = sstudent ("id" ..< 3) ("s" ..= "hi") __ __
(==>) :: 
    LHS2 Hole a f b -> LHS2 Hole a g b ->
    (Context f (Hole2 Hole f a)
    ,Context g (Hole2 Hole g a))
LHS2 a ==> LHS2 b = (a,b)

v a func term = LHS2 $ Hole (H a [(func,term)])
h a = LHS2 $ Hole (H a [])
(..<),(..=),(..>),(..!=) :: (Functor f,Traversable f) => String -> LHS2 Hole a f b -> LHS2 Hole a f b
a ..< b = v a [LT] $ c b
c b = maybe (error "undefined coerce") id $ deepProject $ fromRep' b
a ..= b = v a [EQ] $ c b
a ..> b = v a [GT] $ c b
a ..!= b = v a [LT,GT] $ c b
instance WildCard (LHS2 Hole a f) where
    __ = LHS2 $ Hole $ Wild
instance Functor f => Rep' (Cxt NoHole f) where
    type PF' (Cxt NoHole f) = f
    type PHOLE' (Cxt NoHole f) = ()
    type PHOLE'' (Cxt NoHole f) = NoHole
    toRep'  = toCxt
    fromRep' = fmap (const ())

instance (Functor f) => Rep' (LHS2 h a f)
  where
    type PF' (LHS2 h a f) = f
    type PHOLE' (LHS2 h a f) = Hole2 h f a
    type PHOLE'' (LHS2 h a f) = h
    toRep'  = LHS2
    fromRep' = unLHS2

instance Rep' (LHS f)
  where
    type PF' (LHS f) = (WILD :+: META (LHS f) :+: f)
    type PHOLE' (LHS f) = ()
    type PHOLE'' (LHS f) = NoHole
    toRep'   = LHS
    fromRep' = unLHS

instance Rep' (RHS f)
  where
    type PF' (RHS f) = (META (RHS f) :+: f)
    type PHOLE' (RHS f) = ()
    type PHOLE'' (RHS f) = NoHole
    toRep'   = RHS
    fromRep' = unRHS
    
type HoledCxt h f a = Cxt h f (Hole2 h f a)

example = sstudent ("x" ..< 2) "hi" ("y" ..!= h "x") sMath ==> sstudent (h "y") "MATCHED" (h "x") sEnglish
main = do
    --drawTerm $ reduce (parallelStep [(g,g2),(f,f2)]) f3
    --putStrLn $ show $ ( d4 :: Expr2 Hole SIG (V Hole SIG String (Cxt Hole L2 )) b)
    --putStrLn $ show $ m2 (g5,g4) g3
    mapM_ drawTerm $ appRule' example $ (sstudent 1 "hi" 0 sMath :: Term SIG)
    {-
    putStrLn $ show $ m (f,f2) f3 (\mp -> mp ! "num" < iL (6 :: Int))
    let e = unExpr ex
    drawTerm $ rewriteWith (reduce $ rewrite' app $ quantify student_rule) e
    drawTerm $ rewriteWith (reduce $ rewrite' app $ quantify student_rule2) e
    -}
appRule' :: (Ord a,OrdF f,Show a,ShowF f,v ~ Hole2 Hole f a,Ord v, EqF f, Eq a, Functor f, Foldable f)
          => Data.Comp.TermRewriting.Rule f f v -> Step (Cxt h f a)
appRule' rule t = do
    (res, subst) <- matchRule rule t
    trace (concatMap (\(a,b) -> show a ++ "::::" ++ show b) $ toList subst) (Just undefined)
    let x = concatMap (\(H v conds,b) ->
                    fmap (\(ords,cond) -> 
                    elem (compare b (substHoles' cond subst)) ords ) conds) $ toList subst
    trace (show x) $ return ()
    if and x then 
        return $ substHoles' res subst
    else
        return t
