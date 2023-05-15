module STLC where

import Unbound.Generics.LocallyNameless
    ( string2Name,
      aeq,
      bind,
      lunbind,
      unbind,
      Alpha,
      Bind,
      Embed(..),
      Name,
      Subst(isvar, subst, substs),
      SubstName(SubstName) )

import Data.Char

import Control.Monad.Trans.Except ( throwE )
import qualified Data.List as List
import qualified Text.PrettyPrint as PP

import Util hiding (Prim)


------------------------------------------------------
-- The Simply Typed λ-calculus with extensions
------------------------------------------------------

type TmName = Name Tm

data Ty = TyBool
        | TyNat
        | TyArr !Ty !Ty
        | TyProd ![Ty]
   deriving (Show, Generic)

data Tm = TmZero
        | TmSucc !Tm
        | TmIsZero !Tm
        | TmPred !Tm
        | TmTrue
        | TmFalse
        | TmVar !TmName
        | TmLam !(Bind (TmName, Embed Ty) Tm)
        | TmApp !Tm !Tm
        | TmProd ![Tm]
        | TmPrj !Tm !Int
        | TmIf !Tm !Tm !Tm
        | TmAnn !Tm !Ty
   deriving (Show, Generic)

------------------------------------------------------
-- Use unbound-generics to derive substitution, alpha-equivalence
-- and free variable functions
------------------------------------------------------

instance Alpha Tm 
instance Alpha Ty 

instance Subst Tm Ty
instance Subst Ty Tm
instance Subst Ty Ty
instance Subst Tm Tm where
  isvar (TmVar x) = Just (SubstName x)
  isvar _  = Nothing
  
instance Eq Ty where
  (==) = aeq
instance Eq Tm where
  (==) = aeq
  
------------------------------------------------------
-- Example terms
------------------------------------------------------

x :: Name Tm
y :: Name Tm
z :: Name Tm
(x, y, z) = (string2Name "x", string2Name "y", string2Name "z")

natid :: Tm
natid = TmLam (bind (x, Embed TyNat) (TmVar x))


two :: Tm
two = TmSucc (TmSucc TmZero)
                          

-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------
type Gamma = [ (TmName, Ty) ]

newtype Ctx = Ctx { getGamma :: Gamma }
emptyCtx :: Ctx
emptyCtx = Ctx {  getGamma = [] }

lookupVar :: Ctx -> TmName -> M Ty
lookupVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwE "NotFound"

extendTm :: TmName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : getGamma ctx }


typecheck :: Ctx -> Tm -> M Tm
typecheck g e@(TmVar x) = do 
  ty <- lookupVar g x
  return $ TmAnn e ty
typecheck g TmZero = return $ TmAnn TmZero TyNat
typecheck g (TmSucc nv) = do
  ae1 <- typecheck g nv
  case ae1 of
    e1@(TmAnn _ TyNat) -> return $ TmAnn (TmSucc e1) TyNat
    _ -> throwE "Not a nat"
typecheck g (TmPred nv) = do
  ae1 <- typecheck g nv 
  case ae1 of
    e1@(TmAnn _ TyNat) -> return $ TmAnn (TmPred e1) TyNat
    _ -> throwE "Not a nat"
typecheck g (TmIsZero nv) = do
  ae1 <- typecheck g nv 
  case ae1 of
    e1@(TmAnn _ TyNat) -> return $ TmAnn (TmIsZero e1) TyBool
    _ -> throwE "Not a nat"
typecheck g TmTrue = return $ TmAnn TmTrue TyBool
typecheck g TmFalse = return $ TmAnn TmFalse TyBool
typecheck g (TmLam bnd) = do
  ((x, Embed ty1), e1) <- unbind bnd
  ae1 <- typecheck (extendTm x ty1 g) e1
  case ae1 of 
    (TmAnn _ ty2') ->
        return $ TmAnn 
           (TmLam (bind (x, Embed ty1) ae1))
           (TyArr ty1 ty2')
    _ -> throwE "Annotated expression expected"
typecheck g e@(TmApp e1 e2) = do
  ae1 <- typecheck g e1
  ae2 <- typecheck g e2
  case (ae1, ae2) of 
    (TmAnn _ ty1, TmAnn _ ty2) ->
      case ty1 of
        TyArr ty11 ty21 | ty2 `aeq` ty11 ->
          return (TmAnn (TmApp ae1 ae2) ty21)
        _ -> throwE "TypeError"
    _ -> throwE "Annotated expression epxected"
typecheck g (TmProd es) = do 
  atys <- mapM (typecheck g) es
  let tys = map (\(TmAnn _ ty) -> ty) atys
  return $ TmAnn (TmProd atys) (TyProd tys)
typecheck g (TmPrj e i) = do
  ae <- typecheck g e
  case ae of 
    (TmAnn _ ty) -> 
      case ty of 
        TyProd tys | i < length tys -> return $ TmAnn (TmPrj ae i) (tys !! i)
        _ -> throwE "TypeError"
typecheck g (TmIf e0 e1 e2) = do
  ae0 <- typecheck g e0
  ae1 <- typecheck g e1
  ae2 <- typecheck g e2
  case (ae0, ae1, ae2) of 
    (TmAnn _ ty0, TmAnn _ ty1, TmAnn _ ty2) ->
      if ty1 `aeq` ty2 && ty0 `aeq` TyBool then 
        return (TmAnn (TmIf ae0 ae1 ae2) ty1)
      else   
        throwE "TypeError"
    _ -> throwE "Annotated Expressions expected"
typecheck g _ = throwE "TypeError"
-----------------------------------------------------------------
-- Small-step semantics
-----------------------------------------------------------------

natval :: Tm -> Bool
natval TmZero = True
natval (TmSucc nv) = natval nv
natval _ = False

value :: Tm -> Bool
value TmTrue      = True
value TmFalse     = True
value (TmLam _)   = True
value (TmProd es) = all value es
value v           = natval v

steps :: [Tm] -> M [Tm]
steps [] = throwE "can't step empty list"
steps (e:es) | value e = do
  es' <- steps es
  return (e : es')
steps (e:es) = do 
  e'  <- step e
  return (e' : es)
  
step :: Tm -> M Tm
step e | value e = throwE "can't step value"
step (TmVar _)   = throwE "unbound variable" 
step (TmSucc e1) = do
  e1' <- step e1
  return $ TmSucc e1'
step (TmPred e2@(TmSucc e1)) | natval e2 = return e1
step (TmPred e1) = do
  e1' <- step e1
  return $ TmPred e1'
step (TmIsZero TmZero) = return TmTrue
step (TmIsZero v2) | natval v2 = return TmFalse
step (TmIsZero e1) = do
  e1' <- step e1
  return $ TmIsZero e1'
step (TmApp e1@(TmLam bnd) e2) = 
  if value e2 
  then do
    ((x, _), t) <- unbind bnd
    return $ substs [ (x, e2) ] t
  else do          
    e2' <- step e2
    return (TmApp e1 e2') 
step (TmApp e1 e2) = do
  e1' <- step e1
  return (TmApp e1' e2)
step (TmPrj e1@(TmProd es) i) | value e1 && i < length es = return $ es !! i
step (TmPrj e1 i) = do 
  e1' <- step e1
  return (TmPrj e1' i) 
step (TmProd es) = do
  es' <- steps es
  return (TmProd es')
step (TmIf TmTrue e1 _) = return e1
step (TmIf TmFalse _ e2) = return e2
step (TmIf e0 e1 e2) = do 
  e0' <- step e0
  return (TmIf e0' e1 e2)
step (TmAnn e ty) = return e
step _ = throwE "Doesn't step"
  
evaluate :: Tm -> M Tm
evaluate e = if value e then return e else do
  e' <- step e
  evaluate e'
  
-----------------------------------------------------------------
-- Pretty-printer
-----------------------------------------------------------------

instance Display Ty where
  display TyNat       = return $ text "Nat"
  display TyBool      = return $ text "Bool"
  display (TyArr ty1 ty2) = do  
    d1 <- withPrec (precedence "->" + 1) $ display ty1
    d2 <- withPrec (precedence "->")     $ display ty2
    binop d1 "->" d2
  display (TyProd tys) = displayTuple tys
    
instance Display Tm where
  display TmZero = return $ text "0"
  display (TmSucc nv) = do 
    dn <- display nv
    prefix "Succ" dn
  display (TmPred nv) = do
    dn <- display nv
    prefix "Pred" dn
  display (TmIsZero nv) = do
    dn <- display nv
    prefix "IsZero" dn
  display TmTrue = return $ text "true"
  display TmFalse = return $ text "false"
  display (TmVar n) = display n
  display (TmLam bnd) = lunbind bnd $ \((x, Embed ty), e) -> do
    dx <- display x      
    dt <- display ty
    de <- display e
    prefix "λ" (dx <+> colon PP.<> dt PP.<> text "." <+> de)
      -- else prefix "\\"  (arg PP.<> text "." <+> de)
  display (TmApp e1 e2) = do
    d1 <- withPrec (precedence " ") $ display e1
    d2 <- withPrec (precedence " " + 1) $ display e2
    binop d1 " " d2
  display (TmProd es) = displayTuple es

  display (TmPrj e i) = do
    de <- display e 
    return $ text "Pi" PP.<> int i <+> de
  display (TmIf e0 e1 e2) = do
    d0 <- display e0
    d1 <- display e1
    d2 <- display e2
    prefix "if" $ sep [d0 , text "then" <+> d1 , text "else" <+> d2]
  display (TmAnn e ty) = do
    de <- display e
    dt <- display ty
    binop de ":" dt 

-- Parser

data Token = LParen | RParen | TokDot | TokLam | TokVar !TmName | TokIf | TokThen | TokElse |
  TokZero | TokSucc | TokPred | TokIsZero | TokColon | TokBool | TokNat | TokArrow | TokTrue | TokFalse deriving (Show)

nextToken :: String -> Maybe (Token, String)
nextToken [] = Nothing
nextToken ('(':tl) = Just (LParen, tl)
nextToken (')':tl) = Just (RParen, tl)
nextToken ('.':tl) = Just (TokDot, tl)
nextToken ('&':tl) = Just (TokLam, tl)
nextToken (c:tl) | isLower c =
  let (str, rest) = exhaustVar (c:tl) in Just (TokVar . string2Name $ str, rest)
nextToken ('I':'f':tl) = Just (TokIf, tl)
nextToken ('T':'h':'e':'n':tl) = Just (TokThen, tl)
nextToken ('E':'l':'s':'e':tl) = Just (TokElse, tl)
nextToken ('0':tl) = Just (TokZero, tl)
nextToken ('S':'u':'c':'c':tl) = Just (TokSucc, tl)
nextToken ('P':'r':'e':'d':tl) = Just (TokPred, tl)
nextToken ('I':'s':'Z':'e':'r':'o':tl) = Just (TokIsZero, tl)
nextToken (':':tl) = Just (TokColon, tl)
nextToken ('B':'o':'o':'l':tl) = Just (TokBool, tl)
nextToken ('N':'a':'t':tl) = Just (TokNat, tl)
nextToken ('-':'>':tl) = Just (TokArrow, tl)
nextToken ('T':'r':'u':'e':tl) = Just (TokTrue, tl)
nextToken ('F':'a':'l':'s':'e':tl) = Just (TokFalse, tl)
nextToken (' ':tl) = nextToken tl
nextToken ('\t':tl) = nextToken tl
nextToken ('\n':tl) = nextToken tl
nextToken _ = Nothing

exhaustVar :: String -> (String, String)
exhaustVar [] = ("", [])
exhaustVar (c:tl) | isAlphaNum c =
  let (str, rest) = exhaustVar tl in (c:str, rest)
exhaustVar cs = ("", cs)

scan :: String -> [Token]
scan [] = []
scan cs =
  case nextToken cs of
    Just (tok, rest) -> tok : scan rest
    Nothing -> []

nextTerm :: [Token] -> Maybe (Tm, [Token])
nextTerm [] = Nothing
nextTerm (TokZero:tl) = Just (TmZero, tl)
nextTerm (TokTrue:tl) = Just (TmTrue, tl)
nextTerm (TokFalse:tl) = Just (TmFalse,tl)
nextTerm (TokVar v:tl) = Just (TmVar v, tl)
nextTerm (TokLam:tl) = case nextLam tl of
  Just (lam, rest) -> Just (lam, rest)
  Nothing -> Nothing
nextTerm (LParen:tl) = case nextApp tl of
  Just (app, rest) -> Just (app, rest)
  Nothing -> Nothing
nextTerm (TokIf:tl) = case nextIf tl of
  Just (ifTerm, rest) -> Just (ifTerm, rest)
  Nothing -> Nothing
nextTerm (TokSucc:tl) = case nextUnaryArg tl TmSucc of
  Just (term, rest) -> Just (term, rest)
  Nothing -> Nothing
nextTerm (TokPred:tl) = case nextUnaryArg tl TmPred of
  Just (term, rest) -> Just (term, rest)
  Nothing -> Nothing
nextTerm (TokIsZero:tl) = case nextUnaryArg tl TmIsZero of
  Just (term, rest) -> Just (term, rest)
  Nothing -> Nothing
nextTerm _ = Nothing

nextLam :: [Token] -> Maybe (Tm, [Token])
nextLam (TokVar v:TokColon:tl) = case nextTyp tl of
  Just (typ, TokDot:rest) -> case nextTerm rest of
    Just (body, rest') -> Just (TmLam (bind (v, Embed typ) body), rest')
    Nothing -> Nothing
  _ -> Nothing
nextLam _ = Nothing

nextApp :: [Token] -> Maybe (Tm, [Token])
nextApp ts = case nextTerm ts of
  Just (func, RParen:LParen:rest) -> case nextTerm rest of
    Just (input, RParen:rest') -> Just (TmApp func input, rest')
    _ -> Nothing
  _ -> Nothing

nextIf :: [Token] -> Maybe (Tm, [Token])
nextIf ts = case nextTerm ts of
  Just (cond, TokThen:tl) -> case nextTerm tl of 
    Just (ifTrue, TokElse:tl') -> case nextTerm tl' of
      Just (ifFalse, rest) -> Just (TmIf cond ifTrue ifFalse, rest)
      _ -> Nothing
    _ -> Nothing
  _ -> Nothing

  
nextUnaryArg :: [Token] -> (Tm -> Tm) -> Maybe (Tm, [Token])
nextUnaryArg ts constructor = case nextTerm ts of
  Just (term, rest) -> Just (constructor term, rest)
  Nothing -> Nothing

nextTyp :: [Token] -> Maybe (Ty, [Token])
nextTyp (LParen:tl) =
  case nextTyp tl of
    Just (left@(TyArr _ _), RParen:TokArrow:rest) -> case nextTyp rest of
      Just (right, tl') -> Just (TyArr left right, tl')
      _ -> Nothing
    _ -> Nothing
nextTyp (TokBool:TokArrow:tl) =
  let Just (right, tl') = nextTyp tl in
    Just (TyArr TyBool right, tl')
nextTyp (TokBool:tl) = Just (TyBool, tl)
nextTyp (TokNat:TokArrow:tl) =
  let Just (right, tl') = nextTyp tl in
    Just (TyArr TyNat right, tl')
nextTyp (TokNat:tl) = Just (TyNat, tl)
nextTyp _ = Nothing
  

parse :: [Token] -> Tm
parse tokens = case nextTerm tokens of
  Just (term, []) -> term
  _ -> error "Could not parse code!"


interpret :: String -> Tm
interpret = parse . scan