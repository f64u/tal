module C where

import Unbound.Generics.LocallyNameless hiding (prec,empty,Data,Refl,Val)
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Unbound.Generics.LocallyNameless.Alpha

import Control.Monad
import Control.Monad.Except

import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map


import Util
import Text.PrettyPrint as PP


------------------
-- should move to Unbound.LocallyNameless.Ops
-- patUnbind :: (Alpha p, Alpha t) => p -> Bind p t -> t
-- patUnbind p (B _ t) = openT p t
------------------


-- System C

type TyName = Name Ty
type TmName = Name Tm
type ValName = Name Val

data Ty = TyVar TyName
        | TyInt
        | All (Bind [TyName] [Ty])
        | TyProd [Ty]
        | Exists (Bind TyName Ty) -- new
   deriving (Show, Generic)

data Val = TmInt Int
        | TmVar ValName
        | Fix (Bind (ValName, [TyName]) (Bind [(ValName, Embed Ty)] Tm))
        | TmProd [AnnVal]
        | TApp AnnVal Ty  -- new
        | Pack Ty AnnVal  -- new
   deriving (Show, Generic)
            
data AnnVal = Ann Val Ty
   deriving (Show, Generic)
            
data Decl   = 
    DeclVar     ValName (Embed AnnVal)
  | DeclPrj Int ValName (Embed AnnVal)
  | DeclPrim    ValName (Embed (AnnVal, Prim, AnnVal))
  | DeclUnpack  TyName ValName (Embed AnnVal)  -- new
    deriving (Show, Generic)
             
data Tm = Let (Bind Decl Tm)
  | App   AnnVal [AnnVal]  -- updated
  | TmIf0 AnnVal Tm Tm
  | Halt  Ty AnnVal    
   deriving (Show, Generic)

-- For H

newtype Heap = Heap (Map ValName AnnVal) 
  deriving (Show, Semigroup, Monoid)


------------------------------------------------------
instance Alpha Ty 
instance Alpha Val 
instance Alpha AnnVal
instance Alpha Decl
instance Alpha Tm

instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Ty Prim
instance Subst Ty Tm
instance Subst Ty AnnVal
instance Subst Ty Decl
instance Subst Ty Val


instance Subst Val Prim
instance Subst Val Ty
instance Subst Val AnnVal
instance Subst Val Decl
instance Subst Val Tm
instance Subst Val Val where
  isvar (TmVar x) = Just (SubstName x)
  isvar _  = Nothing
  
------------------------------------------------------
-- Helper functions
------------------------------------------------------

mkTyApp :: (MonadError String m, Fresh m) => AnnVal -> [Ty] -> m AnnVal
mkTyApp av [] = return av
mkTyApp av@(Ann _ (All bnd)) (ty:tys) = do
    (as, atys) <- unbind bnd               
    case as of 
      a:as' -> 
        let atys' = subst a ty atys in
        mkTyApp (Ann (TApp av ty) (All (bind as' atys'))) tys
      _ -> throwError "type error: not a polymorphic All"
mkTyApp (Ann _ ty) _ = throwError "type error: not an All"

mkProd :: [AnnVal] -> AnnVal
mkProd vs = Ann (TmProd vs) (TyProd tys) where
   tys = map (\(Ann _ ty) -> ty) vs                

-----------------------------------------------------------------
-- Free variables, with types
-----------------------------------------------------------------

x :: Name Tm
y :: Name Tm
z :: Name Tm
(x,y,z) = (string2Name "x", string2Name "y", string2Name "z")

a :: Name Ty
b :: Name Ty
c :: Name Ty
(a,b,c) = (string2Name "a", string2Name "b", string2Name "c")

-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------
type Delta = [ TyName ]
type Gamma = [ (ValName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
emptyCtx = Ctx { getDelta = [], getGamma = [] }

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do
    if v `List.elem` getDelta g then
      return ()
    else
      throwError $ "Type variable not found " ++ show v

lookupTmVar :: Ctx -> ValName -> M Ty
lookupTmVar g v = do
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwError $ "Term variable notFound " ++ show v

extendTy :: TyName -> Ctx -> Ctx
extendTy n ctx = ctx { getDelta =  n : getDelta ctx }

extendTys :: [TyName] -> Ctx -> Ctx
extendTys ns ctx = foldr extendTy ctx ns

extendTm :: ValName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : getGamma ctx }

extendTms :: [ValName] -> [Ty] -> Ctx -> Ctx
extendTms [] [] ctx = ctx
extendTms (n:ns) (ty:tys) ctx = extendTm n ty (extendTms ns tys ctx)

extendDecl :: Decl -> Ctx -> Ctx
extendDecl (DeclVar x (Embed (Ann _ ty))) = extendTm x ty
extendDecl (DeclPrj i x (Embed (Ann _ (TyProd tys)))) = extendTm x (tys !! i)                                           
extendDecl (DeclPrim x  _) = extendTm x TyInt
extendDecl (DeclUnpack b x (Embed (Ann _ (Exists bnd)))) = 
  extendTy b . extendTm x (patUnbind b bnd)
    


tcty :: Ctx -> Ty -> M ()
tcty g  (TyVar x) =
   checkTyVar g x
tcty g  (All b) = do
   (xs, tys) <- unbind b
   let g' = extendTys xs g -- XX
   mapM_ (tcty g') tys
tcty g TyInt =  return ()
tcty g (TyProd tys) = do
   mapM_ (tcty g) tys
tcty g (Exists b) = do 
  (a, ty) <- unbind b
  tcty (extendTy a g) ty


typecheckVal :: Ctx -> Val -> M Ty
typecheckVal g (TmVar x) = lookupTmVar g x
typecheckVal g (Fix bnd) = do
  ((f, as), bnd2) <- unbind bnd
  (xtys, e)       <- unbind bnd2
  let g' = extendTys as g
  let (xs,tys) = unzip $ map (\(x,Embed y) -> (x,y)) xtys      
  mapM_ (tcty g') tys
  let fty = All (bind as tys)
  typecheck (extendTm f fty (extendTms xs tys g')) e
  return fty
typecheckVal g (TmProd es) = do 
  tys <- mapM (typecheckAnnVal g) es
  return $ TyProd tys
typecheckVal g (TmInt i)    = return TyInt
typecheckVal g (TApp av ty) = do
  tcty g ty
  ty' <- typecheckAnnVal g av
  case ty' of 
    All bnd -> do 
      (as, bs) <- unbind bnd
      case as of 
        [] -> throwError "can't instantiate non-polymorphic function"
        (a:as') -> do
          let bs' = subst a ty bs
          return (All (bind as' bs'))

typecheckAnnVal g (Ann (Pack ty1 av) ty) = do
  case ty of 
    Exists bnd -> do 
      (a, ty2) <- unbind bnd
      tcty g ty1
      ty' <- typecheckAnnVal g av
      if not (ty' `aeq` subst a ty1 ty2) 
         then throwError "type error"
         else return ty     
typecheckAnnVal g (Ann v ty) = do  
  tcty g ty
  ty' <- typecheckVal g v 
  if ty `aeq` ty'
     then return ty
     else throwError $ "wrong annotation on: " ++ pp v ++ "\nInferred: " ++ pp ty ++ "\nAnnotated: " ++ pp ty' 

typecheckDecl g (DeclVar x (Embed av)) = do
  ty <- typecheckAnnVal g av
  return $ extendTm x ty g
typecheckDecl g (DeclPrj i x (Embed av)) = do
  ty <- typecheckAnnVal g av
  case ty of 
    TyProd tys | i < length tys -> 
      return $ extendTm x (tys !! i) g
    _ -> throwError "cannot project"
typecheckDecl g (DeclPrim x (Embed (av1, _, av2))) = do
  ty1 <- typecheckAnnVal g av1
  ty2 <- typecheckAnnVal g av2
  case (ty1 , ty2) of 
    (TyInt, TyInt) -> return $ extendTm x TyInt g
    _ -> throwError "TypeError"
typecheckDecl g (DeclUnpack a x (Embed av)) = do
  tya <- typecheckAnnVal g av
  case tya of 
    Exists bnd -> do 
      let ty = patUnbind a bnd 
      return $ extendTy a (extendTm x ty g)
    _ -> throwError "TypeError"
                 
typecheck :: Ctx -> Tm -> M ()
typecheck g (Let bnd) = do
  (d,e) <- unbind bnd
  g' <- typecheckDecl g d
  typecheck g' e
typecheck g (App av es) = do
  ty <- typecheckAnnVal g av
  case ty of
   (All bnd) -> do
     (as, argtys) <- unbind bnd
     argtys' <- mapM (typecheckAnnVal g) es
     if not (null as)
       then throwError "must use type application"
       else 
         if length argtys /= length argtys'
           then throwError "incorrect args"
           else unless (and (zipWith aeq argtys argtys')) $  
              throwError "arg mismatch"
              
typecheck g (TmIf0 av e1 e2) = do
  ty0 <- typecheckAnnVal g av
  typecheck g e1
  typecheck g e2
  if ty0 `aeq` TyInt then 
    return ()
  else   
    throwError "TypeError"
typecheck g (Halt ty av) = do
  ty' <- typecheckAnnVal g av
  unless (ty `aeq` ty') $
    throwError "type error"

-----------------------------------------------------------------

heapvalcheck g ann@(Ann (Fix bnd) _) = 
  typecheckAnnVal g ann
heapvalcheck g (Ann _ _) = 
  throwError "type error: only code in heap"
  
hoistcheck (tm, Heap m) = do
  let g' = 
        Map.foldlWithKey (\ctx x (Ann _ ty) -> extendTm x ty ctx) 
        emptyCtx m
  mapM_ (heapvalcheck g') (Map.elems m)
  typecheck g' tm
  
-----------------------------------------------------------------
-- Small-step semantics
-----------------------------------------------------------------
  
mkSubst :: Decl -> M (Tm -> Tm)
mkSubst (DeclVar   x (Embed (Ann v _))) = return $ subst x v
mkSubst (DeclPrj i x (Embed (Ann (TmProd avs) _))) | i < length avs =
       let Ann vi _ = avs !! i in return $ subst x vi
mkSubst (DeclPrim  x (Embed (Ann (TmInt i1) _, p, Ann (TmInt i2) _))) = 
       let v = TmInt (evalPrim p i1 i2) in
       return $ subst x v
mkSubst (DeclUnpack a x (Embed (Ann (Pack ty (Ann u _)) _))) = 
  return $ subst a ty . subst x u
mkSubst (DeclPrj i x (Embed av)) = 
  throwError $ "invalid prj " ++ pp i ++ ": " ++ pp av
mkSubst (DeclUnpack a x (Embed av)) = 
  throwError $ "invalid unpack:" ++ pp av



step :: Tm -> M Tm

step (Let bnd) = do
  (d, e) <- unbind bnd
  ss <- mkSubst d
  return $ ss e
      
step (App (Ann e1@(Fix bnd) _) avs) = do
    ((f, as), bnd2) <- unbind bnd
    (xtys, e) <- unbind bnd2
    let us = map (\(Ann u _) -> u) avs
    let xs = map fst xtys
    return $ substs ((f,e1):zip xs us) e

step (TmIf0 (Ann (TmInt i) _) e1 e2) = if i==0 then return e1 else return e2

step _ = throwError "cannot step"
  
evaluate :: Tm -> M Val
evaluate (Halt _ (Ann v _)) = return v
evaluate e = do
  e' <- step e
  evaluate e'
  
-----------------------------------------------------------------
-- Pretty-printer
-----------------------------------------------------------------

instance Display Ty where
  display (TyVar n)     = display n
  display TyInt       = return $ text "Int"
  display (All bnd) = lunbind bnd $ \ (as,tys) -> do
    da <- displayList as
    dt <- displayList tys
    if null as 
      then return $ parens dt <+> text "-> void"
      else prefix "forall" (brackets da PP.<> text "." <+> parens dt <+> text "-> void")
  display (TyProd tys) = displayTuple tys
  display (Exists bnd) = lunbind bnd $ \ (a,ty) -> do
    da <- display a 
    dt <- display ty
    prefix "exists" (da PP.<> text "." <+> dt)
    
instance Display (ValName,Embed Ty) where                         
  display (n, Embed ty) = do
    dn <- display n
    dt <- display ty
    return $ dn PP.<> colon PP.<> dt
    
instance Display Val where                         
  display (TmInt i) = return $ int i
  display (TmVar n) = display n
  display (Fix bnd) = lunbind bnd $ \((f, as), bnd2) -> lunbind bnd2 $ \(xtys, e) -> do
    df    <- display f 
    ds    <- displayList as  
    dargs <- displayList xtys
    de    <- withPrec (precedence "fix") $ display e
    let tyArgs = if null as then empty else brackets ds
    let tmArgs = if null xtys then empty else parens dargs
    if f `elem` (toListOf fv e :: [ValName])
      then prefix "fix" (df <+> tyArgs PP.<> tmArgs PP.<> text "." $$ de)
      else prefix "\\"  (tyArgs PP.<> tmArgs PP.<> text "." $$ de)
    
  display (TmProd es) = displayTuple es
  
  display (Pack ty e) = do 
    dty <- display ty
    de  <- display e 
    prefix "pack" (brackets (dty PP.<> comma PP.<> de))
  display (TApp av ty) = do
    dv <- display av
    dt <- display ty
    return $ dv <+> brackets dt

instance Display AnnVal where
{-  display (Ann av ty) = do
    da <- display av
    dt <- display ty
    return $ parens (da PP.<> text ":" PP.<> dt) -}
  display (Ann av _) = display av

instance Display Tm where
  display (App av args) = do
    da    <- display av
    dargs <- displayList args
    let tmArgs = if null args then empty else space PP.<> parens dargs
    return $ da PP.<> tmArgs
  display (Halt ty v) = do 
    dv <- display v
    --dt <- display ty
    return $ text "halt" <+> dv -- <+> text ":" <+> dt
  display (Let bnd) = lunbind bnd $ \(d, e) -> do
    dd <- display d
    de <- display e
    return (text "let" <+> dd <+> text "in" $$ de)
  display (TmIf0 e0 e1 e2) = do
    d0 <- display e0
    d1 <- display e1
    d2 <- display e2
    prefix "if0" $ parens $ sep [d0 PP.<> comma , d1 PP.<> comma, d2]

instance Display Decl where
  display (DeclVar x (Embed av)) = do
    dx <- display x
    dv <- display av
    return $ dx <+> text "=" <+> dv
  display (DeclPrj i x (Embed av)) = do
    dx <- display x
    dv <- display av
    return $ dx <+> text "=" <+> text "pi" PP.<> int i <+> dv
  display (DeclPrim x (Embed (e1, p, e2))) = do
    dx <- display x
    let str = show p
    d1 <- display e1 
    d2 <- display e2 
    return $ dx <+> text "=" <+> d1 <+> text str <+> d2
  display (DeclUnpack a x (Embed av)) = do
    da <- display a
    dx <- display x
    dav <- display av
    return $ brackets (da PP.<> comma PP.<> dx) <+> text "=" <+> dav
    
--------------------------------------------
-- C to H  (actually C)  Hoisting
--------------------------------------------    

displayCode (Ann v ty) = display v

instance Display Heap where
  display (Heap m) = do
    fcns <- mapM (\(d,v) -> do 
                     dn <- display d
                     dv <- displayCode v
                     return (dn, dv)) (Map.toList m)
    return $ hang (text "letrec") 2 $ 
      vcat [ n <+> text "=" <+> dv | (n,dv) <- fcns ]

instance Display (Tm, Heap) where
  display (tm,h) = do
    dh <- display h
    dt <- display tm
    return $ dh $$ text "in" <+> dt