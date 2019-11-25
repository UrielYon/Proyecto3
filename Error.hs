module Error where

import Data.List (union,(\\))
import Data.Char (isDigit)

data Frame = PlusL () MiniHs
           | PlusR MiniHs ()
           | SucF ()
           | PredF ()             
           | ProdL () MiniHs
           | ProdR MiniHs ()
           | NegF ()
           | ConjL () MiniHs
           | ConjR MiniHs ()
           | DisyL () MiniHs
           | DisyR MiniHs ()
           | GtL () MiniHs
           | GtR MiniHs ()
           | LtL () MiniHs
           | LtR MiniHs ()
           | EquiL () MiniHs
           | EquiR MiniHs ()
           | IftF () MiniHs MiniHs
           | AppL () MiniHs
           | AppR MiniHs ()
           | RaiseF ()
           | HandleF () Name MiniHs
           deriving(Show)

type Stack = [Frame]

type Name = String

data MiniHs = V Name -- ^ Constructor for the untyped variables.
           | N Int -- ^ Constructor for untyped numbers.
           | B Bool -- ^ Constructor for untyped booleans.
           | Suc MiniHs -- ^ Constructor for untyped successor operator.
           | Pred MiniHs -- ^ Construtor for untyped predecessor operator.
           | Plus MiniHs MiniHs -- ^ Constructor for untyped plus operator.
           | Prod MiniHs MiniHs -- ^ Constructor for untyped product operator.
           | Neg MiniHs -- ^ Constructor for untyped negation operator.
           | Conj MiniHs MiniHs -- ^ Constructor for untyped conjunction operator.
           | Disy MiniHs MiniHs -- ^ Constructor for untyped disjunction operator.
           | Gt MiniHs MiniHs -- ^ Constructor for untyped greater than operator.
           | Lt MiniHs MiniHs -- ^ Constructor for untyped lower than operator.
           | Equi MiniHs MiniHs -- ^ Constructor for untyped equality operator.
           | Ift MiniHs MiniHs MiniHs -- ^ Constructor for untyped if-else operator.
           | L Name MiniHs -- ^ Constructor for untyped abstraction.
           | Fix Name MiniHs -- ^ Constructor for untyped fix operator.
           | App MiniHs MiniHs -- ^ Constructor for untyped application operator.
           | Raise MiniHs
           | Handle MiniHs Name MiniHs
            deriving(Show)

data KState = Eval Stack MiniHs | Return Stack MiniHs | Err Stack MiniHs deriving(Show)

type Subst = (Name,MiniHs)

fv :: MiniHs -> [Name]
fv (Raise e) = fv e
fv (Handle e1 x e2) = fv e1 `union` (fv e2\\[x])


newId :: Name -> Name
newId x = let (p,s) = splitName x ("","") in
  if s == "" then
    x++"0"
  else
    p++(show (fromInteger $ (read s::Integer)+1))

splitName :: Name -> (Name,Name) -> (Name,Name)
splitName [] s = s
splitName n@(c:cs) (p,s) = case isDigit c of
  True -> (p,n++s)
  False -> splitName cs (p++[c],s)

alpha :: MiniHs -> MiniHs
alpha (Raise e) = Raise (alpha e)
alpha (Handle e1 x e2) = Handle (alpha e1) x1 (alpha (substitution e2 (x,V x1))) where
  x1 = newId x


substitution :: MiniHs -> Subst -> MiniHs
substitution (Handle e1 y e2) = s@(x,r) = case not (y `elem` ([x] `union` fv r)) of
  True -> Handle (substitution e1 s) y (substitution e2 s)
  False -> let l' = alpha (Handle (substitution e1 s) y e2) in substitution l'
substitution (Raise e) s = Raise (substitution e s)


isVal :: MiniHs -> Bool
isVal (N _) = True
isVal (B _) = True
isVal (L _ _) = True
isVal _ = False

eval :: KState -> KState
eval (Eval p (N n)) = Return p (N n)
eval (Eval p (B b)) = Return p (B b)
eval (Eval p (V x)) = Return p (V x)
eval (Eval p (L x e)) = Return p (L x e)
eval (Eval p (Plus e1 e2)) = (Eval (Plus () e2):p e1)
eval (Eval (Plus () e2):p v) = case isVal v of
  True -> (Eval (PlusR v ()):p e2)
  False -> error
eval (Eval (PlusR (N n) ()) (N m)) = (Return p (N n+m))
eval (Return (NegF ()):p (B b)) = Return p (B not b)
eval (Eval p (Neg e)) = (Eval (NegF ()):p e)
eval (Return (AppR (L x e) ()):p v) = case isVal v of
  True -> (Return p (substitution e (x,v)))
  False -> error
eval (Return (AppL () e2):p v) = case isVal v of
  True -> (Eval (AppR v ()):p e2)
  False -> error
eval (Eval p (App e1 e2)) = (Eval (AppL () e2):p e1)
eval (Eval p (Fix x e)) = (Eval p (substitution e (x,(Fix x e))))
eval (Return (IftF () e2 e3):p (B False)) = (Eval p e3)
eval (Return (IftF () e2 e3):p (B True)) = (Eval p e2)
eval (Eval p (Ift e1 e2 e3)) = (Eval (IftF () e2 e3):p e1)
eval (Eval p (Raise e)) = (Eval (RaiseF ()):p e)
eval (Return (RaiseF ()):p v) = case isVal v of
  True -> (Err p v)
  False -> error "K Undefined"
eval (Eval p (Handle e1 x e2)) = (Eval (HandleF() x e2):p e1)
eval (Return (Handle () x e2):p v) = case isVal v of
  True -> Return p v
  False -> error "K Undefined"
eval (Err (t:p) (Raise v)) = case t of
  Handle () x e2 -> Eval p (substitution e2 (x,v))
  _ -> Err p (Raise v)

evals :: KState -> KState
evals s@(Return [] v) = case isVal v of
  True -> s
  False -> error
evals s = evals (eval s)

minus x y = Plus x (Prod y (N (-1)))

restaPos = L "x" (L "y" (Ift (Lt (V "x") (V "y")) (Raise (N 0)) (minus (V "x") (V "y"))))

exampleE = Handle (minus (N 1) (App (App restaPos (N 2)) (Suc (N 2)))) "x" (Prod (N 2) (V "x"))
