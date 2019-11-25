{-|
Module      : MiniC
Description : An implementation of the evaluation of untyped Mini C programs.
Copyright   : (c) Fernando Abigail Galicia-Mendoza, 2019
License     : GPL-3
Maintainer  : fernandogamen@ciencias.unam.mx
Stability   : experimental-education
Portability : POSIX
This script contains the functions to calculate the evaluation of typed Mini C
Programs.
-}
module MiniC where

  import Data.List
  import Data.Char

  -- | Type that represents the set of possible variable names.
  type Name = String

  -- | A 'MiniC' is a implementation of the abstract syntax of typed Mini C programs.
  data MiniC = V Name -- ^ Constructor for the typed variables.
              | N Int -- ^ Constructor for the typed numbers.
              | B Bool -- ^ Constructor for the typed booleans.
              | Suc MiniC -- ^ Constructor for the typed successor operator.
              | Pred MiniC -- ^ Constructor for the typed predecessor operator.
              | Plus MiniC MiniC -- ^ Constructor for the typed plus operator.
              | Prod MiniC MiniC -- ^ Constructor for the typed product operator.
              | Neg MiniC -- ^ Constructor for the typed negation operator.
              | Conj MiniC MiniC -- ^ Constructor for the typed conjunction operator.
              | Disy MiniC MiniC -- ^ Constructor for the typed disjunction operator.
              | Gt MiniC MiniC -- ^ Constructor for the typed greater than operator.
              | Lt MiniC MiniC -- ^ Constructor for the typed lower than operator.
              | Equi MiniC MiniC -- ^ Constructor for the typed equality operator.
              | Ift MiniC MiniC MiniC -- ^ Constructor for the typed if-else conditional.
              | L Name MiniC -- ^ Constructor for the typed abstraction.
              | App MiniC MiniC -- ^ Constructor for the typed application.
              -- Imperative operators for memory
              | Li Label -- ^ Constructor for the memory labels
              | Assign MiniC MiniC -- ^ Constructor for the assignments
              | Ref MiniC -- ^ Constructor for the references
              | DeRef MiniC -- ^ Constructor for the dereferences
              | Void -- ^ Constructor for the empty expression
              | Seq MiniC MiniC -- ^ Constructor for the sequence of programs
              | While MiniC MiniC -- ^ Constructor for the while cycle

  type Label = Int

  -- | A 'Memory' is the implementation of a abstract memory. Consists in a pair (l,v) that represents
  -- the expression (l |-> v).
  type Memory = [(Int,MiniC)]

  -- | A 'Exec' is a representation of a state of the execution of the program.
  type Exec = (Memory,MiniC)

  instance Show MiniC where
    show l = case l of
      V x -> x
      N n -> "num["++show n++"]"
      B b -> "bool["++show b++"]"
      Suc e-> "suc("++show e++")"
      Pred e-> "pred("++show e++")"
      Plus e1 e2-> "("++show e1++"+"++show e2++")"
      Prod e1 e2-> "("++show e1++"*"++show e2++")"
      Neg e-> "not("++show e++")"
      Conj e1 e2-> "("++show e1++"&&"++show e2++")"
      Disy e1 e2-> "("++show e1++"||"++show e2++")"
      Gt e1 e2-> "("++show e1++">"++show e2++")"
      Lt e1 e2-> "("++show e1++"<"++show e2++")"
      Equi e1 e2-> "("++show e1++"=="++show e2++")"
      Ift e1 e2 e3-> "if "++show e1++" then "++show e2++" else "++show e3
      L x t -> "(lam ("++x++")"++" => "++show t++")"
      App t s -> "("++show t++" <+> "++show s++")"
      --
      Seq e1 e2 -> "("++show e1++";"++show e2++")"
      Li x -> "(l_"++show x++")"
      Assign e1 e2 -> "("++show e1++" := "++show e2++")"
      Ref e -> "(ref ("++show e++"))"
      DeRef e -> "(!("++show e++"))"
      Void -> "()"
      While e1 e2 -> "(while ("++show e1++","++show e2++"))"

  -- | A 'Subst' represents a substitution.
  type Subst = (Name,MiniC)

  -- | The 'fv' function takes a typed Mini Haskell program and returns their free variables.
  fv :: MiniC -> [Name]
 fv :: MiniC -> [Name]
  fv (V x) = [x]
  fv (N n) = []
  fv (B b) = []
  fv (Suc x) = fv x
  fv (Pred x) = fv x
  fv (Plus x y) = fv x `union` fv y
  fv (Prod x y) = fv x `union` fv y
  fv (Neg x) = fv x
  fv (Conj x y) = fv x `union` fv y
  fv (Disy x y) = fv x `union` fv y
  fv (Gt x y) = fv x `union` fv y
  fv (Lt x y) = fv x `union` fv y
  fv (Equi x y) = fv x `union` fv y
  fv (Ift x y z) = fv x `union` fv y `union` fv z
  fv (L x t e) = fv e \\ [x]
  fv (Fix x t e) = fv e \\ [x]
  fv (App t s) = fv t `union` fv s
  fv (Seq x y) = fv x `union`fv y
  fv (Li x) = fv x
  --fv (Assign x y) = fv y
  fv (Ref x) = fv x
  fv (DeRef x) = fv x
  --fv (Void) = 
  fv (While x y z) = fv x `union` fv y `union` fv z

  {-|
  The 'newId' function creates a new variable with the following conditions:
  1. If at the end of the variable is not a number then the function 
  add the number 0 at the end of the variable.
  2. If at the end of the variable is a number then the function
  replace the original number with its sucessor.
  -} 
  newId :: Name -> Name
  newId x = let (p,s) = splitName x ("","") in
              if s == "" then
                x++"0"
              else
                p++(show (fromInteger $ (read s::Integer)+1))

  {-|
  The 'splitName' function tries to split strings of the form "vn" returning
  the pair (v,n) where "v" could be any string but "n" is a string with only numbers.
  If the string doesn't end with a number then "n" will be equal to the empty string.
  -}
  splitName :: Name -> (Name,Name) -> (Name,Name)
  splitName [] s = s
  splitName n@(c:cs) (p,s) = case isDigit c of
    True -> (p,n++s)
    False -> splitName cs (p++[c],s)

  -- | The 'alpha' function generates the alpha-equivalence of a typed Mini Haskell program.
  alpha :: MiniC -> MiniC
  alpha (V x) = V (newId x)
  alpha (N n) = N n
  alpha (B b) = B b
  alpha (Suc x) = Suc (alpha x)
  alpha (Pred x) = Pred (alpha x)
  alpha (Plus x y) = Plus (alpha x) (alpha y)
  alpha (Prod x y) = Prod (alpha x) (alpha y)
  alpha (Neg x) = Neg (alpha x)
  alpha (Conj x y) = Conj (alpha x) (alpha y)
  alpha (Disy x y) = Disy (alpha x) (alpha y)
  alpha (Gt x y) = Gt (alpha x) (alpha y)
  alpha (Lt x y) = Lt (alpha x) (alpha y)
  alpha (Equi x y) = Equi (alpha x) (alpha y)
  alpha (Ift x y z) = Ift (alpha x) (alpha y) (alpha z)
  alpha (L x t e) = (L (newId x) t (substitution e (x,(V (newId x)))))
  alpha (Fix x t e) = (Fix (newId x) t (substitution e (x,(V (newId x)))))
  alpha (App t s) = App (alpha t) (alpha s)
  
  -- | The 'substitution' function applies the substitution given as 
  -- a parameter to a typed Mini Haskell program.
  substitution :: MiniC -> Subst -> MiniC
  substitution :: MiniC -> Subst -> MiniC
  substitution (V n) (x,e) = if n == x then e else (V n)
  substitution (N n) s = (N n)
  substitution (B b) s = (B b)
  substitution (Suc e) s = Suc (substitution e s)
  substitution (Pred e) s = Pred (substitution e s)
  substitution (Plus e1 e2) s = Plus (substitution e1 s) (substitution e2 s)
  substitution (Prod e1 e2) s = Prod (substitution e1 s) (substitution e2 s)
  substitution (Neg e1) s = Neg (substitution e1 s)
  substitution (Conj e1 e2) s = Conj (substitution e1 s) (substitution e2 s)
  substitution (Disy e1 e2) s = Disy (substitution e1 s) (substitution e2 s)
  substitution (Gt e1 e2) s = Gt (substitution e1 s) (substitution e2 s)
  substitution (Lt e1 e2) s = Lt (substitution e1 s) (substitution e2 s)
  substitution (Equi e1 e2) s = Equi (substitution e1 s) (substitution e2 s)
  substitution (Ift e1 e2 e3) s = Ift (substitution e1 s) (substitution e2 s) (substitution e3 s)
  substitution (L x t e) s@(y,ez) = case (not (x `elem`(fv (ez) `union` [y]))) of 
                        true -> L x t (substitution e s)
                        false-> let x' = alpha(L x t e) in substitution x' s
  substitution (Fix x t e) s@(y,ez) = if (x==y) then (Fix y t ez) else
                           if not (x `elem` (fv ez))then (Fix x t (substitution e s)) else (substitution (alpha (Fix x t e)) s)
  substitution (App x y) s = App (substitution x s) (substitution y s)
  
  -- | The 'eval' function is an implementation of the evaluation for typed Mini Haskell
  -- programs.
  eval1 :: Exec -> Exec
  eval1 (m(Suc(N n))) = (m,N (n+1))
  eval1 (m,(Suc e)) = case eval1 (m,e) of
    (m',e') -> (m',Suc e')
  eval1 (m,(Plus (N n1) (N n2))) = (m,(N (n1 + n2)))
  eval1 (m,(Plus (N n1) e)) = case eval1 (m,e) of
    (m',e') -> (m',Plus (N n1) e')
  eval1 (m,(Plus e1 e2)) = case eval1 (m,e1) of
    (m',e') -> (m',Plus e' e2)
  --Faltan los casos de todas las demas operaciones
  eval1 (m,Ift (B b) e1 e2) = if b then (m,e1) else (m,e2)
  eval1 (m,(Ift e1 e2 e3)) = case (m,e1) of
    (m',e') -> (m',(Ift e' e2 e3))
  eval1 (m,App (L x e) e2) = case isValue e2 of
    True -> (m, substitution e (x,e2))
    False -> case (m,e2) of
      (m',e') -> (m',(App(L x e) e'))
  eval1 (m,App e1 e2) = case isValue e1 of
    True -> case eval1 (m,e2) of
      (m',e2') -> (m',App e1 e2')
    False -> case eval1 (m,e1) of
      (m',e1') -> (m',App e1' e2)
  eval1 (m,(Ref e)) = case isValue e of
    True -> let l = newL m in (m++[(l,e)],Li l)
    False -> case eval1 (m,e) of
      (m',e') -> (m',Ref e')
  eval1 (m,(DeRef (Li e))) = (m,get m e)
  eval1 (m,(DeRef e)) = case eval1 (m,e) of
    (m',e') -> (m',DeRef e')
  eval1 (m,Seq Void e) = (m,e)
  eval1 (m,Seq e1 e2) = case eval1 (m,e1) of
    (m',e1') -> (m',Seq e1' e2)
  eval1 (m,Assign (Li l) e) = case isValue e of
    True -> (changeMem m l e, Void)
    False -> case eval1 (m,e) of
      (m',e') -> (m',Assign (Li l) e')
  eval1 (m,Assign e1 e2) = case eval1 (m,e1) of
    (m',e1') -> (m',Assign e1' e2)
  eval1 (m,Void) = (m,Void)
  eval1 (m,While e1 e2) = (m, (If e1 (Seq e2 (While e1 e2)) void))

  -- | The 'newL' function returns a new location memory.
  newL :: Memory -> Int
  newL _ = error "error"

  -- | The 'getVal' function returns the value stored in a memory and location given
  -- as parameters.
  getVal :: Label -> Memory -> MiniC
  getVal _ _ = error "error"

  -- | The 'changeMem' function returns the updated memory.
  changeMem :: Memory -> Label -> MiniC -> Memory
  changeMem _ _ _ = error "error"

  -- | The 'isValue' is the predicate that determines if a typed Mini Haskell
  -- program is a value.
  isVal :: MiniC -> Bool
  isVal (N _) = True
  isVal (B _) = True
  isVal (L _ _) = True
  isVal (Li _) = True
  isVal Void = True
  isVal _ = False

  {-| 
  The 'evals' function is the implementation of the relexive-transitive closure
  of the evaluation relation.
  -}
  evals' :: Exec -> Exec
   evals' (V x) = (V x)
  evals' (N n) = (N n)
  evals' (B b) = (B b)
  evals' e = evals' (eval1 e) 


  -- | The 'exec' function evaluates a program in a empty memory.
  exec :: MiniC -> Exec
  exec e = error "error"

  printExec :: Exec -> String
  printExec (m,e) = "Memory:\n"++printMem m++"\n\nFinal Execution:\n"++show e

  printMem :: Memory -> String
  printMem [] = ""
  printMem [(l,v)] = show l++" : "++show v
  printMem ((l,v):ms) = show l++" : "++show v++"\n"++printMem ms

  examplee1 = Assign (Ref (N 0)) (Suc (N 1))
  examplee2 = Assign (V "x") (Plus (DeRef (V "1")) (N 3))
  example = App (L "x" (Seq examplee1 examplee2)) (Ref (Pred (N 1)))

  -- l1 = Assign (V "x") (N 1)
  -- l2 = Assign (V "y") (N 0)
  -- l3 = Seq l1 (Seq l2 whilel)
  -- whilel = While (Lt (DeRef (V "x")) (N 2)) l4
  -- l4 = Seq l5 l6
  -- l5 = Assign (V "x") (Plus (DeRef (V "x")) (DeRef (V "x")))
  -- l6 = Assign (V "y") (Plus (DeRef (V "y")) (N 1))

  -- examplel1 = Assign (V "ret") (N 0)
  
  -- examplef = Assign (V "ret") (Plus (V "n") (V "m"))
  -- exampledf =  Assign (V "func1") (L "n" (L "m" examplef))

  -- examplef1 = App (App (DeRef (V "func1")) (V "r")) (N 3)
  -- exampledf1 =  Assign (V "doble") (L "r" (Assign (V "ret") examplef1))

  -- exampleR1 = App (DeRef (V "doble")) (N 4)

  -- examplel4 = Seq examplel1 (Seq exampledf (Seq exampledf1 exampleR1))
