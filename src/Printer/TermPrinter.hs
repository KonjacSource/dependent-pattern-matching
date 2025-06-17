module Printer.TermPrinter where 

import Definition
import Syntax
import Context
import GHC.Stack (HasCallStack)

ctxNames :: Context -> [Name]
ctxNames (types -> ts) = fst <$> ts

freshName :: [Name] -> Name -> Name 
freshName used "_" = "_"
freshName used x
  | x `notElem` used = x 
  | otherwise = go 0 where 
    go n | x ++ show n `elem` used = go (n + 1)
         | otherwise = x ++ show n

atomp, appp, pip, letp :: Int
atomp = 3 
appp = 2 
pip = 1 
letp = 0 

par :: Int -> Int -> ShowS -> ShowS 
par p p' = showParen (p' < p)

printTerm :: HasCallStack => Int -> [Name] -> Term -> ShowS 
printTerm p ns = \case 
  Var x 
    | x >= 0 -> ((ns !! x) ++)
    | otherwise -> ("v" ++) . (show x ++) -- This happend when unification of pattern matching.
  Call f -> (f ++)
  App a b -> par p appp $ printTerm appp ns a . (' ':) . printTerm atomp ns b
  Lam (freshName ns -> x) t -> par p letp $ 
    ("λ " ++) . (x ++) . goLam (x:ns) t where 
      goLam ns (Lam (freshName ns -> x) t) =
        (' ':) . (x++) . goLam (x:ns) t
      goLam ns t = (". "++) . printTerm letp ns t
  U -> ("U" ++)
  Pi "_" a b -> par p pip $ printTerm appp ns a . (" → " ++) . printTerm pip ("_" : ns) b
  Pi (freshName ns -> x) a b -> par p pip $ 
    piBinder ns x a . goPi (x:ns) b where 
      goPi ns (Pi (freshName ns -> x) a b)
        | x /= "_" = piBinder ns x a . goPi (x:ns) b
      goPi ns b = (" → "++) . printTerm pip ns b
  Let (freshName ns -> x) a t u -> par p letp $ 
    ("let "++) . (x++) . (" : "++) . printTerm letp ns a . ("\n  = "++) . printTerm letp ns t . (";\n\n"++) . printTerm letp (x:ns) u
  PrintEnv x -> printTerm p ns x
  where piBinder ns x a = showParen True ((x ++) . (" : " ++) . printTerm letp ns a)

showTerm :: Context -> Term -> String 
showTerm ctx t = printTerm 0 (ctxNames ctx) t ""