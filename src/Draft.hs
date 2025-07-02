{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-} 
{-# OPTIONS_GHC -ddump-splices #-}

module Draft where

import Prelude hiding ((/))
import Syntax 
import Definition
import Context
import Evaluation
import qualified Data.Map as M
import FunctionChecker
import Don'tWriteParser.Parser 
import ProgramChecker


-- Definitions and Context 
----------------------------

{-
data Nat where 
  | zero : Nat 
  | suc : Nat -> Nat
-}
natDef :: DataDef
natDef = DataDef
  { dataName = "Nat"
  , dataIx = []
  , dataCons = [
      ("zero", [], []),
      ("suc", [("_", Call "Nat")], [])
    ]
  }

zeroDef :: ConsDef 
zeroDef = ConsDef
  { consName = "zero"
  , consData = natDef
  , consType = Call "Nat"
  }

sucDef :: ConsDef 
sucDef = ConsDef 
  { consName = "suc"
  , consData = natDef 
  , consType = Pi "_" (Call "Nat") (Call "Nat")
  }

addDef :: FuncDef 
addDef = FuncDef 
  { funcName = "add"
  , funcType = Pi "_" (Call "Nat") $ Pi "_" (Call "Nat") $ Call "Nat"
  , funcClauses = [
      Clause 
        [PatCon "zero" [], PatVar "n"] (Var 0),
      Clause 
        [PatCon "suc" [PatVar "m"], PatVar "n"] (Call "suc" `App` (Call "add" `App` Var 1 `App` Var 0))
    ]
  }

one, two, three :: Term 
one = Call "suc" `App` Call "zero"
two = Call "suc" `App` one
three = Call "suc" `App` two

{-
data Id : (A : U) (x y : A) -> U where 
  | refl : (A : U) (x : A) -> Id A x x
-}

idDef :: DataDef 
idDef = DataDef 
  { dataName = "Id"
  , dataIx = [("A", U), ("x", Var 0), ("y", Var 1)]
  , dataCons = [("refl", [("A", U), ("x", Var 0)], [Var 1, Var 0, Var 0])]
  }

reflDef :: ConsDef
reflDef = ConsDef
  { consName = "refl"
  , consData = idDef
  , consType = Pi "A" U $ Pi "x" (Var 0) $ Call "Id" `App` Var 1 `App` Var 0 `App` Var 0 
  }

{-
sym : (A : U) (x y : A) (_ : Id A x y) -> Id A y x
sym A x y (refl A' x') = refl A' x'
-}
symDefR :: RFuncDef
symDefR = RFuncDef
  { funcNameR = "sym"
  , funcTypeR = RPi "tA" RU $ RPi "tx" (RVar "tA") $ RPi "ty" (RVar "tA") $ 
      RPi "_" (RVar "Id" `RApp` RVar "tA" `RApp` RVar "tx" `RApp` RVar "ty") $
      RVar "Id" `RApp` RVar "tA" `RApp` RVar "ty" `RApp` RVar "tx"
  , funcClausesR = 
    [ RClause 
      { clausePatternsR = [RPat "A" [], RPat "x" [], RPat "y" [], RPat "refl" [RPat "A'" [], RPat "x'" []]] 
      , clauseRhsR = RVar "refl" `RApp` RVar "A" `RApp` RVar "x"
      }
    ] 
  }

symDef :: FuncDef
symDef = case checkFunc (Context [] [] testDefs) symDefR of 
  Right f -> f 
  Left m -> error m

congDefR :: RFuncDef
congDefR = $(parseFunc =<< [| 
    def cong : (A : U) (B : U) (x : A) (y : A) (f : A --> B) (_ : Id A x y) --> Id B (f x) (f y) 
    / A . B . x . y . f . refl A x1 := refl B (f y)
  |])

congDef = case checkFunc (Context [] [] testDefs) congDefR of 
  Right f -> f 
  Left m -> error m 

idDefR = $(parseData =<< [|
    datatype Id : (A : U) (x : A) (y : A) --> U 
    / refl : (A : U) (x : A) --> Id A x x 
  |])

testProg :: Program
testProg = $(parseProg =<< [|
    datatype Id : (A : U) (x : A) (y : A) --> U 
    / refl : (A : U) (x : A) --> Id A x x 

    $
    
    def cong : (A : U) (B : U) (x : A) (y : A) (f : A --> B) --> Id A x y --> Id B (f x) (f y) 
    / A . B . x . y . f . refl A1 x1 := refl B (f y)

    $

    def sym : (A : U) (x : A) (y : A) --> Id A x y --> Id A y x 
    / A . x . y . refl A1 x1 := refl A1 x1

    $

    def trans : (A : U) (x : A) (y : A) (z : A) --> Id A x y --> Id A y z --> Id A x z
    / A . x . y . z . refl A1 x1 . refl A2 y1 := do refl A1 y1

    $

    datatype Nat : U
    / zero : Nat
    / suc : (_ : Nat) --> Nat

    $

    def add : (_ : Nat) (_ : Nat) --> Nat
    / zero . n := n
    / suc m . n := suc (add m n)

    $

    def addIdR : (n : Nat) --> Id Nat n (add n zero)
    / zero := refl Nat zero
    / suc m := cong Nat Nat m (add m zero) suc (addIdR m)
    
    $

    def addSuc : (n : Nat) (m : Nat) --> Id Nat (add n (suc m)) (suc (add n m))
    / zero . m := refl Nat (suc m)
    / suc n . m := cong Nat Nat (add n (suc m)) (suc (add n m)) suc (addSuc n m)

    $

    def addCom : (n : Nat) (m : Nat) --> Id Nat (add n m) (add m n)
    / zero . m := addIdR m
    / suc n . m := 
        trans Nat (suc (add n m)) (suc (add m n)) (add m (suc n)) 
          (cong Nat Nat (add n m) (add m n) suc (addCom n m)) 
          (sym Nat (add m (suc n)) (suc (add m n)) (addSuc m n))
    
    $

    def J : (A : U) (P : (x : A) (y : A) --> Id A x y --> U) 
          (m : (x : A) --> P x x (refl A x))
          (a : A) (b : A) (p : Id A a b) --> P a b p
    / A . P . m . a . b . refl A1 a1 := m a1

    $

    def retZero : (A : U) --> Id U A Nat --> A 
    / A . refl U' A' := do zero

    $

    datatype Vec : (A : U) (n : Nat) --> U
    / nil : (A : U) --> Vec A zero
    / cons : (A : U) (n : Nat) (a : A) (as : Vec A n) --> Vec A (suc n)

    $
    
    def append : (A : U) (n : Nat) (m : Nat) --> Vec A n --> Vec A m --> Vec A (add n m)
    / A . n . m . nil A' . ys := ys
    / A . n . m . cons A' n' x xs . ys := cons A (add n' m) x (append A n' m xs ys)
  |])

testDefs' :: TCM Defs
testDefs' = checkProg M.empty testProg

testDefs :: Defs
testDefs = M.fromList 
  [ ("Nat", DefData natDef)
  , ("zero", DefCons zeroDef)
  , ("suc", DefCons sucDef)
  , ("add", DefFunc addDef) 
  , ("Id", DefData idDef)
  , ("refl", DefCons reflDef)
  , ("cong", DefFunc congDef)
  ]
-- Evaluator
----------------

-- Succeed eval
evalTest1 :: Term 
evalTest1 = normalForm (testDefs, []) (
    Call "add" `App` three `App` two
  )

-- Stucked by variable
evalTest2 :: Term 
evalTest2 = normalForm (testDefs, []) (
    Lam "x" $ 
      Call "add" `App` (Call "suc" `App` (Call "suc" `App` Var 0)) `App` one
  )

-- Stucked by smaller arity
evalTest3 :: Term
evalTest3 = normalForm (testDefs, []) (
    Call "add" `App` three
  )

-- Stucked by function
evalTest4 :: Term 
evalTest4 = normalForm (testDefs, []) (
    Lam "x" $
      Call "add" `App` (Call "add" `App` Var 0 `App` one) `App` two
  )
