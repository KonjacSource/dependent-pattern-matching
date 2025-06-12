module Draft where

import Syntax 
import Definition
import Context
import Evaluation
import qualified Data.Map as M

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
  , funcArgTypes = [("_", Call "Nat"), ("_", Call "Nat")]
  , funcType = Call "Nat"
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

testDefs :: Defs
testDefs = M.fromList [("Nat", DefData natDef), ("zero", DefCons zeroDef), ("suc", DefCons sucDef), ("add", DefFunc addDef)]


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
