module Draft where

import Syntax 
import Definition
import Context
import Evaluation
import qualified Data.Map as M
import FunctionChecker

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
      { clausePatternsR = [PatVar "A", PatVar "x", PatVar "y", PatCon "refl" [PatVar "A'", PatVar "x'"]] 
      , clauseRhsR = RVar "refl" `RApp` RVar "A" `RApp` RVar "x"
      }
    ] 
  }

symDef :: FuncDef
symDef = case checkFunc (Context [] [] testDefs) symDefR of 
  Right f -> f 
  Left m -> error m

testDefs :: Defs
testDefs = M.fromList 
  [ ("Nat", DefData natDef)
  , ("zero", DefCons zeroDef)
  , ("suc", DefCons sucDef)
  , ("add", DefFunc addDef) 
  , ("Id", DefData idDef)
  , ("refl", DefCons reflDef)
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
