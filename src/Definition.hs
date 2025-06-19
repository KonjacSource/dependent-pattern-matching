-- 函数, 类型的定义
module Definition where

import Syntax

data Def
  = DefFunc FuncDef
  | DefData DataDef
  | DefCons ConsDef 

data ConsDef = ConsDef
  { consName :: Id 
  , consData :: DataDef -- ^ 该构造子所属的类型.
  , consType :: Type -- ^ 构造子本身作为一个函数的类型
  }

data FuncDef = FuncDef
  { funcName :: Id
  , funcType :: Type -- ^ 函数的类型
  , funcClauses :: [Clause]
  } 

data DataDef = DataDef
  { dataName :: Id 
  , dataIx   :: Telescope
  , dataCons  :: [(Id, Telescope, [Term])] 
  -- ^ 构造子的名字, 参数列表, 返回的 Indexes, dataCons.2 |- dataCons.3 
  } 

lookupCons :: DataDef -> Id -> TCM (Telescope, [Term])
lookupCons (DataDef d _ cons) c = go cons where 
  go [] = Left $ c ++ " is not a constructor of " ++ d 
  go ((c', ts, ix):rest) 
    | c' == c = pure (ts, ix)
    | otherwise = go rest

getConsType :: DataDef -> Telescope -> [Term] -> Term 
getConsType d [] ix = go (Call $ dataName d) ix where 
  go t [] = t
  go t (a:as) = go (App t a) as
getConsType d ((x, t):ts) ix = Pi x t $ getConsType d ts ix 

dataType :: DataDef -> Type 
dataType d = go (dataIx d) where 
  go [] = U 
  go ((x,t):ts) = Pi x t (go ts)

data Clause = Clause
  { clausePatterns :: [Pattern]
  , clauseRhs :: Term
  }  

data Pattern 
  = PatVar Name
  | PatCon Name [Pattern] 

class Arity f where 
  arity :: f -> Int 

instance Arity Clause where 
  arity = length . clausePatterns

instance Arity FuncDef where 
  arity f = case funcClauses f of 
    [] -> 0
    (c:_) -> arity c

data RClause = RClause
  { clausePatternsR :: [RPattern]
  , clauseRhsR :: Raw
  }

data RPattern = RPat Name [RPattern]

data RFuncDef = RFuncDef
  { funcNameR :: Id
  , funcTypeR :: Raw -- ^ 函数的类型
  , funcClausesR :: [RClause]
  }  

type RTelescope = [(Name, Raw)]

data RDataDef = RDataDef
  { dataNameR :: Name
  , dataIxR :: RTelescope
  , dataConsR :: [(Name, RTelescope, [Raw])]
  } deriving Show 

data RDef = RDefData RDataDef | RDefFunc RFuncDef

type Program = [RDef]

