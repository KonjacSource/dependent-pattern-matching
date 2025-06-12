-- 函数, 类型的定义
module Definition where

import Syntax

data Def
  = DefFunc FuncDef
  | DefData DataDef
  | DefCons ConsDef 

data ConsDef = ConsDef
  { consName :: Name 
  , consData :: DataDef -- ^ 该构造子所属的类型.
  , consType :: Type -- ^ 构造子本身作为一个函数的类型
  }

data FuncDef = FuncDef
  { funcName :: Name
  , funcArgTypes :: Telescope 
  , funcType :: Type -- ^ 返回值的类型, funcArgTypes |- funcType
  , funcClauses :: [Clause]
  }

data DataDef = DataDef
  { dataName :: Name 
  , dataIx   :: Telescope
  , dataCons  :: [(Name, Telescope, [Term])] 
  -- ^ 构造子的名字, 参数列表, 返回的 Indexes 
  }

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
  arity = length . funcArgTypes