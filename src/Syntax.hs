module Syntax where 

-- De Bruijn index and level.
newtype Ix  = Ix  Int deriving (Eq, Show, Num) via Int
newtype Lvl = Lvl Int deriving (Eq, Show, Num) via Int

-- 局部变量名
type Name = String 

-- 全局定义的函数, 类型或是构造子
type Id = String

type Type = Term 

data Term 
  = Var Ix 
  | Lam Name Term
  | App Term Term
  | Pi Name Type Type
  | Call Id 
  -- ^ 函数, 类型, 构造子调用, 因为这些东西被认为是全局的, 所以这里不用 db ix, 这里也可以把 Id 直接换成定义.
  | Let Name Type Term Term
  | U 
  -- ^ 懒得考虑宇宙问题
  | PrintEnv Term
  -- ^ Test 
  deriving Show

infixl 7 `App`

-- 列表中处于后部的类型居于前面构成的语境中.
type Telescope = [(Name, Type)]

data Raw 
  = RVar Name 
  | RLam Name Raw 
  | RApp Raw Raw 
  | RPi Name Raw Raw 
  | RLet Name Raw Raw Raw 
  | RU 
  | RPrintEnv Raw
  -- ^ evaluate 时输出
  | RPrintCtx Raw
  -- ^ 类型检查时输出

sorry :: a
sorry = undefined
