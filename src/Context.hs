module Context where

import Data.Map (Map)
import qualified Data.Map as M
import Syntax
import Definition

type VType = Value
data Value 
  = VRig Lvl Spine
  | VLam Name Closure
  | VPi Name VType Closure
  | VCons ConsDef Spine
  | VData DataDef Spine
  | VFunc FuncDef Spine
  | VU

data Closure = Closure Env Term

pattern VVar :: Lvl -> Value
pattern VVar x = VRig x []

type Spine = [Value]

type Defs = Map Name Def

type Env = [VType]

currentLvl :: Env -> Lvl 
currentLvl = Lvl . length

type TyEnv = [(Name, VType)]

data Context = Context
  { values :: Env
  , types  :: TyEnv
  , defs   :: Defs
  }

pushVar :: Name -> VType -> Value -> Context -> Context 
pushVar x t v (Context vals typs defs) = Context (v:vals) ((x,t):typs) defs

pushVar' :: Name -> VType -> Context -> Context 
pushVar' x t (Context vals typs defs) = Context (VVar (currentLvl vals):vals) ((x,t):typs) defs

