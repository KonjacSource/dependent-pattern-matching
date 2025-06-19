module Context where

import Data.Map (Map)
import qualified Data.Map as M
import Syntax
import Definition

data Value 
  = VRig Lvl Spine
  | VLam Name Closure
  | VPi Name VType Closure
  | VCons ConsDef Spine
  | VData DataDef Spine
  | VFunc FuncDef Spine
  | VU

type VType = Value

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

-- pattern to value
p2v :: Defs -> Lvl -> Pattern -> Value
p2v defs dep = fst . go1 dep where
  go1 l = \case 
    PatVar _ -> (VVar dep, l+1)
    PatCon c ps -> case M.lookup c defs of 
      Just (DefCons c) -> 
        let (l, r) = go dep ps in 
          (VCons c l, r)
      _ -> error "impossible"
  go l [] = ([], l)
  go l (p:ps) = 
    let (p', l') = go1 l p 
        (ps', l'') = go l' ps 
    in (p':ps', l'')


--------
deriving instance Show ConsDef
deriving instance Show DataDef
deriving instance Show FuncDef
deriving instance Show Clause
deriving instance Show Pattern
deriving instance Show Value
deriving instance Show Closure
deriving instance Show RFuncDef
deriving instance Show RClause
deriving instance Show RPattern

