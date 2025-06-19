module DataChecker where 

import Syntax
import Definition
import Context
import Evaluation
import TypeChecker
import qualified Data.Map as M

checkTelescope :: Context -> RTelescope -> TCM (Context, Telescope)
checkTelescope ctx [] = pure (ctx, [])
checkTelescope ctx ((x,t) : rest) = do 
  t <- check ctx t VU
  (ctx, rest) <- checkTelescope (pushVar' x (eval (evalCtx ctx) t) ctx) rest
  pure (ctx, (x, t) : rest)

insertData :: Defs -> DataDef -> Defs
insertData defs dat = M.insert (dataName dat) (DefData dat) defs

checkData :: Defs -> RDataDef -> TCM DataDef
checkData defs rdat = do 
  (snd -> ix_ty) <- checkTelescope (Context [] [] defs) (dataIxR rdat)
  let defs' = insertData defs (DataDef (dataNameR rdat) ix_ty [])
  cons <- mapM (checkCons defs' ix_ty) (dataConsR rdat)
  pure (DataDef (dataNameR rdat) ix_ty cons)    
  where 
    checkCons :: Defs -> Telescope -> (Name, RTelescope, [Raw]) -> TCM (Name, Telescope, [Term])
    checkCons defs ix_ty (c, ts, ret_ix) = do 
      (ctx, ts') <- checkTelescope (Context [] [] defs) ts
      ix' <- checkSp ctx ctx ret_ix ix_ty
      pure (c, ts', ix')

getConstructors :: DataDef -> [(Name, ConsDef)]
getConstructors dat = map go (dataCons dat) where 
  go (c, ts, ix) = (c, ConsDef c dat (go1 ts (go2 (Call (dataName dat)) ix)))
  go1 [] c = c 
  go1 ((x, t):xs) c = Pi x t $ go1 xs c
  go2 c [] = c
  go2 c (a:as) = go2 (App c a) as

insertCons :: Defs -> [(Name, ConsDef)] -> Defs
insertCons = foldl (\d (c, def) -> M.insert c (DefCons def) d) 

