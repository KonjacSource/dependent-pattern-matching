-- 极简双向类型检查
module TypeChecker where
import Syntax
import Evaluation
import Definition 
import Context
import qualified Data.Map as M

type TCM = Either String 

infer :: Context -> Raw -> TCM (Term, VType)
infer ctx = \case 
    RVar x -> do 
      let go i = \case 
            [] -> lookupDef x 
            ((x', t): xs) 
              | x == x' -> pure (Var i, t)
              | otherwise -> go (i + 1) xs
      go 0 (types ctx)
    RU -> pure (U, VU)
    RApp f x -> do 
      (f', f_ty) <- infer ctx f 
      case f_ty of 
        VPi _ a b -> do
          x' <- check ctx x a 
          let b' = evalClosure (defs ctx) b (eval (evalCtx ctx) x')
          pure (App f' x', b')
        _ -> Left "Applied on a nonfunction."
    RLam {} -> Left "Tried to infer a lambda."
    RPi x a b -> do 
      a' <- check ctx a VU 
      b' <- check (pushVar' x (eval (evalCtx ctx) a') ctx) b VU
      pure (Pi x a' b', VU)
    RLet x t v e -> do 
      t' <- check ctx t VU
      let vt = eval (evalCtx ctx) t'
      v' <- check ctx v vt
      let vv = eval (evalCtx ctx) v'
      (e', et) <- infer (pushVar x vt vv ctx) e
      pure (Let x t' v' e', et)
    RPrintCtx e -> infer ctx e -- TODO
    RPrintEnv e -> do 
      (e', et) <- infer ctx e 
      pure (PrintEnv e', et)
  where 
    lookupDef f = case M.lookup f (defs ctx) of 
      Nothing -> Left $ "Unknown identifier: " ++ f 
      Just d -> case d of 
        DefCons c -> pure (Call f, eval (defs ctx, []) (consType c))
        DefFunc c -> pure (Call f, eval (defs ctx, []) (funcType c))
        DefData c -> pure (Call f, eval (defs ctx, []) (dataType c))

check :: Context -> Raw -> VType -> TCM Term 
check ctx r t = case (r, t) of 
  (RLam x b, VPi x' xt bt) -> do 
    b' <- check (pushVar' x xt ctx) b (evalClosure (defs ctx) bt (VVar $ currentLvl (values ctx)))
    pure (Lam x b')
  (RLet x t v e, et) -> do 
    t' <- check ctx t VU
    let vt = eval (evalCtx ctx) t'
    v' <- check ctx v vt 
    let vv = eval (evalCtx ctx) v'
    e' <- check (pushVar x vt vv ctx) e et -- No need to move indexes in `et`, since we are using de Bruijn level here
    pure (Let x t' v' e')
  _ -> do 
    (r', t') <- infer ctx r
    if conv (evalCtx ctx) t' t then 
      pure r'
    else 
      Left "Type mismatch"