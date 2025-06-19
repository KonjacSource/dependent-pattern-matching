-- 极简双向类型检查
module TypeChecker where
import Syntax
import Evaluation
import Definition 
import Context
import qualified Data.Map as M
import Printer.ValuePrinter
import Printer.TermPrinter
import Debug.Trace

infer :: Context -> Raw -> TCM (Term, VType)
infer ctx r = -- trace ("infer: " ++ show r) $ 
  case r of
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
    RPrintCtx e -> trace (showCtx ctx) $ infer ctx e 
    RPrintEnv e -> do 
      (e', et) <- infer ctx e 
      pure (PrintEnv e', et)
  where 
    lookupDef f = case M.lookup f (defs ctx) of 
      Nothing -> Left $ "Unknown identifier: " ++ f 
      Just d -> case d of 
        DefCons c -> pure (Call f, eval (evalCtx ctx) (consType c))
        DefFunc c -> pure (Call f, eval (evalCtx ctx) (funcType c))
        DefData c -> pure (Call f, eval (evalCtx ctx) (dataType c))

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
  (RPrintCtx e, et) -> do 
    trace (showCtx ctx ++ "\n----------------------------------\n" ++ showVal ctx et ) $ check ctx e et
  _ -> do 
    (r', t') <- infer ctx r
    if conv (evalCtx ctx) t' t then 
      pure r'
    else 
      Left $ "Type mismatch. \n Expecting: " ++ showVal ctx t ++ "\n Actually: " ++ showVal ctx t' ++ "\n In term: " ++ showTerm ctx r' ++ "\nIn context: " ++ showCtx ctx

checkSp :: Context -> Context -> [Raw] -> Telescope -> TCM [Term] 
checkSp ctx t_ctx [] [] = pure []
checkSp ctx t_ctx (r:rs) ((x, t):ts) = do
  let tv = eval (evalCtx t_ctx) t
  r' <- check ctx r tv
  rs' <- checkSp ctx (pushVar x tv (eval (evalCtx ctx) r') t_ctx) rs ts
  pure (r' : rs')
checkSp ctx _ _ _ = error "checkSp: impossible"