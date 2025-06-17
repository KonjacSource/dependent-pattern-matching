module FunctionChecker where

import Syntax
import Definition
import Context
import Evaluation
import TypeChecker
import qualified Data.Map as M
import Tools
import Printer.ValuePrinter
import Debug.Trace (trace)
import GHC.Stack (HasCallStack)
import Printer.TermPrinter

-- 检查模式匹配
--------------
{-
考虑一个如下函数定义

```
f : (x : A) (y : B) (z : C) -> D 
f p1 p2 p3 = rhs
```

每个模式对应参数中的一个变量.
前面的模式会影响后面的类型, 比如当我们使用 p1 去匹配 x 的时候, 
后面的类型就变成了 (y : B[p1/x]) (z : C[p1/x]) -> D[p1/x],
所以当我们检查模式的时候, 需要关注语境的变换, 
最终当三个模式匹配完成之后, 我们需要检查 rhs : D [p1/x] [p2/y] [p3/z].

另一方面, 我们需要进一步考虑模式之间的依赖性. 
一些靠前的变量模式可能会被后面的模式重新赋值, 
很多系统使用一些特定的标注来指示被赋值的模式, 通常被称为 Inaccessible Pattern.
我们这里不使用 Inaccessible Pattern, 直接使用变量模式, 并在 rhs 添加新的绑定.
例如,

```
sym : (x y : A) -> x = y -> y = x
sym x y (refl u) = ?0
```

这样右边的语境看起来就像 

x = u : A
y = u : A
u : A
-----------
?0 : u = u

转换成我们这里使用的 de Bruijn index 和 level 之后看起来就像

Name  | Index  | Value (Level)
-------------------------------
u     | 0      | VVar 2
y     | 1      | VVar 2 
x     | 2      | VVar 2

这里诡吊的一点是外层的变量被赋了内层的值, 这点在实现时不会造成困扰, 
以 sym 函数为例, 当我们模式匹配到 refl 的时候, de Bruijn 已经积累到了 2.
-}

-- unify ctx flexet u v t = ctx'
-- 其中 ctx 是当前语境, flexet 是灵活变量集合, u 和 v 是我们试图 unify 的两个值, t 是它们的类型, ctx' 是 unify 之后的新语境, 
-- 我们要更新被 unify 的变量之后的语境部分. 
-- 注意这里的 unify 没有对称性, 我们总是将 u 里的灵活变量赋值.
unify :: Context -> [Lvl] -> Value -> Value -> VType -> TCM Context
unify ctx flexet u v t = 
  -- trace ("I'm unifying " ++ showVal ctx u ++ " with " ++ showVal ctx v ++ " against type: " ++ showVal ctx t)
  case (u, v) of
    (VVar x, v)
      | x `elem` flexet && x `notElem` fv (defs ctx) (currentLvl (values ctx)) v ->
          pure $ updateCtx ctx x v
    (VCons c us, VCons c' vs)
      | consName c == consName c' ->
          unifySp ctx flexet us vs $ eval (evalCtx ctx) (consType c)
    (u, v)
      | conv (evalCtx ctx) u v -> pure ctx
      | otherwise -> Left "Unable to unify"

unifySp :: Context -> [Lvl] -> Spine -> Spine -> VType -> TCM Context
unifySp ctx flexet us vs ts = case (us, vs, ts) of
  ([], [], _) -> pure ctx
  (u:us, v:vs, VPi x t b) -> do
    ctx' <- unify ctx flexet u v t
    let u' = updateVal ctx' u
    -- trace ("before update: " ++ showVal ctx u ++ " after: " ++ showVal ctx' u') $ pure ()
    unifySp ctx' flexet us vs (evalClosure (defs ctx) b u')
  _ -> 
    output ctx [us, vs, [ts]] $
    Left "unifySp: Unable to unify"

updateVal :: Context -> Value -> Value
updateVal ctx = eval (evalCtx ctx) . quote (defs ctx) (currentLvl (values ctx))

-- TODO: test
updateCtx :: Context -> Lvl -> Value -> Context
updateCtx ctx x v = 
  -- trace ("I'm updating contex: " ++ showCtx ctx ++ "\n\n" ++ " with: " ++ show x ++ " := " ++ showVal ctx v) $ 
  -- trace ("\t x' := " ++ show x') $
  -- trace ("\t x'v := " ++ fst xty) $
  -- trace ("\t postenv := " ++ show postenv) $
  -- trace ("\t postyp := " ++ show postyp) $
  -- trace ("#result := " ++ showCtx (Context env' typ' def)) $
  Context env' typ' def
  where
    env = values ctx
    typ = types ctx
    def = defs ctx
    x' = toIx (currentLvl env) x
    (postenv, xval_old:prenv) = splitAt x' env
    (postyp, xty:pretyp) = splitAt x' typ

    env1 = postenv ++ v : prenv 

    refresh es tys []     [] = (es, tys)
    refresh es tys (v:vs) ((x,t):ts) =
      -- trace "---------------------------------------------------------------------" $
      -- trace ("doing " ++ x ++ " quote v = " ++ showTerm ctx (quote def (currentLvl env) v)) $
      -- trace ("        eval v = " ++ showVal ctx (eval (def, env) (quote def (currentLvl env) v))) $
      refresh (eval (def, env1) (quote def (currentLvl env) v):es) 
              ((x, eval (def, env1) (quote def (currentLvl env) t)):tys) 
              vs ts
    refresh _ _ _ _ = error "impossible"

    (env', typ') = refresh (v:prenv) (xty:pretyp) (reverse postenv) (reverse postyp)

checkPat :: Context -> [Pattern] -> VType -> TCM (Context, VType)
checkPat ctx [] ty = pure (ctx, ty)
checkPat ctx (p:ps) (VPi x' a b) = 
  -- trace ("I'm checking the pattern: " ++ show p ++ " aginst type: " ++ showVal ctx a) $ 
  case p of 
    PatVar x -> do
      let ctx' = pushVar' x a ctx
      let b' = evalClosure (defs ctx) b (VVar $ currentLvl (values ctx))
      -- trace ("rest_type = " ++ showVal ctx' b') $ pure ()
      (rest, rhs) <- checkPat ctx' ps b' 
      pure (rest, rhs)
    PatCon c c_arg -> case a of 
      VData d d_arg -> do
        (c_tele, c_ix) <- lookupCons d c
        let c_ty = eval (evalCtx ctx) $ getConsType d c_tele c_ix
        (ctx', c_ty') <- checkPat ctx c_arg c_ty
        d_arg' <- case c_ty' of 
          VData _ x -> pure x 
          _ -> Left "impossible"
        let d_type = eval (evalCtx ctx') (dataType d)
        -- trace ("Starting unification: " ++ ctxShow ctx' d_arg ++ " with " ++ ctxShow ctx' d_arg' ++ " against: " ++ ctxShow ctx' d_type) $ pure ()
        ctx'' <- unifySp ctx' (fvSp (defs ctx') (currentLvl (values ctx')) d_arg) d_arg d_arg' d_type 
        let b_rest = evalClosure (defs ctx'') b (p2v (defs ctx'') (currentLvl (values ctx')) p)
        let b_rest_updated = eval (evalCtx ctx'') (quote (defs ctx'') (currentLvl (values ctx'')) b_rest)
        -- trace ("rest_type = " ++ showVal ctx'' b_rest_updated) $ pure ()
        checkPat ctx'' ps b_rest_updated 
      _ -> Left "Try to eliminate a nondatatype with constructor."
checkPat _ _ _ = Left "too much patterns."

checkArity :: FuncDef -> TCM () 
checkArity _ = pure () -- TODO 

checkCls :: HasCallStack => Context -> Id -> Type -> RClause -> TCM Clause
checkCls ctx func_name func_typ (RClause ps rhs) = do
  -- trace "I'm checking clause" $ pure ()
  let func_typ' = eval (evalCtx ctx) func_typ
  (ctx', rhs_ty) <- checkPat ctx ps func_typ'
  -- trace ("I'm checking rhs: " ++ showCtx ctx' ++ "\n-------------\n rhs : " ++ showVal ctx' rhs_ty) $ pure ()
  rhs' <- check ctx' rhs rhs_ty
  pure $ Clause ps rhs'

checkFunc1 :: Context -> RFuncDef -> TCM FuncDef
checkFunc1 ctx (RFuncDef func_name func_typ cls) = do 
  func_typ' <- check ctx func_typ VU
  let go = \case 
        [] -> pure [] 
        (rcls : rrest) -> do 
          cls <- checkCls ctx func_name func_typ' rcls
          rest <- go rrest 
          pure $ cls : rest
  cls' <- go cls
  pure $ FuncDef func_name func_typ' cls'

checkFunc ::  Context -> RFuncDef -> TCM FuncDef
checkFunc ctx rfun = do 
  fun <- checkFunc1 ctx rfun 
  checkArity fun 
  -- TODO : Check Coverage.
  pure fun