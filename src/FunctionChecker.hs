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

data UnifRes 
  = UnifOk Context 
  | UnifStuck  -- When Agda would say : I'm not sure if there should be a case for the constructor 
  | UnifFail   -- Absurd pattern

-- unify ctx u v t = ctx'
-- 其中 ctx 是当前语境, u 和 v 是我们试图 unify 的两个值, t 是它们的类型, ctx' 是 unify 之后的新语境, 
-- 我们要更新被 unify 的变量之后的语境部分. 
unify :: Context -> Value -> Value -> VType -> UnifRes
unify ctx u v t = 
  -- trace ("I'm unifying " ++ showVal ctx u ++ " with " ++ showVal ctx v ++ " against type: " ++ showVal ctx t)
  case (u, v) of
    (VVar x, v)
      | x `notElem` fv (defs ctx) (currentLvl (values ctx)) v ->
          UnifOk $ updateCtx ctx x v
    (v, VVar x)
      | x `notElem` fv (defs ctx) (currentLvl (values ctx)) v ->
          UnifOk $ updateCtx ctx x v
    (VCons c us, VCons c' vs)
      | consName c == consName c' ->
          unifySp ctx us vs $ eval (evalCtx ctx) (consType c)
      | otherwise -> UnifFail
    (u, v)
      | conv (evalCtx ctx) u v -> UnifOk ctx
      | otherwise -> UnifStuck

unifySp :: Context -> Spine -> Spine -> VType -> UnifRes
unifySp ctx us vs ts = case (us, vs, ts) of
  ([], [], _) -> UnifOk ctx
  (u:us, v:vs, VPi x t b) -> 
    case unify ctx (updateVal ctx u) (updateVal ctx v) t of 
      UnifOk ctx' -> 
        let u' = updateVal ctx' u in 
        -- trace ("before update: " ++ showVal ctx u ++ " after: " ++ showVal ctx' u') $ 
        unifySp ctx' us vs (evalClosure (defs ctx) b u')
      e -> e
  _ -> 
    output ctx [us, vs, [ts]] $
    error "impossible"

updateVal :: Context -> Value -> Value
updateVal ctx = eval (evalCtx ctx) . quote (defs ctx) (currentLvl (values ctx))

freshVal :: Defs -> [Value] -> [Value] -> Value -> Value 
freshVal def from to = eval (def, to) . quote def (currentLvl from)

-- TODO: crucial part of unification, need fully test
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

    changeTail :: [a] -> [a] -> [a]
    changeTail orig new = take (length orig - length new) orig ++ new

    -- 只更换了 x 的值的语境.
    env1 = postenv ++ v : prenv 

    -- 用上面那个语境去更新被他影响到的语境.
    -- 注意前方的语境也可能被影响, 所以这里需要对语境整体进行刷新.
    -- 先前的版本只更新了后方的语境.
    refresh :: [Value] -> [(Name, VType)] -> ([Value], [(Name, VType)]) 
    refresh [] [] = ([], [])
    refresh (v:es) ((x,t):tys) = 
      let (es', tys') = refresh es tys 
          env'' = changeTail env1 es' 
      in (freshVal def env env'' v :es', (x, freshVal def env env'' t): tys')
    refresh _ _ = error "refresh: impossible"

    (env', typ') = refresh env typ 

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
          e -> Left $ "checkPat: impossible, expected a data type: " ++ showVal ctx e
        let d_type = eval (evalCtx ctx') (dataType d)
        -- trace ("Starting unification: " ++ ctxShow ctx' d_arg ++ " with " ++ ctxShow ctx' d_arg' ++ " against: " ++ ctxShow ctx' d_type) $ pure ()
        ctx'' <- case unifySp ctx' d_arg d_arg' d_type of 
          UnifOk c -> pure c 
          UnifStuck -> Left "I'm not sure if there should be a case."
          UnifFail -> Left "Impossible case."
        -- b_rest is using an old context in its closure, so we need to update it.
        -- So we have to refresh the context.
        -- Note. Here p2v start from the level of ctx, not ctx''.
        let patVal = p2v (defs ctx'') (currentLvl (values ctx)) p
        let patVal' = eval (evalCtx ctx'') (quote (defs ctx'') (currentLvl (values ctx'')) patVal)
        let b_rest = evalClosure (defs ctx'') b patVal'
        -- trace ("context = " ++ showCtx ctx'') $ pure ()
        -- trace ("pattern = " ++ show p) $ pure ()
        -- trace ("p2v = " ++ show (p2v (defs ctx'') (currentLvl (values ctx)) p) ++ "\n\n") $ pure ()
        let b_rest_updated = eval (evalCtx ctx'') (quote (defs ctx'') (currentLvl (values ctx'')) b_rest)

        ------------------------------------------------------
        -- let Closure _ body = b
        -- let b_rest = eval (defs ctx'', p2v (defs ctx'') (currentLvl (values ctx')) p : values ctx'') body
        ------------------------------------------------------

        -- trace ("rest_type = " ++ showVal ctx'' b_rest_updated) $ pure ()
        checkPat ctx'' ps b_rest_updated 
      _ -> Left "Try to eliminate a nondatatype with constructor."
checkPat _ _ _ = Left "too much patterns."

checkArity :: FuncDef -> TCM () 
checkArity _ = pure () -- TODO 

elabPattern :: Defs -> RPattern -> Pattern 
elabPattern defs (RPat x ps) = case ps of 
  [] -> -- maybe var or con
    case M.lookup x defs of 
      Just (DefCons _) -> PatCon x []
      _ | x /= "_" -> PatVar x
        | otherwise -> error "not support yet."
  _ -> PatCon x (elabPattern defs <$> ps) -- must be con

checkCls :: HasCallStack => Context -> Id -> Type -> RClause -> TCM Clause
checkCls ctx func_name func_typ (RClause (map (elabPattern (defs ctx)) -> ps) rhs) = do
  -- trace "I'm checking clause" $ pure ()
  let func_typ' = eval (evalCtx ctx) func_typ
  (ctx', rhs_ty) <- checkPat ctx ps func_typ'
  -- trace ("I'm checking rhs: " ++ showCtx ctx' ++ "\n-------------\n rhs : " ++ showVal ctx' rhs_ty) $ pure ()
  rhs' <- check ctx' rhs rhs_ty
  pure $ Clause ps rhs'

checkFunc1 :: Context -> RFuncDef -> TCM FuncDef
checkFunc1 ctx (RFuncDef func_name func_typ cls) = do 
  func_typ' <- check ctx func_typ VU
  -- trace ("Checking function: " ++ func_name ++ " with type: " ++ showTerm ctx func_typ') $ pure ()
  let go = \case 
        [] -> pure [] 
        (rcls : rrest) -> do 
          cls <- checkCls ctx func_name func_typ' rcls
          rest <- go rrest 
          pure $ cls : rest
  cls' <- go cls
  pure $ FuncDef func_name func_typ' cls'

insertFunc :: Defs -> FuncDef -> Defs
insertFunc defs func = M.insert (funcName func) (DefFunc func) defs

checkFunc ::  Context -> RFuncDef -> TCM FuncDef
checkFunc ctx rfun = do 
  prefun <- checkFunc1 ctx (rfun {funcClausesR = []})
  -- this allowing recursion.
  fun <- checkFunc1 (ctx {defs = M.insert (funcNameR rfun) (DefFunc prefun) (defs ctx)}) rfun 
  checkArity fun 
  -- TODO : Check Coverage.
  pure fun