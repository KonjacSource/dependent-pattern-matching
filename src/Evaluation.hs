-- 求值器, 重点是 `eval`, `match`, `quote` 以及 `conv`
module Evaluation where

import Syntax
import Context
import Definition
import qualified Data.Map as M
import Debug.Trace (trace)
import Data.List (nub)
import GHC.Stack (HasCallStack)

type EvalCtx = (Defs, Env)

evalCtx :: Context -> EvalCtx
evalCtx ctx = (defs ctx, values ctx)

data MatchResult
  = MatchSuc Env   -- ^ 匹配成功
  | MatchStuck (Either Lvl FuncDef)
  -- ^ 匹配卡住了, 并返回卡住的相关信息, 这在Coverage Check的时候会用到
  | MatchFailed    -- ^ c != c'

-- | 注意, 虽然在这个项目中模式匹配总是发生在顶层, 
-- 但是我们可能会扩展这个系统, 加入模块, 或是句内 case 语句.
match1 :: EvalCtx -> Pattern -> Value -> MatchResult
match1 ctx@(def, env) pat val = case (pat, val) of
  (PatVar x, v) -> MatchSuc (v : env)
  (PatCon c ps, VCons c_def args)
    | c == consName c_def -> match ctx ps args
    | otherwise -> MatchFailed
  (PatCon _ _, VU) -> MatchFailed
  (PatCon _ _, VData _ _) -> MatchFailed
  (PatCon _ _, VLam _ _) -> MatchFailed
  (PatCon _ _, VPi {}) -> MatchFailed
  (PatCon _ _, VRig x _) -> MatchStuck (Left x)
  (PatCon _ _, VFunc f _) -> MatchStuck (Right f)

match :: EvalCtx -> [Pattern] -> Spine -> MatchResult
match (_, env) [] [] = MatchSuc env
match ctx@(def, env) (p:ps) (a:as) =
  case match1 ctx p a of
    MatchFailed -> MatchFailed
    MatchStuck l -> MatchStuck l
    MatchSuc env' -> match (def, env') ps as
match _ _ _ = error "impossible"

-- | Make sure `(length sp) <= arity f`
evalFun :: EvalCtx -> FuncDef -> [Clause] -> Spine -> Value
evalFun ctx@(def, env) f [] sp = error "evalFun: impossible, maybe something wrong in coverage checker."
evalFun ctx@(def, env) f (c:cs) sp
  | length sp < arity f = VFunc f sp -- Wait
  | otherwise = -- `length sp == arity f`
      case match ctx (clausePatterns c) sp of
        MatchFailed -> evalFun ctx f cs sp --Failed
        MatchStuck _ -> VFunc f sp       -- Stucked
        MatchSuc env' -> eval (def, env') (clauseRhs c) -- Succeeded

-- 这个模块最重要的函数
eval :: HasCallStack => EvalCtx -> Term -> Value
eval ctx@(def, env) = \case
  Var ix 
    | ix >= 0 -> env !! ix
    | otherwise -> error $ "looking for " ++ show ix ++ " in " ++ show env
  Lam x tm -> VLam x (Closure env tm)
  Pi x (eval ctx -> ty) tm -> VPi x ty (Closure env tm)
  Let x ty (eval ctx -> tm) rhs -> eval (def, tm:env) rhs
  Call f -> case M.lookup f def of
    Just (DefFunc f) -> VFunc f []
    Just (DefData d) -> VData d []
    Just (DefCons c) -> VCons c []
    Nothing -> error "eval: impossible"
  App (eval ctx -> f) (eval ctx -> a) -> app ctx f a
  PrintEnv t ->
    trace (show (quoteEnv def env)) $
    eval ctx t
  U -> VU

quoteEnv :: Defs -> Env -> [Term]
quoteEnv _ [] = []
quoteEnv def (v:vs) = quote def (currentLvl vs) v : quoteEnv def vs

app :: EvalCtx -> Value -> Value -> Value
app ctx@(def, env) f a = case f of
  VLam x clo -> evalClosure def clo a
  VFunc f sp
    | length (sp ++ [a]) < arity f -> evalFun ctx f (funcClauses f) (sp ++ [a])
    | otherwise -> let (sp', rest) = splitAt (arity f) (sp ++ [a]) in
        appSp ctx (evalFun ctx f (funcClauses f) sp') rest
  VCons c sp -> VCons c (sp ++ [a])
  VData d sp -> VData d (sp ++ [a])
  VRig x sp -> VRig x (sp ++ [a])
  VPi {} -> error "app: impossible"
  VU -> error "app: impossible"

appSp :: EvalCtx -> Value -> Spine -> Value
appSp ctx f [] = f
appSp ctx f (a:as) = appSp ctx (app ctx f a) as

quoteSp :: Defs -> Lvl -> Term -> Spine -> Term
quoteSp def l tm [] = tm
quoteSp def l tm (a:as) = quoteSp def l (App tm (quote def l a)) as

{- 
  如何转换 de Bruijn Level 和 Index?

  Level 是从外往里数，Index 是从里往外数的.
  比如
    λ x. (λ y. x y) x
  用 Level 表示是
    λ. (λ. 0 1) 0
  用 Index 则是
    λ. (λ. 1 0) 0
  Level 的好处是不需要在替换的时候进行移位, 所以我们在 `Value` 中用 Level 表示变量.
  
  `quote` 会将 `Value` 转回 `Term`, 其中自然会涉及到 Level 到 Index 的变换,
  所以我们需要在 `quote` 参数中记录当前语境的深度, 即, 最近绑定的 Level 的数值加一.
    [dep = 0] (λ. [dep = 1] (λ. [dep = 2] 0 1) 0)
-}
toIx :: Lvl -> Lvl -> Ix
toIx (Lvl dep) (Lvl lv) = dep - lv - 1

quote :: Defs -> Lvl -> Value -> Term
quote def dep = \case
  VRig lv sp -> quoteSp def dep (Var (toIx dep lv)) sp
  VLam x clo -> Lam x
    (quote def (dep + 1) (evalClosure def clo (VVar dep)))
  VPi x ty clo -> Pi x (quote def dep ty)
    (quote def (dep + 1) (evalClosure def clo (VVar dep)))
  VCons c sp -> quoteSp def dep (Call (consName c)) sp
  VFunc f sp -> quoteSp def dep (Call (funcName f)) sp
  VData d sp -> quoteSp def dep (Call (dataName d)) sp
  VU -> U

evalClosure :: Defs -> Closure -> Value -> Value
evalClosure def (Closure env tm) val = eval (def, val:env) tm

normalForm :: EvalCtx -> Term -> Term
normalForm ctx@(def, env) t = quote def (currentLvl env) (eval ctx t)

convSp :: EvalCtx  -> Spine -> Spine -> Bool
convSp ctx [] [] = True
convSp ctx (a:as) (b:bs) = conv ctx a b && convSp ctx as bs
convSp _ _ _ = False

-- Judgmental Equality.
conv :: EvalCtx -> Value -> Value -> Bool
conv ctx@(def, env) a b = case (a, b) of
    (VRig a as, VRig b bs) -> a == b && convSp ctx as bs
    (VPi _ a b, VPi _ a' b') ->
      conv ctx a a' && conv (def, VVar dep : env) (evalClosure def b (VVar dep)) (evalClosure def b' (VVar dep))
    (VLam _ b, VLam _ b') -> conv (def, VVar dep : env) (evalClosure def b (VVar dep)) (evalClosure def b' (VVar dep))

    -- 下面这两项能保证用模式匹配定义的 `id` 函数和 λx.x 相等.
    (VLam _ a, b) -> conv (def, VVar dep : env) (evalClosure def a (VVar dep)) (app ctx b (VVar dep))
    (b, VLam _ a) -> conv (def, VVar dep : env) (evalClosure def a (VVar dep)) (app ctx b (VVar dep))

    (VU, VU) -> True
    (VFunc f sp, VFunc f' sp')
      | funcName f == funcName f' -> convSp ctx sp sp'
    (VData d sp, VData d' sp')
      | dataName d == dataName d' -> convSp ctx sp sp'
    (VCons c sp, VCons c' sp')
      | consName c == consName c' -> convSp ctx sp sp'

    _ -> False
  where dep = currentLvl env


fvSp :: Defs -> Lvl -> Spine -> [Lvl]
fvSp def dep = \case 
  [] -> []
  (v:vs) -> fv def dep v ++ fvSp def dep vs

fv :: Defs -> Lvl -> Value -> [Lvl]
fv def dep = nub . \case
  VRig l sp -> l : fvSp def dep sp
  VLam x b -> filter (< dep) $ fv def (dep + 1) (evalClosure def b (VVar dep))
  VPi x t b -> fv def dep t ++ filter (< dep) (fv def (dep + 1) (evalClosure def b (VVar dep)))
  VCons _ sp -> fvSp def dep sp 
  VFunc _ sp -> fvSp def dep sp 
  VData _ sp -> fvSp def dep sp 
  VU -> []


