# dependent-pattern-matching

依赖模式匹配和 Indexed Inductive Types 的最简单实现, 简单起见, 不考虑元变量求解和终止检查. 对项的检查的部分高度参考 elaboration-zoo.
包含元变量求解和终止检查的项目可以看 [ShiTT](https://github.com/KonjacSource/ShiTT).

阅读之前, 读者需要了解以下内容,
- 基本的依值类型实现 (双向类型检查)
- 了解 de Bruijn Index 和 Level, 以及基于此的求值
- 基本 Haskell 语法
- 对依赖模式匹配有基本的直觉 (或者你熟悉 GADT 也行)

主要模块的阅读顺序:
- Syntax [Done]
  * 基本语法, 项的定义
- Definition [Done]
  * 类型, 函数定义的语法
- Context [Done]
  * 各种语境相关定义与工具
- Evaluation [Done]
  * 支持模式匹配的求值器, 基于 NBE.
- TypeChecker [Done]
  * 项的双向类型检查, 没写 elaborator
- FunctionChecker [Todo]
  这是本项目的核心
  * 检查函数 [Done]
  * 模式完全性检查 [Todo]

有一篇写的很烂的[文章](design_proof_assistant_net.pdf).

## Example

我写 Template Haskell 是因为懒得写 parser.

```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-} 
import Prelude hiding ((/))
import Syntax 
import Definition
import Context
import Evaluation
import qualified Data.Map as M
import Don'tWriteParser.Parser 
import ProgramChecker

testProg = checkProg M.empty $(parseProg =<< [|
    datatype Id : (A : U) (x : A) (y : A) --> U 
    / refl : (A : U) (x : A) --> Id A x x 

    $
    
    def cong : (A : U) (B : U) (x : A) (y : A) (f : A --> B) --> Id A x y --> Id B (f x) (f y) 
    / A . B . x . y . f . (refl A1 x1) := refl B (f y)

    $

    def sym : (A : U) (x : A) (y : A) --> Id A x y --> Id A y x 
    / A . x . y . (refl A1 x1) := refl A1 x1

    $

    def trans : (A : U) (x : A) (y : A) (z : A) --> Id A x y --> Id A y z --> Id A x z
    / A . x . y . z . (refl A1 x1) . (refl A2 y1) := refl A2 y1 

    $

    datatype Nat : U
    / zero : Nat
    / suc : (_ : Nat) --> Nat

    $

    def add : (_ : Nat) (_ : Nat) --> Nat
    / zero . n := n
    / suc m . n := suc (add m n)

    $

    def addIdR : (n : Nat) --> Id Nat n (add n zero)
    / zero := refl Nat zero
    / suc m := cong Nat Nat m (add m zero) suc (addIdR m)
    
    $

    def addSuc : (n : Nat) (m : Nat) --> Id Nat (add n (suc m)) (suc (add n m))
    / zero . m := refl Nat (suc m)
    / suc n . m := cong Nat Nat (add n (suc m)) (suc (add n m)) suc (addSuc n m)
    
    $

    def addCom : (n : Nat) (m : Nat) --> Id Nat (add n m) (add m n)
    / zero . m := addIdR m
    / suc n . m := 
        trans Nat (suc (add n m)) (suc (add m n)) (add m (suc n)) 
          (cong Nat Nat (add n m) (add m n) suc (addCom n m)) 
          (sym Nat (add m (suc n)) (suc (add m n)) (addSuc m n))
    $

    def J : (A : U) (P : (x : A) (y : A) --> Id A x y --> U) 
          (m : (x : A) --> P x x (refl A x))
          (a : A) (b : A) (p : Id A a b) --> P a b p
    / A . P . m . a . b . refl A1 a1 := m a1

    $
    
    def retZero : (A : U) --> Id U A Nat --> A 
    / A . refl U' A' := do zero

    $

    datatype Vec : (A : U) (n : Nat) --> U
    / nil : (A : U) --> Vec A zero
    / cons : (A : U) (n : Nat) (a : A) (as : Vec A n) --> Vec A (suc n)

    $
    
    def append : (A : U) (n : Nat) (m : Nat) --> Vec A n --> Vec A m --> Vec A (add n m)
    / A . n . m . nil A' . ys := ys
    / A . n . m . cons A' n' x xs . ys := cons A (add n' m) x (append A n' m xs ys)
  |])
```

注. 使用 ``(do e)`` 来打印语境, 其中 ``(do e) = e`` 