# dependent-pattern-matching

[中文](README-zh.md)

The simplest implementation of Dependent Pattern Matching and Indexed Inductive Types. For simplicity, metavariable solving and termination checking are not considered. The term checking part is highly inspired by elaboration-zoo. For a project that includes metavariable solving and termination checking, see [ShiTT](https://github.com/KonjacSource/ShiTT).

Before reading, you should be familiar with:

- Basic implementation of dependent types (bidirectional type checking)
- Understanding of de Bruijn Index and Level, and evaluation based on them
- Basic Haskell syntax
- An intuitive understanding of dependent pattern matching (or familiarity with GADTs)

Recommended reading order of main modules:

- Syntax [Done]
  * Basic syntax and term definitions
- Definition [Done]
  * Syntax for types and function definitions
- Context [Done]
  * Various context-related definitions and utilities
- Evaluation [Done]
  * Evaluator supporting pattern matching, based on NBE
- TypeChecker [Done]
  * Bidirectional type checking for terms (elaborator not written)
- FunctionChecker [Todo] This is the core of the project
  * Function checking [Done]
  * Pattern coverage checking [Todo]
  
There is a shitty [paper](design_proof_assistant_net.pdf) (it's in Chinese) about this program.

Note. The comments of this project is basically in Chinese. You can directly ask questions in Issues, if you have any problem about code.

## Example

I wrote Template Haskell instead of a parser. XD

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

Note. Use ``(do e)`` to print context during type checking, where ``(do e) = e`` .