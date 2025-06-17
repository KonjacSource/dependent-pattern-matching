module Printer.ValuePrinter where 

import Definition
import Syntax
import Context
import Evaluation
import Printer.TermPrinter
import Tools
import GHC.Stack (HasCallStack)

showVal :: HasCallStack => Context -> Value -> String 
showVal ctx v =printTerm 0 (ctxNames ctx) (quote (defs ctx) (currentLvl (values ctx)) v) ""

showCtx :: HasCallStack => Context -> String
showCtx ctx@(Context values types defs) = "\n" ++ go values types where 
  go [] [] = ""
  go (v:vs) ((x, t):ts) = 
    go vs ts ++ "\n" ++

    x ++ " : " ++ showVal ctx t ++ " := " ++
    showVal ctx v

instance ContextShow Context Value where 
  ctxShow = showVal