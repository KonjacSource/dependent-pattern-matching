module ProgramChecker where 

import FunctionChecker 
import DataChecker
import TypeChecker
import Context
import Definition
import qualified Data.Map as M
import Syntax 

checkProg :: Defs -> Program -> TCM Defs
checkProg def [] = pure def
checkProg def (d:ds) = case d of 
  RDefFunc d -> do 
    f <- checkFunc (Context [] [] def) d 
    checkProg (insertFunc def f) ds
  RDefData d -> do 
    d <- checkData def d 
    checkProg (insertCons (insertData def d) (getConstructors d)) ds
  