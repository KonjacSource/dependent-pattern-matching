module Tools where 

import Debug.Trace 
import Data.List (intercalate)

output :: ContextShow c a => c -> a -> b -> b 
output ctx a = trace (ctxShow ctx a ++ "\n") 

class ContextShow c a where
  ctxShow :: c -> a -> String

instance ContextShow c a => ContextShow c [a] where 
  ctxShow ctx = ("[" ++) . (++ "]") . intercalate ", " . map (ctxShow ctx)