{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-} 
{-# OPTIONS_GHC -ddump-splices #-}

module Don'tWriteParser.Test where 

import Prelude hiding ((/))
import Don'tWriteParser.Parser 
import Language.Haskell.TH
import Syntax (Raw (..)) 
import qualified Syntax as S
