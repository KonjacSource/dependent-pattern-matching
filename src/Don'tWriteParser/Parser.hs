-- Use Template Haskell as parser.
-- I should have used transformer here.
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-} 
{-# LANGUAGE DeriveLift #-} 
module Don'tWriteParser.Parser where 

import Prelude hiding ((/))
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (Lift(..))
import Syntax (Raw (..)) 
import qualified Syntax as S
import Definition 

{-
== Syntax
----------

infixr 1 / 
infixr 4 =>
infixr 5 : 

== Data Type

datatype data_id : telescope => U   
/ con_id : telescope => data_id spine
/ con_id : telescope => data_id spine
...

== Function

def f : term 
/ patterns := term  
/ patterns := term 
... 
 
== Term 

term ::= 
  | x                             -- Variable
  | term term                     -- Application 
  | \ x -> term                   -- Lambda
  | let x = term : term in term -- Let-in
  | telescope => term             -- Pi
  | term => term                  -- Function
  | U                             -- Universe

telescope ::= 
  | (x : term)
  | (x : term) telescope

pattern ::=
  | x
  | (cons patterns)

== Source File

definition
$
definition
$
definition
...

-}

infixr 1 / 
infixr 2 :=
infixr 6 -->

(/) = undefined
(-->) = undefined
data Won'tBeMultiDefined_114514 = (:=)



-- term ::= 
--   | x                             -- Variable
--   | term term                     -- Application 
--   | \ x -> term                   -- Lambda
--   | let x = term : term in term -- Let-in
--   | telescope => term             -- Pi
--   | term => term                  -- Function
--   | U                             -- Universe

-- | TODO change type to :: Exp -> Maybe Raw
parseRaw' :: Exp -> Q Exp 
parseRaw' e = case e of
  VarE (nameBase -> x) ->
    [| RVar x |]
  UnboundVarE (nameBase -> x) 
    | x == "U" -> [| RU |]
    | otherwise -> [| RVar x |]
  ConE (nameBase -> x) 
    | x == "U" -> [| RU |]
    | otherwise -> [| RVar x |]
  AppE (parseRaw' -> a) (parseRaw' -> b) -> 
    [| RApp $a $b |]
  LamE ps (parseRaw' -> body) -> 
    mkbinder binders body where 
      go (VarP x) = nameBase x 
      go (ConP x [] []) = nameBase x
      go WildP = "_"
      go _ = error $ "Parse error in: " ++ pprint e
      binders = reverse $ go <$> ps
      mkbinder [] body = [|$body|]
      mkbinder (x:xs) body = mkbinder xs [| RLam x $body |]
  LetE [ValD p (NormalB (InfixE (Just (parseRaw' -> e)) (ConE i) (Just (parseRaw' -> t)))) []] (parseRaw' -> body) 
    | nameBase i == ":" -> do
        let name = nameBase case p of 
                    VarP x -> x
                    ConP x [] [] -> x
                    _ -> error $ "Parse error in: " ++ pprint p
        [| RLet name $t $e $body |]
  (InfixE (Just a) (VarE arr) (Just (parseRaw' -> b))) | nameBase arr == "-->" -> do 
    tele <- parseReversedTelescope a 
    case tele of 
      Just tele -> go tele b where 
        go [] b = [| $b |]
        go ((x, t):xs) b = go xs [| RPi x $t $b|] 
      Nothing ->
        let a' = parseRaw' a in [| RPi "_" $a' $b|]
  _ -> let s = show e in [|s|]

parseId :: Exp -> Maybe String 
parseId = \case 
  VarE (nameBase -> x) -> pure x
  UnboundVarE (nameBase -> x) 
    | x /= "U" -> pure x
  ConE (nameBase -> x) 
    | x /= "U" -> pure x
  _ -> Nothing

parseTelescope1 :: Exp -> Q (Maybe (String, Q Exp))
parseTelescope1 = \case 
  (InfixE (Just x) (ConE i) (Just (parseRaw' -> t)))
    | nameBase i == ":" -> case parseId x of 
        Nothing -> pure Nothing
        Just x -> pure $ pure (x, t)
  _ -> pure Nothing

parseReversedTelescope :: Exp -> Q (Maybe [(String, Q Exp)])
parseReversedTelescope e = do 
  e' <- parseTelescope1 e 
  case e' of 
    Just t -> pure . pure . pure $ t
    Nothing -> case e of 
      AppE l r -> do
        l' <- parseReversedTelescope l
        r' <- parseTelescope1 r 
        pure $ do 
          l'' <- l'
          r'' <- r' 
          pure $ r'' : l''
      _ -> pure Nothing

-- def f : term
-- / patterns := term  
-- / patterns := term 

def = undefined

flattenApp :: Exp -> [Exp]
flattenApp = \case 
  AppE f x -> flattenApp f ++ [x]
  x -> [x]

parsePattern1 :: Exp -> Maybe RPattern 
parsePattern1 (flattenApp -> c:sp) = do
  c' <- parseId c 
  sp' <- mapM parsePattern1 sp
  pure $ RPat c' sp'

parsePatterns :: Exp -> Q [RPattern]
parsePatterns (flattenApp -> ps) = case mapM parsePattern1 ps of 
  Just ps -> pure ps 
  _ -> error $ "parse error in " ++ show ps
  

parseFunc' :: Exp -> Q (Maybe (String, Exp, [([RPattern], Exp)])) -- ^ Id, Type, Clauses
parseFunc' = \case 
    (InfixE (Just header) (VarE i) (Just cls)) | nameBase i == "/" -> do
      header' <- do_header header  
      case header' of
        Nothing -> pure Nothing
        Just (f_name, f_type) -> do 
          cls <- getClss cls 
          pure $ Just (f_name, f_type, cls)
    header -> do 
      header' <- do_header header  
      case header' of
        Nothing -> pure Nothing
        Just (f_name, f_type) -> do 
          pure $ Just (f_name, f_type, [])
  where 
    do_header (InfixE (Just (AppE (VarE (nameBase -> d)) f)) (ConE (nameBase -> i)) (Just t))
      | i == ":" && d == "def" = case parseId f of 
          Nothing -> error "expecting identifier."
          Just f -> do 
            t' <- parseRaw' t 
            pure $ Just(f, t')
    do_header _ = pure Nothing
    getCls :: Exp -> Q (Maybe ([RPattern], Exp))
    getCls (InfixE (Just ps) (ConE (nameBase -> i)) (Just rhs) ) 
      | i == ":=" = do 
        ps' <- parsePatterns ps 
        rhs' <- parseRaw' rhs
        pure . Just $  (ps', rhs')
    getCls _ = pure Nothing
    getClss :: Exp -> Q [([RPattern], Exp)]
    getClss = \case 
      (InfixE (Just this) (VarE (nameBase -> i)) (Just rest)) | i == "/" -> do 
        this' <- getCls this
        case this' of 
          Nothing -> error $ "expecting clause at: " ++ show this
          Just this' -> do
            rest' <- getClss rest
            pure $ this' : rest'
      e -> do 
        e' <- getCls e 
        case e' of 
          Just e' -> pure [e']
          Nothing -> error $ "expecting clause at: " ++ show e

makeFunc :: (String, Exp, [([RPattern], Exp)]) -> Q Exp 
makeFunc (f_name, f_type, cls) = 
  [| 
    RFuncDef f_name $(pure f_type) $(mkCls cls)
  |] 
  where
    mkCls :: [([RPattern], Exp)] -> Q Exp 
    mkCls = \case 
      [] -> [| [] |]
      (ps, rhs):rest -> 
        [| RClause ps $(pure rhs) : $(mkCls rest) |]

deriving instance Lift RPattern 

parseFunc :: Exp -> Q Exp 
parseFunc e = do 
  e' <- parseFunc' e
  case e' of 
    Nothing -> error "parse error."
    Just e' -> makeFunc e'