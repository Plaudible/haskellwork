module LFPparser where
-- Version 3.1, Tue Mar  5 15:49:04 EST 2019

import LFP
-- import qualified Text.ParserCombinators.ReadP as R
import Text.ParserCombinators.ReadP
import Data.Char (isDigit,isSpace,isLower)
import Data.Maybe (listToMaybe)    
-- import Test.QuickCheck hiding (Fun)



{- THE GRAMMAR:
   Expr ::= Num | tt | ff | (AOp Expr Expr) | (COp Expr Expr)
          | if Expr then Expr else Expr | while Expr do Expr 
          | skip | { Expr (; Expr)^* } | val(LExp) | LExp := Expr
          | Var | fn Var => Expr |let Var = Expr in Expr | (Expr Expr^+)     

   LExp   ::= X0 | X1 | X2 | ...
   AOp    ::= + | - | *  
   COp    ::= == | /= | < | <= | > | >= 
   Var    ::= (a|...|z)^+
-}

---------------------------------------------------------------------------
-- The parser
---------------------------------------------------------------------------
-- utilities 

run :: ReadP a -> String -> [(a,String)]
run        = readP_to_S
      
full :: ReadP a -> String -> Maybe a
full p inp = listToMaybe [ x | (x,"") <- run p inp]

token :: ReadP a -> ReadP a
token p    = do { result <- p ; skipSpaces ; return result }

symbol :: String -> ReadP String
symbol sym = token (string sym)

identifier :: ReadP String
identifier = token (munch1 isLower)

parens :: ReadP a -> ReadP a
parens p   = between (symbol "(") (symbol ")") p 

braces :: ReadP a -> ReadP a
braces p   = between (symbol "{") (symbol "}") p 

natural :: ReadP Int
natural    = do { ds <- token(munch1 isDigit) ; return (read ds :: Int) }

integer :: ReadP Int
integer    = do { char '-'; n <- natural; return (-n) } +++ natural

semiSep :: ReadP a -> ReadP [a]
semiSep p  = sepBy p (symbol ";")

-- locations
location   = do { (char 'X'); n <- natural; return $ Loc (fromIntegral n) }

-- variables
varExp     = do { x <- identifier; return $ Var x }

-- expressions
expr       = choice [ numExp, ttExp,    ffExp,    valExp,  assgnExp, 
                      ifExp,  skipExp,  whileExp, seqExp,  lamExp,
                      aExp,   bExp,     letExp,   appExp,  varExp
                    ]

numExp     = do { n <- integer;  return $ AConst (fromIntegral n) }
ttExp      = do { symbol "tt"; return (BConst True) }
ffExp      = do { symbol "ff"; return (BConst False) }
valExp     = do { symbol "val"
                ; loc <- parens(location)
                ; return $ Val loc 
                }

assgnExp   = do { n <- location
                ; symbol ":="
                ; rhs <- expr 
                ; return $ Set n rhs
                }

ifExp      = do { symbol "if"
                ; tst    <- expr
                ; symbol "then"
                ; thenExp <- expr
                ; symbol "else"
                ; elseExp <- expr
                ; return $ If tst thenExp elseExp
                }

skipExp    = do { symbol "skip" ; return Skip }

whileExp   = do { symbol "while"
                ; tst  <- expr
                ; symbol "do"
                ; body <- expr
                ; return $ While tst body
                }

seqExp     = do { ss <- braces(semiSep expr)
                ; if null ss then return Skip else return $ foldr1 Seq ss 
                }

aExp       = parens aexp
    where  aexp = do { op <- iopExp
                     ; e1 <- expr
                     ; e2 <- expr
                     ; return $ ABin op e1 e2
                     }

iopExp      = choice [ oper "+" Plus, oper "-" Minus, oper "*" Times]
    where oper str op = do { symbol str; return op }

bExp       = parens bexp
    where bexp = do { op <- copExp
                    ; e1 <- expr
                    ; e2 <- expr
                    ; return $ Compare op e1 e2
                    }

copExp     = choice [ coper "==" Eq  , coper "/=" Neq , 
                      coper "<=" Leq , coper ">=" Geq , 
                      coper "<" Lt   , coper ">" Gt   ]   
    where coper st op = do { symbol st; return op }


appExp     =  do { es <- parens(many1 expr)
                 ; case es of 
                     [e] -> return e
                     es' -> return $ foldl1 App es'
                 }

lamExp     = do { symbol "fn"
                ; x <- identifier
                ; symbol "=>"
                ; body <- expr
                ; return $ Fun x body
                }

letExp      = do { symbol "let"
                 ; x  <- identifier
                 ; symbol "="
                 ; e0 <- expr
                 ; symbol "in"
                 ; e1 <- expr
                 ; return $ Let x e0 e1
                 }

---------------------------------------------------------------------------
-- top level function

-- (eparse inp) = the parse of an LFC expression
eparse inp = case (full (do { skipSpaces; expr}) inp) of
               Nothing     -> error ("Failed to parse " ++ inp)
               Just result -> result

---------------------------------------------------------------------------

-- a test expression, try: eparse e
e =  "let c = \
         \ fn x => { X1 := (* val(X1) val(X0)); X0 := (- val(X0) x) } in \
         \ { X1 := 1;  while (> val(X0) 0) do (c 1) }"
