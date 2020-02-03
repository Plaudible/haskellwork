module LFP where
-- version 3.1, Tue Mar  5 15:49:04 EST 2019
import State (Location)
-- import Test.QuickCheck hiding (Fun)
-- import Control.Monad

------------------------------------------------------------------------
-- Abstract syntax

data Expr = AConst Int | BConst Bool | Loc Location | Var String
          | ABin AOp Expr Expr | Compare COp Expr Expr 
          | Val Expr | Set Expr Expr | If Expr Expr Expr | Skip 
          | Seq Expr Expr | While Expr Expr
          | Fun String Expr | Let String Expr Expr | App Expr Expr 
--            deriving (Eq,Show)
            deriving (Eq)
               
data AOp  = Plus | Minus | Times 
--            deriving (Eq,Show)
            deriving (Eq)

data COp  = Eq | Neq | Lt | Leq | Gt | Geq
--            deriving (Eq,Show)
            deriving (Eq)

------------------------------------------------------------------------
-- Display

instance Show AOp  where show = showOp
instance Show COp  where show = showCop
instance Show Expr where show = showExpr
{--
--}

showOp :: AOp -> String
showOp Plus  = "+"
showOp Minus = "-"
showOp Times = "*"

showCop :: COp -> String
showCop Eq  = "=="
showCop Neq = "/="
showCop Lt  = "<"
showCop Leq = "<="
showCop Gt  = ">"
showCop Geq = ">="

showExpr :: Expr -> String
showExpr (AConst n)  
    = if n<0 then "("++show n++")" else show n
showExpr (Val e)     
    = "val(" ++ show e ++ ")"
showExpr (ABin iop e1 e2) 
    = "("++showOp iop ++ " " ++ showExpr e1 ++" "++showExpr e2++")"
showExpr (Compare cop e1 e2) 
    = "("++showCop cop ++ " " ++ showExpr e1 ++" "++showExpr e2++")"
showExpr (BConst b)  
    = if b then "tt" else "ff"
showExpr (Loc loc)   
    = 'X':show loc
showExpr Skip        
    = "skip"
showExpr (Set e1 e2) 
    = showExpr e1 ++ " := " ++ showExpr e2
showExpr (Seq e1 e2) 
    = "{ "++ show e1 ++ showRest e2 ++ " }"
      where showRest (Seq e1 e2) = "; "++showExpr e1++showRest e2
            showRest e           = "; "++showExpr e
showExpr (If e0 e1 e2) 
    = "if " ++ showExpr e0 ++ " then " ++ showExpr e1 ++ " else { "
      ++ showExpr e2 ++ " }"
showExpr (While e0 e1) 
    = "while " ++ showExpr e0 ++ " do " ++ showExpr e1
showExpr (Var x) 
    = x
showExpr (Fun x e) 
    = "(fn "++x++" => "++showExpr e++")"
showExpr (App e0 e1) 
    = "("++show op ++showArgs args++")"
      where 
        (op:args) = gather e0 [e1]
        gather (App e e') es = gather e (e':es)
        gather e es          = e:es
        showArgs es = concatMap (\e->' ':showExpr e) es
showExpr (Let x e0 e1) 
    = "let "++x++" = "++showExpr e0++" in "++showExpr e1
