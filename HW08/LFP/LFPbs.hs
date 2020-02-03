-- LFPbs.hs, last updated: Tue Mar 19 14:21:59 EDT 2019
-- Author(s): Maxwell Bockmann

import LFP
import LFPparser
import State
import Data.List   ((\\),nub,union,sort)
import Debug.Trace (trace)
import Test.HUnit  hiding (State)

fixMe place = error ("Fix me: "++ place)
------------------------------------------------------------------------
-- freeVars

-- (multiFreeVars [e1,e2,...,ek]) = the free vars in e1,...,ek.
multiFreeVars :: [Expr] -> [String]
multiFreeVars = nub . sort . (concatMap freeVars)

freeVars :: Expr -> [String]
-- Uncomment the following line to trace
-- freeVars e | trace ("FreeVars trace: "++ show e) False = undefined
freeVars (Val e)           = freeVars e
freeVars (ABin _ e1 e2)    = multiFreeVars [e1,e2]
freeVars (Compare _ e1 e2) = multiFreeVars [e1,e2]
freeVars (Set e1 e2)       = multiFreeVars [e1,e2]
freeVars (Seq e1 e2)       = multiFreeVars [e1,e2]
freeVars (While e1 e2)     = multiFreeVars [e1,e2]
freeVars (App e1 e2)       = multiFreeVars [e1,e2]
freeVars (If e0 e1 e2)     = multiFreeVars [e0,e1,e2]
freeVars (Var x)           = [x]
freeVars (Fun x e)         = [y | y <- freeVars e, y /= x]
freeVars (Let x e1 e2)     = [y | y <- multiFreeVars[e1,e2],y /= x]
-- the otherwise cases, these have no free vars.  So:
freeVars _                 = []

-- (fvs s) = the free vars of e, where e is the parse of s
fvs :: String -> [String]
fvs inp = multiFreeVars [ eparse inp ]

--fvTest :: String -> [String] -> IO ()
makefvTest inp vars
    = TestCase (assertEqual ("for (fvs "++inp++")") (fvs inp) (sort vars))

--                   test expr.               expected result
testfv1 = makefvTest "x"                      ["x"]
testfv2 = makefvTest "let x = y in (+ x y)"   ["y"]
testfv3 = makefvTest "((fn x => (+ x y)) y)"  ["y"]
testfv4 = makefvTest fv4                      ["x","p"]
testfv5 = makefvTest fv5                      []

fv4 = "((fn p => (p x)) (fn x => (+ x p)))"
fv5 = "let c = fn x => fn p => (p (* x x)) in "
      ++ " (let inc = fn x => (+ 1 x) in (c 4 inc))"


-- the printed output of the follow looks horrible inside of emacs
runFvAll =  runTestTT $ TestList [ "Test 1" ~: testfv1
                                 , "Test 2" ~: testfv2
                                 , "Test 3" ~: testfv3
                                 , "Test 4" ~: testfv4
                                 , "Test 5" ~: testfv5
                                 ]
------------------------------------------------------------------------
------------------------------------------------------------------------
-- fresh variables

-- strings = the infinite list of **all** Strings over lowercase letters.
--    Try (take 200 strings)
strings = "":[x:s | s <- strings , x <- ['a'..'z']]
-- (fresh ns) = a lower-case string not in the list ns
--    Try (fresh ["a","b","d","a","e"])
fresh names = head (strings \\ (nub  ("":names)))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Substitution

substTraceShow e x new
    = "  Subst trace: "++"e = "++show e++"   x = "++show x++
      "   new = "++show new

subst :: Expr -> String -> Expr -> Expr
-- Uncomment the following line to trace
-- subst e x new | trace (substTraceShow e x new) False = undefined
subst (Val e)             x new
    = Val (subst e x new)
subst (ABin op e1 e2)     x new
    = ABin op (subst e1 x new) (subst e2 x new)
subst (Compare cop e1 e2) x new
    = Compare cop (subst e1 x new) (subst e2 x new)
subst (Set e1 e2)         x new
    = Set (subst e1 x new) (subst e2 x new)
subst (Seq e1 e2)         x new
    = Seq (subst e1 x new) (subst e2 x new)
subst (While e1 e2)       x new
    = While (subst e1 x new) (subst e2 x new)
subst (App e1 e2)         x new
    = App (subst e1 x new) (subst e2 x new)
subst (If e0 e1 e2)       x new
    = If (subst e0 x new) (subst e1 x new) (subst e2 x new)
subst (Var y)             x new
     | x == y = new
     | otherwise = (Var y)
subst (Fun y e)           x new
     | x == y = (Fun y e)
     | otherwise = (Fun z e'')
     where
       z = fresh (union  (multiFreeVars [e,new]) [x])
       e' = subst e y (Var z)
       e'' = subst e' x  new
subst (Let y e0 e1)       x new
     | x == y = (Let y e0' e1)
     | otherwise = (Let z e0' e1'')
     where
           e0' = subst e0 x new
           z = fresh (union (multiFreeVars [e0,e1,new]) [x])
           e1' = subst e1 y (Var z)
           e1'' = subst e1' x new

      -- the otherwise case, nothing to replace
subst stuff               x new
    = stuff

------------------------------------------------------------------------
-- a helper function for testing subst
-- For example, once you have the Var-case working, try
--   (runSubst "x" "x" "(y w)")
runSubst :: String -> String -> String -> IO ()
runSubst e x new
    = do { putStrLn ("Computing: "++e++"["++ new ++"/"++x++"]")
         ; putStrLn ("result =   "++show (subst (eparse e) x (eparse new)))
         ; putStrLn ""
         }

-- Examples to test subst
st1 = runSubst "x" "x" "(y w)"
-- should produce: (y w)

st2 = runSubst "z" "x" "(y w)"
-- should produce: z

st3 = runSubst "(z x)" "x" "(y w)"
-- should produce: (z (y w))

st4 = runSubst "(fn x => z)" "x" "(y w)"
-- should produce: (fn x=>z)

st5 = runSubst "(fn t => z)" "x" "(y w)"
-- should produce: (fn a=>z)

st6 = runSubst "(fn t => x)" "x" "(y w)"
-- should produce: (fn a=>(y w))

st7 = runSubst "(fn y => (x y))" "x" "(y w)"
-- should produce: (fn a=>(y w a))

st8 = runSubst "(y (y z))" "x" "(z w)"
-- should produce: (y (y z))

st9 = runSubst "(fn u => fn w => (w x u))" "x" "(u w)"
-- should produce: (fn a => (fn c => (c (u w) a)))

st10 = runSubst "(fn a => fn b => (a (x b)))" "x" "(fn b => (a b))" -- FIXED
-- should produce: (fn b => (fn d => (b ((fn b => (a b)) d))))

st11 = runSubst "let x = (+ y x) in (+ y x)" "x" "3"
-- should produce: let x = (+ y 3) in (+ y x)

st12 = runSubst "(x 2 3)" "x" "fn y => fn z => (+ y z)"
-- should produce: ((fn y=>(fn z=>(+ y z))) 2 3)

st13 = runSubst "(x (+ 1 (let x = 4 in x)) (* 2 (let y = 3 in (x y z))))"
                "x"
                "fn y => fn z => (+ y z)"
-- should produce: ((fn y => (fn z => (+ y z)))
--                  (+ 1 let x = 4 in x)
--                  (* 2 let a = 3 in ((fn y => (fn z => (+ y z))) a z)))


runSubAll = do { st1; st2; st3; st4; st5; st6; st7; st8; st9; st10;
                 st11; st12; st13
               }

------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
-- Eval: a big step semantics for LFP

type Config = (Expr,State)

eval :: Config -> Config
-- Uncomment the following line to trace eval
-- eval (e,s) | trace ("Eval trace: "++(show e)) False = undefined
eval (AConst v,s)          = (AConst v,s)
eval (BConst v,s)          = (BConst v,s)
eval (Loc loc,s)           = (Loc loc,s)
eval (Skip,s)              = (Skip,s)
eval (Fun x e,s)           = (Fun x e,s)
eval (Val (Loc loc),s)     = (AConst (fetch s loc),s)
eval (ABin iop e1 e2,s)    = (AConst (aApply iop v1 v2),s'')
    where
      (AConst v1,s')  = eval (e1,s)
      (AConst v2,s'') = eval (e2,s')
eval (Compare cop e1 e2,s) = (BConst (bApply cop v1 v2),s'')
    where
      (AConst v1,s')  = eval (e1,s)
      (AConst v2,s'') = eval (e2,s')
eval (Set le ie,s)         = (Skip,set s' loc n)
    where (AConst n,s') = eval (ie,s)
          (Loc loc,s'') = eval (le,s')
eval (Seq cmd1 cmd2,s)     = (Skip,s2)
    where (Skip,s1) = eval (cmd1,s)
          (Skip,s2) = eval (cmd2,s1)
eval (If be cmd1 cmd2,s)   = eval (e,s')
    where (BConst v,s') = eval (be,s)
          e = if v then cmd1 else cmd2
eval (While be cmd,s)      = eval (cmd',s')
    where (BConst v,s') = eval (be,s)
          cmd' = if v then (Seq cmd (While be cmd)) else Skip
eval (Let x e0 e1,s)       = eval (App (Fun x e1) e0,s)
-- call by name application
eval (App e0 e1,s)         = eval (v,s'')
    where (Fun x e0', s') = eval (e0, s)
          (v, s'') = eval ((subst e0' x e1), s')

-- call by value application (fn x m,' s') = eval (m,s)
{-eval (App e0 e1,s)         = eval (v,s''')
    where (Fun x e0', s')  = eval (e0, s)
          (u,s'')          = eval (e1,s')
          (v,s''')         = eval ((subst e0' x u),s'')
-}
------------------------------------------------------------------------
------------------------------------------------------------------------
-- Utilities for eval

-- aApply iop n1 n2 = (n1 iop n2)
-- E.g., (aApply Plus 3 4) ~~> 7
aApply :: AOp -> Int -> Int -> Int
aApply Plus  n1 n2 = n1+n2
aApply Minus n1 n2 = n1-n2
aApply Times n1 n2 = n1*n2

-- bApply cop n1 n2 = (n1 cop n2)
-- E.g.:  (bApply Eq 3 4) ~~> False
-- E.g.:  (bApply Eq 3 3) ~~> True
bApply :: COp -> Int -> Int -> Bool
bApply Eq  v1 v2 = (v1==v2)
bApply Neq v1 v2 = (v1/=v2)
bApply Lt  v1 v2 = (v1<v2)
bApply Leq v1 v2 = (v1<=v2)
bApply Gt  v1 v2 = (v1>v2)
bApply Geq v1 v2 = (v1>=v2)

------------------------------------------------------------------------
-- runEval e
--   parses e, runs eval on the result in state4, and prints the answer
runEval :: String -> IO ()
runEval e = do { putStrLn ("Evaluating:\n    " ++ e)
               ; let (e',s') = eval (eparse e,state4)
               ; let ps = [(i,x) | (i,x) <- (dump s'), x /= 0]
               ; putStr "Result:\n    "
               ; putStrLn (show e')
               ; putStr "    "
               ; prnState s'
               ; putStrLn ""
               }

------------------------------------------------------------------------
-- Examples to test eval

-- 4! again.
et1 = runEval "{ X1 := 1; \
                \ while (> val(X0) 0) do { \
                \ X1 := (* val(X1) val(X0)); X0 := (- val(X0) 1) }}"
{- should have result:
    skip
    Locs(!=0): X[1]=24
-}

et2 = runEval "let x = 2 in (+ 10 x)"
{- Should have result:
    12
    Locs(!=0): X[0]=4
-}

et3 = runEval "let x = 10 in let y = (+ x 1) in let x = (- y 5) \
                \ in let y = (+ y 1) in (+ (* 100 x) y)"
{- Should have result:
    612
    Locs(!=0): X[0]=4
-}

et4 = runEval "(fn x => (+ x 2))"
{- (runEval e4) should have result:
    (fn x=>(+ x 2))
    Locs(!=0): X[0]=4
-}

et5 = runEval "((fn x => (+ x 2)) 19)"
{- (runEval e5) should have result:
    21
    Locs(!=0): X[0]=4
-}

et6 = runEval "let c = fn x => fn y => (+ x y) in (c 2 3)"
{- (runEval e6) should have result:
    5
    Locs(!=0): X[0]=4
-}
et7 = runEval "let c = fn x => fn p => (p (* x x)) \
      \ in (let inc = fn x => (+ 1 x) in (c 4 inc))"
{- (runEval e6) should have result:
    17
    Locs(!=0): X[0]=4
-}
et8 = runEval "let c = \
         \ fn x => { X1 := (* val(X1) val(X0)); X0 := (- val(X0) x) } in \
         \ { X1 := 1;  while (> val(X0) 0) do (c 1) }"
{- Should have result:
    skip
    Locs(!=0): X[1]=24
-}

et9 = runEval "let c = \
         \ fn x => { X1 := (* val(X1) val(X0)); X0 := (- val(X0) x) } in \
         \ { X1 := 1;  while (> val(X0) 0) do (c 2) }"
{- Should have result:
    skip
    Locs(!=0): X[1]=8
-}
et10 = runEval "let c = { X1 := (* val(X1) val(X0)) } in \
         \ { X1 := 1;  while (> val(X0) 0) do { c; X0 := (- val(X0) 1) }}"
{- Should have call-by-name result:
    skip
    Locs(!=0): X[1]=24

   Should have call-by-name result:
    skip
    Locs(!=0): X[1]=1
-}

-- runs all ten eval tests
runEvalAll = do { et1; et2; et3; et4; et5; et6; et7; et8; et9; et10}

------------------------------------------------------------------------
------------------------------------------------------------------------
