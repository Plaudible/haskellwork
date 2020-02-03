-----------------------------------------------------------------------
-- Written by: Maxwell Bockmann (Whoops, I remembered my name. Please add 5 points :) )
------------------------------------------------------------------------
-- Homework 3, Part I
-- Propositional logic, based on an example of W. Heijltjes & P. Wadler

import Control.Monad( liftM, liftM2 )
import Text.ParserCombinators.ReadP
import Data.List( nub, sort )
import Test.HUnit
import Test.QuickCheck( quickCheck, sample,
                        Arbitrary( arbitrary ), Gen,
                        oneof, elements, sized  )


-- The datatype 'Prop'

type Name = String
data Prop = Var Name
          | F
          | T
          | Not Prop
          | Prop :|: Prop
          | Prop :&: Prop
          | Prop :->: Prop
          | Prop :<->: Prop
          deriving (Eq, Ord, Show)
          -- deriving (Eq, Ord)

-- instance Show Prop where show  =  showProp

-- turns a Prop into a string approximating mathematical notation
showProp :: Prop -> String

showProp (Var x)     = x
showProp (F)         = "F"
showProp (T)         = "T"
showProp (Not p)     = "(~" ++ showProp p ++ ")"
showProp (p :|: q)   = "("  ++ showProp p ++ "|" ++ showProp q ++ ")"
showProp (p :&: q)   = "("  ++ showProp p ++ "&" ++ showProp q ++ ")"
showProp (p :->: q)  = "("  ++ showProp p ++ "->" ++ showProp q ++ ")"
showProp (p :<->: q) = "("  ++ showProp p ++ "<->" ++ showProp q ++ ")"

-- some samples
vp, vq, vr, p1, p2, p3 :: Prop
vp = Var "P"
vq = Var "Q"
vr = Var "R"
p1 = ((vp :|: vq) :&: (vp :&: vq))
p2 = ((vp :|: vq) :&: ((Not vp) :&: (Not vq)))
p3 = ((vp :&: (vq :|: vr))
      :&: (((Not vp) :|: (Not vq)) :&: ((Not vp) :|: (Not vr))))

type Names = [Name]
type Env = [(Name, Bool)]

lookUp :: Name -> Env -> Bool
lookUp x env = case (lookup x env) of
                 (Just b) -> b
                 Nothing  -> False

-- evaluates a proposition in a given environment
eval :: Env -> Prop -> Bool
eval e (Var x)     = lookUp x e
eval e (F)         = False
eval e (T)         = True
eval e (Not p)     = not (eval e p)
eval e (p :|: q)   = eval e p || eval e q
eval e (p :&: q)   = eval e p && eval e q
eval e (p :->: q)  = (not (eval e p)) || eval e q
eval e (p :<->: q) = eval e p == eval e q


------------------------------------------------------------------------
-- names p = a list of all the names in p (with no reps)
names :: Prop -> Names
names (Var x)       = [x]
names (F)           = []
names (T)           = []
names (Not p)       = names p
names (p :|: q)     = nub (names p ++ names q)
names (p :&: q)     = nub (names p ++ names q)
names (p :->: q)    = nub (names p ++ names q)
names (p :<->: q)   = nub (names p ++ names q)

-- envs [n1,...,nk] = a list of all possible environments for these names.
-- E.g.:
envs :: Names -> [Env]
envs []     = [[]]
envs [x]    = [[(x,True)],[(x,False)]]
envs (x:xs) = [(x,True):t | t <- ts] ++ [(x,False):t | t <- ts]
    where
      ts = envs xs

satisfiable :: Prop -> Bool
satisfiable p = or [eval e p| e <- envs(names p)]

tautology :: Prop -> Bool
tautology p =  and [eval e p| e <- envs(names p)]

equivalent, equivalent' :: Prop -> Prop -> Bool
equivalent p q = and [eval e p == eval e q | e <- envs theNames]
    where theNames = nub (names p ++ names q)

equivalent' p q = tautology (p :<->: q)

equiv1_prop :: Prop -> Prop -> Bool
equiv1_prop p q = (equivalent p q == equivalent' p q)

equiv2_prop :: Prop -> Bool
equiv2_prop p = (equivalent p p) && (equivalent' p p)

subformulas :: Prop -> [Prop]
subformulas (Var x)     =  [Var x]
subformulas (F)         =  [F]
subformulas (T)         =  [T]
subformulas (Not p)     =  (Not p):subformulas p
subformulas (p :|: q)   =  (p :|: q):nub (subformulas p ++ subformulas q)
subformulas (p :&: q)   =  (p :&: q):nub (subformulas p ++ subformulas q)
subformulas (p :->: q)  =  (p :->: q):nub (subformulas p ++ subformulas q)
subformulas (p :<->: q) =  (p :<->: q):nub (subformulas p ++ subformulas q)

pleaseFix = error "Please fix me."

------------------------------------------------------------------------
-- Problem 1 -----------------------------------------------------------

isSimple :: Prop -> Bool
isSimple (_ :->: _)  = False
isSimple (_ :<->: _) = False
isSimple (Not p)     = (isSimple p)
isSimple (p :|: q)   = (isSimple p) && (isSimple q)
isSimple (p :&: q)   = (isSimple p) && (isSimple q)
isSimple (F)           = True
isSimple (T)           = True
isSimple (Var x)       = True

------------------------------------------------------------------------
-- Problem 2 -----------------------------------------------------------

simplify :: Prop -> Prop
simplify (p :->: q)    = ((Not (simplify p)) :|: (simplify q))
simplify (p :<->: q)   = (((simplify p) :&: (simplify q)) :|: ((Not (simplify p)) :&: (Not (simplify q))))
simplify (p :|: q)     = (simplify p :|: simplify q)
simplify (p :&: q)     = (simplify p :&: simplify q)
simplify (F)           = (F)
simplify (T)           = (T)
simplify (Var x)       = (Var x)
simplify (Not p)       = (Not (simplify p))


-- Testing for Problems 1 and 2 ----------------------------------------

-- QuickCheck properties
simp1_prop, simp2_prop :: Prop -> Bool
simp1_prop p = isSimple (simplify p)      -- see if (simplify p) is simple
simp2_prop p = equivalent p (simplify p)  -- see if: p <-> (simplify p)
-- HUnit tests for isSimple and simplify
-- You can run these tests by evaluating:
--    runTestTT testsSimp
-- To run just testSimp2, evaluate:
--    runTestTT testSimp2

testSimp1
    = TestCase (assertEqual ("simplify "++s1++",")
                            ((Not (Var "P")) :|: (Var "Q"))
                            (simplify q1) )
q1 = ((Var "P") :->: (Var "Q"))
s1 = "((Var \"P\") :->: (Var \"Q\"))"

testSimp2
    = TestCase (assertEqual ("simplify "++s2++",")
                ((Var "P" :&: Var "Q") :|: (Not (Var "P") :&: Not (Var "Q")))
                (simplify q2) )
q2 = ((Var "P" :&: Var "Q") :|: (Not (Var "P") :&: Not (Var "Q")))
s2 = "(Var \"P\" :&: Var \"Q\") :|: (Not (Var \"P\") :&: Not (Var \"Q\"))"

testSimp3
    = TestCase (assertEqual
                ("("++s1++":|:"++s2++",")
                ((Not (Var "P") :|: Var "Q") :|:
                 ((Var "P" :&: Var "Q") :|: (Not (Var "P") :&: Not (Var "Q"))))
                (simplify (q1 :|: q2))
               )
testsSimp = TestList [ TestLabel "testSimp1" testSimp1
                     , TestLabel "testSimp2" testSimp2
                     , TestLabel "testSimp3" testSimp3
                     ]

------------------------------------------------------------------------
-- Problem 3 -----------------------------------------------------------
isNNF :: Prop -> Bool
isNNF (_ :->: _)       = False
isNNF (Not(Not p))     = False
isNNF (Not(_ :&: _))   = False
isNNF (Not(_ :<->: _)) = False
isNNF (Not(_ :|: _))   = False
isNNF (Not(T))         = False
isNNF (Not(F))         = False
isNNF (p :<->: q)      = (isNNF p) && (isNNF q)
isNNF (p :|: q)        = (isNNF p) && (isNNF q)
isNNF (p :&: q)        = (isNNF p) && (isNNF q)
isNNF _                = True

------------------------------------------------------------------------
-- Problem 4 -----------------------------------------------------------
toNNF :: Prop -> Prop
toNNF (p :->: q)     = (simplify((toNNF p) :->: (toNNF q)))
toNNF (p :<->: q)    = (simplify((toNNF p) :<->: (toNNF q)))
toNNF (Not(Not p))   = (toNNF p)
toNNF (Not(p :&: q)) = ((Not(toNNF p)):|:(Not(toNNF q)))
toNNF (Not(p :|: q)) = ((Not(toNNF p)):&:(Not(toNNF q)))
toNNF (p :|: q)      = ((toNNF p) :|: (toNNF q))
toNNF (p :&: q)      = ((toNNF p) :&: (toNNF q))
toNNF (Not F)        = (T)
toNNF (Not T)        = (F)
toNNF (T)            = (T)
toNNF (F)            = (F)
toNNF (Var x)        = (Var x)
toNNF (Not p)        = (Not (toNNF p))

-- Testing for Problems 3 and 4 ----------------------------------------

-- QuickCheck properties for isNNF and toNNF

nnf1_prop, nnf2_prop :: Prop -> Bool
nnf1_prop p = isNNF (toNNF p)        -- see if (toNNF p) is in NNF
nnf2_prop p = equivalent p (toNNF p) -- see if (toNNF p) <-> p


-- HUnit tests for toNNF
-- You can run these tests by evaluating:
--    runTestTT testsNNF
-- To run just testNNF5, evaluate:
--    runTestTT testNNF5

nnfCheck p
    = TestCase (do let q = toNNF p
                   assertBool ("toNNF "++(show p)++" not equiv to "++ (show p))
                              (equivalent p q)
                   assertBool ("toNNF "++(show p)++" not in NNF")
                              (isNNF q))

testNNF1 = TestCase (assertEqual
                     "toNNF (Not T),"
                     F
                     (toNNF (Not T))
                    )
testNNF2 = TestCase (assertEqual
                     "toNNF (Not F),"
                     T
                     (toNNF (Not F))
                    )
testNNF3 = TestCase (assertEqual
                     "toNNF (Not (Not (Not vp))),"
                     (Not vp)
                     (toNNF (Not (Not (Not vp))))
                    )
testNNF4 = TestCase (assertEqual
                     "toNNF (Not (Not (Not (Not vp)))),"
                     vp
                     (toNNF (Not (Not (Not (Not vp)))))
                    )
testNNF5 = nnfCheck ((Not vp) :<->: (Not vq))

testsNNF = TestList [ TestLabel "testNNF1" testNNF1
                    , TestLabel "testNNF2" testNNF2
                    , TestLabel "testNNF3" testNNF3
                    , TestLabel "testNNF4" testNNF4
                    , TestLabel "testNNF5" testNNF5
                    ]

-- You can run these tests by evaluating:
--    runTestTT testsNNF
-- To run just testNNF5, evaluate:
--    runTestTT testNNF5




--------------------------------------------------------------------------
-- The following is lifted from the Univ. of Edinburg --------------------
--------------------------------------------------------------------------

-- For QuickCheck --------------------------------------------------------

instance Arbitrary Prop where
    arbitrary  =  sized prop
        where
          prop n | n <= 0     =  atom
                 | otherwise  =  oneof [ atom
                                       , liftM Not subform
                                       , liftM2 (:|:) subform subform
                                       , liftM2 (:&:) subform subform
                                       , liftM2 (:->:) subform subform
                                       , liftM2 (:<->:) subform' subform'
                                       ]
                 where
                   atom = oneof [liftM Var (elements ["P", "Q", "R", "S"]),
                                   elements [F,T]]
                   subform  =  prop (n `div` 2)
                   subform' =  prop (n `div` 4)

{- To see what kind of propositions are generated, try:
   sample (arbitrary :: Gen Prop)
-}
------------------------------------------------------------------------
-- For Drawing Tables ----------------------------------------------------

-- centre a string in a field of a given width
centre :: Int -> String -> String
centre w s  =  replicate h ' ' ++ s ++ replicate (w-n-h) ' '
    where
      n = length s
      h = (w - n) `div` 2

-- make a string of dashes as long as the given string
dash :: String -> String
dash s  =  replicate (length s) '-'

-- convert boolean to T or F
fort :: Bool -> String
fort False  =  "F"
fort True   =  "T"

-- print a table with columns neatly centred
-- assumes that strings in first row are longer than any others
showTable :: [[String]] -> IO ()
showTable tab  =  putStrLn (
  unlines [ unwords (zipWith centre widths row) | row <- tab ] )
    where
      widths  = map length (head tab)

table p = tables [p]

tables :: [Prop] -> IO ()
tables ps  =
  let xs = nub (concatMap names ps) in
    showTable (
      [ xs            ++ ["|"] ++ [showProp p | p <- ps]           ] ++
      [ dashvars xs   ++ ["|"] ++ [dash (showProp p) | p <- ps ]   ] ++
      [ evalvars e xs ++ ["|"] ++ [fort (eval e p) | p <- ps ] | e <- envs xs]
    )
    where  dashvars xs        =  [ dash x | x <- xs ]
           evalvars e xs      =  [ fort (eval e (Var x)) | x <- xs ]

-- print a truth table, including columns for subformulas
fullTable :: Prop -> IO ()
fullTable = tables . filter nontrivial . subformulas
    where nontrivial :: Prop -> Bool
          nontrivial (Var _) = False
          nontrivial T       = False
          nontrivial F       = False
          nontrivial _       = True





------------------------------------------------------------------------
------------------------------------------------------------------------
-- Part II
------------------------------------------------------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Problem 5 -----------------------------------------------------------
same :: [Int] -> Bool
same xs = (null xs) || and (zipWith (==) xs (tail xs))

------------------------------------------------------------------------
-- Problem 6 -----------------------------------------------------------
squash, squash' :: (a->a->b) -> [a] -> [b]
squash f []        = []
squash f [x]       = []
squash f (x1:x2:xs) = (f x1 x2) : (squash f (xs))

squash' f []        = []
squash' f [x]       = []
squash' f (a:xs) = (zipWith f (a:xs) (xs))

squash_prop xs = (squash (+) xs == squash' (+) xs)
------------------------------------------------------------------------
-- Problem 7 -----------------------------------------------------------

pipeline :: [a -> a] -> [a] -> [a]
pipeline = pleaseFix
