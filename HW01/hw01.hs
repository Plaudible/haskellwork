------------------------------------------------------------------------
-- Homework 1 CIS 352, Spring 2019, Version 1
-- Authors: Maxwell Bockmann
------------------------------------------------------------------------
import Data.Char
import Data.List          (nub)
import Test.QuickCheck
import Text.Printf hiding (toChar)
------------------------------------------------------------------------
pleaseFix = error "Please fix me!!"

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Problem 1: Distance

type Point = (Double,Double)

distance :: Point -> Point -> Double
distance (x1,y1) (x2,y2) = sqrt (((x1-x2)*(x1-x2))+((y1-y2)*(y1-y2))) --uses formula sqrt((x1-x2)^2+(y1-y2)^2)

-- sample function:
-- rotate a point 90 degrees counterclockwise around the origin
rotate90 :: Point -> Point
rotate90 (x,y) = (-y,x)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Problem 2: Testing for Vowels

-- isVowel ch = tests if ch is a lowercase vowel
--   Use `elem` (http://hackage.haskell.org/package/base-4.7.0.2/docs/Prelude.html#v:elem)
isVowel :: Char -> Bool
isVowel ch = ch == 'a' || ch == 'e' || ch == 'i' || ch == 'o' || ch == 'u' --if char is any of these chars, true

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Problem 3: Disemvoweling

-- disEmvowel str = the result of removing all lowercase vowels from str
disEmvowel :: String -> String
disEmvowel [] = [] --empty case
disEmvowel str = [x | x <- str, not(isVowel x)] --if next char is element of vowels, then discarded

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Problem 4:

-- smash str
--   = the result of removing all non-letters from str and
--     changing all uppercase letters to lowercase.
-- E.g.,  smash "Fee, Fie, Foe, and Fum!"
--     returns: "feefiefoefum"
-- Use a helper function if you want
smash :: String -> String
smash [] = [] --empty case
smash str = [toLower x | x <- str, (toLower(x) `elem` ['a'..'z'])] --toLowers entire string, if it's element of lowercase letters include, otherwise discard


------------------------------------------------------------------------
------------------------------------------------------------------------
-- toNum 'a' = 0, toNum 'b' = 1, ...., toNum 'z' = 25, toNum ch = -1 o/w.
toNum :: Char -> Int
toNum ch = if ('a'<=ch && ch <= 'z') then ord ch - ord 'a' else -1

------------------------------------------------------------------------
-- toChar 0 = 'a', toChar 1 = 'b', ...., toNum 25 = 'z', toNum n = '?' o/w.
toChar :: Int -> Char
toChar n = if (0<= n && n <= 25) then chr (n+ord 'a') else '?'

------------------------------------------------------------------------
-- Problem 5: Circular Shift Cipher

-- shift n str = the result of circularly shifting the letters in
--               (smash str)  n places.
-- E.g.,  shift 1  "abcxyz" returns "bcdyza"
-- E.g.,  shift 0  "abcxyz" returns "abcxyz"
-- E.g.,  shift 25 "abcxyz" returns "zabwxy"
-- You can use toNum, toChar, and mod. (There are other ways.)
-- Also use a helper function if you want.

shift :: Int -> String -> String
shift 0 str = smash str --no shift case
shift _ [] = [] -- empty list case
shift n str = [toChar((toNum(x)+n)`mod`26) | x <- smash str] --converts and modifies value with toNum/toChar, smashes str
--shift n (x:xs)
--   | n > 0  = toChar((toNum(smashChar(x))+n)`mod`25):shift n (smash(xs))
--   | n < 0  = shift (n + 1) (smash (x:xs))

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Problem 6: Capitization

capitalized :: String -> String
capitalized "" = "" --emptycase
capitalized (c:cs) = toUpper c: map toLower cs --first is capitalized, rest is mapped as lowercase

------------------------------------------------------------------------
-- Problem 7: Title

title :: [String] -> [String]
title [] = [] --empty case
title (first:rest) = capitalized first : [ if length x > 4 then capitalized x else x | x <- rest]
--logic: use cons for first item, then list comprehension for remaining.
--remaining - length > 4, capitalize else do not


------------------------------------------------------------------------
------------------------------------------------------------------------
------------------------------------------------------------------------
-- test properties

dist_prop :: Point -> Point -> Bool
dist_prop p1 p2
    = abs(distance p1 p2 - dist2 (toPolar p1) (toPolar p2)) < 0.0001
      where
        toPolar (x,y) = (sqrt(x*x+y*y),atan2 y x)
        dist2 (r1,theta1) (r2,theta2)
            = sqrt(r1*r1+r2*r2-2*r1*r2*cos(theta1-theta2))

-- nonsense words
--    Try: sample (arbitrary :: Gen Wrd)
newtype Wrd = Wrd String deriving (Show)
instance Arbitrary Wrd
    where arbitrary =
              do txt <- listOf $
                        frequency [(678,return 'a'), (123,return 'b'),
                                   (230,return 'c'), (352,return 'd'),
                                   (1055,return 'e'), (189,return 'f'),
                                   (167,return 'g'), (506,return 'h'),
                                   (577,return 'i'), (12,return 'j'),
                                   (63,return 'k'), (334,return 'l'),
                                   (200,return 'm'), (560,return 'n'),
                                   (624,return 'o'), (160,return 'p'),
                                   (7,return 'q'),   (495,return 'r'),
                                   (524,return 's'), (752,return 't'),
                                   (230,return 'u'), (81,return 'v'),
                                   (195,return 'w'), (12,return 'x'),
                                   (164,return 'y'), (5,return 'z')]
                 return (Wrd txt)

-- nonsense words with a trailing space or punctuation
--    Try: sample (arbitrary :: Gen Wrd2)
newtype Wrd2 = Wrd2 String deriving (Show)
instance Arbitrary Wrd2
    where arbitrary = do (Wrd txt) <- arbitrary
                         if (null txt)
                         then return (Wrd2 "")
                         else do trm <- (frequency [(7, return " "),
                                                    (1, return ", "),
                                                    (1, return ". "),
                                                    (1, return "! "),
                                                    (1, return "? ")])
                                 return (Wrd2 (txt++trm))

-- a string of nonsense words separated by spaces
--    Try: sample (arbitrary :: Gen Blither)
newtype Blither = Blither String deriving (Show)
instance Arbitrary Blither
    where arbitrary =
              do wrds <- listOf arbitrary
                 return (Blither (concat [cs++" " | (Wrd cs)<-wrds,
                                                    not (null cs)]))

-- a string of nonsense words separated by spaces and punctuation
--    Try: sample (arbitrary :: Gen Twaddle)
newtype Twaddle = Twaddle String deriving (Show)
instance Arbitrary Twaddle
    where arbitrary =
              do wrds <- listOf arbitrary
                 return (Twaddle (concat [cs | (Wrd2 cs) <- wrds,
                                               not (null cs) ]))

vowel_prop c = isVowel c == (p (ord c - ord 'a') == 0)
    where
      p x = x*(8960 + x*(-4448 + x*(720 + x*(-46 + x))))

disemv_prop (Twaddle cs)
    = disEmvowel cs == filter (`notElem` "aeiou") cs

isAsciiLetter c = isAscii c && isLetter c

smash_prop (Twaddle cs) = smash cs == concatMap foo cs
    where
      foo c = if isAsciiLetter c then (toLower c:[]) else []

shift1_prop key
    = length (nub (shift key "abcdefghijklmnopqrstuvwxyz")) == 26

shift2_prop key (Twaddle mess)
    = (shift (-key) (shift key mess)) == smash mess

shift3_prop key
    = (shift key base) == shifted
      where
        base    = "abcdefghijklmnopqrstuvwxyz"
        shifted = take 26 $ drop (key `mod` 26) $ cycle base

isCap wrd = null wrd || (isUpper (head wrd) && all isLower (tail wrd))

cap_prop (Wrd str) =  isCap (capitalized str')
    where
      str' = filter isAsciiLetter str

title_prop (Blither cs)
    = ws /= [] ==> isCap (head ws) && all ok (tail ws)
    where
        ws = title $ filter (not.null) $ map (filter isAsciiLetter) (words cs)
        ok wrd
            | length wrd <= 4 = all isLower wrd
            | otherwise       = isCap wrd

------------------------------------------------------------------------

tests :: [(String, IO ())]
tests = [ ("convert prop",     quickCheck dist_prop)
        , ("vowel prop",       quickCheck vowel_prop)
        , ("disemvowel prop",  quickCheck disemv_prop)
        , ("smash prop",       quickCheck smash_prop)
        , ("shift prop 1",     quickCheck shift1_prop)
        , ("shift prop 2",     quickCheck shift2_prop)
        , ("shift prop 3",     quickCheck shift3_prop)
        , ("capitalized prop", quickCheck cap_prop)
        , ("title prop",       quickCheck title_prop)
        ]

testRun = mapM_ (\(s,a) -> (printf "%-25s: " s) >> a) tests
