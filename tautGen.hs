import System.IO;
import System.Environment;

data Prop = Const Bool
  | Var Char
  | Not Prop
  | And Prop Prop
  | Or Prop Prop
  | Imply Prop Prop
  | Equi Prop Prop

instance Show Prop where
  show (Const v)   = show v
  show (Var c)     = [c]
  show (Not p) = "~"++ right
    where right = if rightNeedParen then "("++show p++")" else show p
          rightNeedParen = rightPrec <= opPrec
          rightPrec = priority p
          opPrec    = priority (Not p)
  show (And l r) = left ++"&"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = (leftPrec < opPrec)  || ((leftPrec == opPrec) && not (isAnd l))
          rightNeedParen = (rightPrec < opPrec ) || ((rightPrec == opPrec) && not (isAnd r))
          leftPrec  = priority l
          rightPrec = priority r
          opPrec    = priority (And l r)
  show (Or l r) = left ++"|"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = (leftPrec < opPrec) || ((leftPrec == opPrec) && not (isOr l))
          rightNeedParen = (rightPrec < opPrec) || ((rightPrec == opPrec) && not (isOr r))
          leftPrec  = priority l
          rightPrec = priority r
          opPrec    = priority (Or l r)
  show (Imply l r) = left ++">"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = leftPrec < opPrec || ((leftPrec == opPrec) && not (isImply l))
          rightNeedParen = rightPrec < opPrec || ((rightPrec == opPrec) && not (isImply r))
          leftPrec  = priority l
          rightPrec = priority r
          opPrec    = priority (Imply l r)
  show (Equi l r) = left ++"#"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = leftPrec < opPrec || ((leftPrec == opPrec) && not (isEqui l))
          rightNeedParen = rightPrec < opPrec || ((rightPrec == opPrec) && not (isEqui r))
          leftPrec  = priority l
          rightPrec = priority r
          opPrec    = priority (Equi l r)

isAnd :: Prop -> Bool
isAnd (And _ _) = True
isAnd _ = False

isOr :: Prop -> Bool
isOr (Or _ _) = True
isOr _ = False

isImply :: Prop -> Bool
isImply (Imply _ _) = True
isImply _ = False

isEqui :: Prop -> Bool
isEqui (Equi _ _) = True
isEqui _ = False

priority :: Prop -> Int
priority (Var _) = 3
priority (Not _) = 2
priority (Imply _ _) = 1
priority (Equi _ _) = 1
priority (And _ _) = 1
priority (Or _ _) = 1

type Substitution = Pair Char Bool

type Pair var value = [(var,value)]

find :: Eq k => k -> Pair k v -> v
find k t =  head [v | (k',v) <- t, k == k']

evaluate :: Substitution -> Prop -> Bool
evaluate _ (Const b)   =  b
evaluate s (Var x)     =  find x s
evaluate s (Not p)     =  not (evaluate s p)
evaluate s (And p q)   =  evaluate s p && evaluate s q
evaluate s (Or p q)    =  evaluate s p || evaluate s q
evaluate s (Imply p q) =  evaluate s p <= evaluate s q
evaluate s (Equi p q)  =  evaluate s p == evaluate s q

variables :: Prop -> [Char]
variables (Const _)   = []
variables (Var x)     = [x]
variables (Not p)     = variables p
variables (And p q)   = variables p ++ variables q
variables (Or p q)    = variables p ++ variables q
variables (Imply p q) = variables p ++ variables q
variables (Equi p q)  = variables p ++ variables q

bools :: Int -> [[Bool]]
bools 0 =  [[]]
bools n =  map (False:) bss ++ map (True:) bss
            where bss = bools (n-1)

removeDuplicates :: Eq a => [a] -> [a]
removeDuplicates [] =  []
removeDuplicates (x:xs) =  x : removeDuplicates (filter (/= x) xs)

substs :: Prop -> [Substitution]
substs p =  map (zip vars) (bools (length vars))
                                 where vars = removeDuplicates (variables p)

isTautology :: Prop -> Bool
isTautology p =  and [evaluate s p | s <- substs p]

string2Prop :: [Char] -> [Prop] -> Prop
string2Prop [] subProps = head subProps
string2Prop (elem:rest) subProps 
                       | elem == 'p' || elem == 'q' = string2Prop rest (Var elem:subProps)
                       | elem == '~' =
                         let (var, restOfList) = (head subProps, tail subProps)
                         in string2Prop rest (Not var:restOfList)
                       | elem == '&' =
                         let (p, q, restOfList) = getElemsStackAndPop subProps
                         in string2Prop rest (And p q:restOfList)
                       | elem == '|' =
                         let (p, q, restOfList) = getElemsStackAndPop subProps
                         in string2Prop rest (Or p q:restOfList)
                       | elem == '>' =
                         let (p, q, restOfList) = getElemsStackAndPop subProps
                         in string2Prop rest (Imply p q:restOfList)
                       | elem == '#' =
                         let (p, q, restOfList) = getElemsStackAndPop subProps
                         in string2Prop rest (Equi p q:restOfList)

getElemsStackAndPop :: [Prop] -> (Prop, Prop, [Prop])
getElemsStackAndPop stack = (head (tail stack), head stack, tail (tail stack))

checkStr :: [Char] -> [Char] -> Bool
checkStr [] checkList = length checkList == 1
checkStr (elem:rest) checkList | elem == 'p' || elem == 'q' = checkStr rest (elem:checkList)
                               | elem == '~' = not (null checkList) && checkStr rest checkList
                               | elem == '&' || elem == '|' ||
                                 elem == '>' || elem == '#' = length checkList >= 2 && checkStr rest (tail checkList)

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

--complexity = length list ^ n
samples :: Int -> [a] -> [[a]]
samples 0 _ = [[]]
samples n xs = [ p : ps | p <- xs, ps <- samples (n - 1) xs]

changeVar :: [Char] -> [Char]
changeVar [] = []
changeVar (elem:rest) | elem == 'p' = 'q' : changeVar rest 
                      | elem == 'q' = 'p' : changeVar rest
                      | otherwise  = elem : changeVar rest

unique :: [[Char]] -> [[Char]]
unique [] = []
unique (x:xs) = x:unique (filter (\elem -> x /= elem && elem /= changeVar x) xs)

genTaut :: Int-> [[Char]]
genTaut n = unique [props | y<- [1..n], 
                            z <- powerset "pq~&|>#", --genPowerset 
                            props <- filter (\q -> checkStr q [] && isTautology (string2Prop q [])) (samples y z)]

uniqueProps :: [Prop] -> [Prop]
uniqueProps [] = []
uniqueProps (x:xs) = x:uniqueProps (filter (\elem -> show x /= show elem) xs)

gen :: [[Char]] -> [Prop] -> Int -> [Prop]
gen [] list n = uniqueProps list
gen (x:rest) list n = let prop = string2Prop x []
                      in if length (show prop) <= n
                           then 
                             gen rest (list ++ [prop]) n
                         else
                             gen rest list n       

genAllTaut :: Int -> Handle -> IO()
genAllTaut n file = do
                     mapM_ (hPrint file) (gen (genTaut n) [] n)

main :: IO ()
main = do
           (firstArg:secArg:_) <-getArgs
           fileHandle <- openFile secArg WriteMode
           let n = read firstArg :: Int
           genAllTaut n fileHandle
           hClose fileHandle
           putStrLn $ "Generation completed for n = " ++ show n