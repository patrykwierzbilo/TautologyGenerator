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
          rightPrec = precedence p
          opPrec    = precedence (Not p) --bylo Var 'c'
  show (And l r) = left ++"&"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = (leftPrec < opPrec)  || ((leftPrec == opPrec) && not (isAnd l))
          rightNeedParen = (rightPrec < opPrec ) || ((rightPrec == opPrec) && not (isAnd r))
          leftPrec  = precedence l
          rightPrec = precedence r
          opPrec    = precedence (And l r)
  show (Or l r) = left ++"|"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = (leftPrec < opPrec) || ((leftPrec == opPrec) && not (isOr l))
          rightNeedParen = (rightPrec < opPrec) || ((rightPrec == opPrec) && not (isOr r))
          leftPrec  = precedence l
          rightPrec = precedence r
          opPrec    = precedence (Or l r)
  show (Imply l r) = left ++">"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = leftPrec < opPrec || ((leftPrec == opPrec) && not (isImply l))
          rightNeedParen = rightPrec < opPrec || ((rightPrec == opPrec) && not (isImply r))
          leftPrec  = precedence l
          rightPrec = precedence r
          opPrec    = precedence (Imply l r)
  show (Equi l r) = left ++"#"++ right
    where left  = if leftNeedParen then "(" ++ show l ++ ")" else show l
          right = if rightNeedParen then "(" ++ show r ++ ")" else show r
          leftNeedParen = leftPrec < opPrec || ((leftPrec == opPrec) && not (isEqui l))
          rightNeedParen = rightPrec < opPrec || ((rightPrec == opPrec) && not (isEqui r))
          leftPrec  = precedence l
          rightPrec = precedence r
          opPrec    = precedence (Equi l r)

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

precedence :: Prop -> Int
precedence (Var _) = 3
precedence (Not _) = 2
precedence (Imply _ _) = 1
precedence (Equi _ _) = 1
precedence (And _ _) = 1
precedence (Or _ _) = 1

type Subst = Assoc Char Bool

type Assoc k v = [(k,v)]

find :: Eq k => k -> Assoc k v -> v
find k t =  head [v | (k',v) <- t, k == k']

eval :: Subst -> Prop -> Bool
eval _ (Const b)   =  b
eval s (Var x)     =  find x s
eval s (Not p)     =  not (eval s p)
eval s (And p q)   =  eval s p && eval s q
eval s (Or p q)    =  eval s p || eval s q
eval s (Imply p q) =  eval s p <= eval s q
eval s (Equi p q)  =  eval s p == eval s q

vars :: Prop -> [Char]
vars (Const _)   = []
vars (Var x)     = [x]
vars (Not p)     = vars p
vars (And p q)   = vars p ++ vars q
vars (Or p q)    = vars p ++ vars q
vars (Imply p q) = vars p ++ vars q
vars (Equi p q)  = vars p ++ vars q

bools :: Int -> [[Bool]]
bools 0 =  [[]]
bools n =  map (False:) bss ++ map (True:) bss
            where bss = bools (n-1)

rmdups :: Eq a => [a] -> [a]
rmdups [] =  []
rmdups (x:xs) =  x : rmdups (filter (/= x) xs)

substs :: Prop -> [Subst]
substs p =  map (zip vs) (bools (length vs))
                                 where vs = rmdups (vars p)

isTaut :: Prop -> Bool
isTaut p =  and [eval s p | s <- substs p]

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

checkset :: [Char] -> Int -> Int -> Int -> Bool
checkset [] operandp operandq operators =  operandp + operandq <= operators + 1 && ((operandq > 0 && operandp > 0) || (operandq == 0 && operandp > 0))
checkset (elem:rest) operandp operandq operators | elem == 'p' = checkset rest (operandp + 1) operandq operators
                                                 | elem == 'q' = checkset rest operandp (operandq + 1) operators
                                                 | elem == '~' = checkset rest operandp operandq operators
                                                 | elem == '&' || elem == '|' ||
                                                   elem == '>' || elem == '#' = checkset rest operandp operandq (operators + 1)

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

genPowerset :: [[Char]]
genPowerset = reverse [l | l <- powerset "pq~&|>#", checkset l 0 0 0]

samples :: Int -> [a] -> [[a]]
samples 0 _ = [[]]
samples n xs = [ p : ps | p <- xs, ps <- samples (n - 1) xs]

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) = x:unique (filter (x /=) xs)

genTaut :: Int-> [[Char]]
genTaut n = unique [props | y<- [1..n], z <- powerset "pq~&|>#", props <- filter (\q -> checkStr q [] && isTaut (string2Prop q [])) (samples y z)]

genAllTaut :: Int -> Handle -> IO()
genAllTaut n file = do
                     mapM (\x -> hPutStrLn file (show x)) (gen (genTaut n) [] n)
                     return ()

gen :: [[Char]] -> [Prop] -> Int -> [Prop]
gen [] list n = list
gen (x:rest) list n = let prop = string2Prop x []
                      in if length (show prop) <= n
                           then 
                             gen rest (list ++ [prop]) n
                         else
                             gen rest list n       

main :: IO ()
main = do
           (firstArg:secArg:_) <-getArgs
           fileHandle <- openFile secArg WriteMode
           let n = read firstArg :: Int
           genAllTaut n fileHandle
           hClose fileHandle
           putStrLn "Generation completed"

--cd Desktop/funkcyjne/projekt