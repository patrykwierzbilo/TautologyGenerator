data Prop =  Const Bool
  | Var Char
  | Not Prop
  | And Prop Prop
  | Or Prop Prop
  | Imply Prop Prop
  | Equi Prop Prop

instance Show Prop where
  show (Const v)   = show v
  show (Var c)     = show c
  show (Not p)     ="~(" ++ show p ++ ")"
  show (And p q)   = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (Or p q)    = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (Imply p q) = "(" ++ show p ++ " -> " ++ show q ++ ")"
  show (Equi p q)  = "(" ++ show p ++ " <-> " ++ show q ++ ")"

type Subst  =  Assoc Char Bool

type Assoc k v =  [(k,v)]

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
                         let (p, q, restOfList) = (head (tail subProps), head subProps, tail (tail subProps))
                         in string2Prop rest (And p q:restOfList)
                       | elem == '|' =
                         let (p, q, restOfList) = (head (tail subProps), head subProps, tail (tail subProps))
                         in string2Prop rest (Or p q:restOfList)
                       | elem == '>' =
                         let (p, q, restOfList) = (head (tail subProps), head subProps, tail (tail subProps))
                         in string2Prop rest (Imply p q:restOfList)
                       | elem == '#' =
                         let (p, q, restOfList) = (head (tail subProps), head subProps, tail (tail subProps))
                         in string2Prop rest (Equi p q:restOfList)

checkStr :: [Char] -> [Char] -> Bool
checkStr [] checkList = length checkList == 1
checkStr (elem:rest) checkList | elem == 'p' || elem == 'q' = checkStr rest (elem:checkList)
                               | elem == '~' = not (null checkList) && checkStr rest checkList
                               | elem == '&' || elem == '|' ||
                                 elem == '>' || elem == '#' = length checkList >= 2 && checkStr rest (tail checkList)

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

samples :: Int -> [a] -> [[a]]
samples 0 _ = [[]]
samples n xs = [ p : ps | p <- xs, ps <- samples (n - 1) xs]

unique :: Eq a => [a] -> [a]
unique [] = []
unique (x:xs) = x:unique (filter (x /=) xs)

genAllTaut :: Int -> [[Char]]
genAllTaut n = unique [props | y<- [1..n], z <- powerset "pq~&|>#", props <- filter (\q -> checkStr q [] && isTaut (string2Prop q [])) (samples y z)]

--cd Desktop/funkcyjne/projekt