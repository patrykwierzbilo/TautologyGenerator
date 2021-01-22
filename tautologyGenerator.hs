data Prop =  Const Bool
  | Var Char
  | Not Prop
  | And Prop Prop
  | Or Prop Prop
  | Imply Prop Prop
  | Equi Prop Prop
  | Empty

instance Show Prop where
  show (Const v)   = show v
  show (Var c)     = show c
  show (Not p)     ="(~(" ++ show p ++ "))"
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

p1 :: Prop
p1 = And (Var 'p') (Not (Var 'p'))

p2 :: Prop
p2 = Imply (And (Var 'p') (Var 'q')) (Var 'p')

p3 :: Prop
p3 = Imply (Var 'p') (And (Var 'p') (Var 'q'))

p4 :: Prop
p4 = Imply (And (Var 'p') (Imply (Var 'p') (Var 'q'))) (Var 'q')
-- >(&(p)(>(p)(q)))(q)

p5 :: Prop
p5 = Equi (Or (Var 'p') (Var 'q')) (And (Var 'p') (Var 'q'))
-- #(|(p)(q))(&(p)(q))

p6 :: Prop
p6 = Equi (Or (Var 'p') (Var 'q')) (Not (And (Not (Var 'p')) (Not (Var 'q'))))
-- #(|(p)(q))(~&(~p)(~q))

string2Prop :: [Char] -> Prop
string2Prop (x:rest)   | x == 'p' = Var 'p'
                       | x == 'q' = Var 'q'
                       | x == '~' = Not (string2Prop rest)
                       | x == '&' = 
                         let (p, q) = splitArr rest
                         in And (string2Prop p) (string2Prop q)
                       | x == '|' = 
                         let (p, q) = splitArr rest
                         in Or (string2Prop p) (string2Prop q)
                       | x == '>' = 
                         let (p, q) = splitArr rest
                         in Imply (string2Prop p) (string2Prop q)
                       | x == '#' = 
                         let (p, q) = splitArr rest
                         in Equi (string2Prop p) (string2Prop q)

splitArr :: [Char] -> ([Char], [Char])
splitArr str =  split str False 0 [] []

split :: [Char] -> Bool -> Int ->[Char] ->[Char] -> ([Char], [Char])
split [] first n firstArr secArr =   (tail ( init (reverse firstArr)), tail ( init (reverse secArr)))
split (elem:list) True n firstArr secArr | elem == '(' = split list True (n + 1) firstArr (elem:secArr)
                                         | elem == ')' = split list True (n - 1) firstArr (elem:secArr)
                                         | otherwise   = split list True n firstArr (elem:secArr)
split (elem:list) False n firstArr secArr | elem == '(' = split list False (n + 1) (elem:firstArr) secArr
                                          | elem == ')' && n - 1 > 0 = split list False (n - 1) (elem:firstArr) secArr
                                          | elem == ')' && n - 1 == 0 = split list True (n - 1) (elem:firstArr) secArr
                                          | otherwise = split list False n (elem:firstArr) secArr

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

samples :: Int -> [a] -> [[a]]
samples 0 _ = [[]]
samples n xs = [ p : ps | p <- xs, ps <- samples (n - 1) xs]