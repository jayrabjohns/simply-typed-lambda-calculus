

------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


------------------------- Assignment 1: Simple types

data Type = 
    Base 
  | (:->) Type Type
  deriving Eq

-- {
nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice (   a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type where
  show = nice

type1 :: Type
type1 =  Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)
-- }

-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var Type Term
  | Apply    Term Term

--{

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable   x) = x
      f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m 
      f i (Apply    n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty

--}

-- - - - - - - - - - - -- Numerals

--{
numeral :: Int -> Term
numeral i = Lambda "f" (Base :-> Base) (Lambda "x" (Base) (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))
--}

--{
sucterm :: Term
sucterm =
    Lambda "m" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Variable "f") (Variable "x"))
    )))

addterm :: Term
addterm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
    ))))

multerm :: Term
multerm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Apply (Variable "m") (Apply (Variable "n") (Variable "f")) 
    )))

suc :: Term -> Term
suc m = Apply sucterm m

add :: Term -> Term -> Term
add m n = Apply (Apply addterm m) n

mul :: Term -> Term -> Term
mul m n = Apply (Apply multerm m) n

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` (suc (numeral 2))

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))
--}

-- - - - - - - - - - - -- Renaming, substitution, beta-reduction

--{
used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x _ n) = [x] `merge` used n
used (Apply  n m) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z t n)
    | z == x    = Lambda z t n
    | otherwise = Lambda z t (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y t m)
    | x == y    = Lambda y t m
    | otherwise = Lambda z t (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)


beta :: Term -> [Term]
beta (Apply (Lambda x t n) m) =
  [substitute x m n] ++
  [Apply (Lambda x t n') m  | n' <- beta n] ++
  [Apply (Lambda x t n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x t n) = [Lambda x t n' | n' <- beta n]
beta (Variable _) = []
--}

-- - - - - - - - - - - -- Normalize

--{
normalize :: Term -> IO ()
normalize m = do
  putStrLn $ show (bound m) ++ " -- " ++ show m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)
--}


------------------------- Assignment 2: Type checking


type Context = [(Var,Type)]

typeof :: Context -> Term -> Type
typeof context (Variable x) = case (lookup x context) of 
    Just t  -> t
    Nothing -> error $ "Variable " ++ x ++ " not in context"
typeof context (Lambda x t m) = (t :-> (typeof ((x,t):context) m))
typeof context (Apply    n m) = applytypes (typeof context n) (typeof context m) where
    applytypes :: Type -> Type -> Type
    applytypes (Base) _ = error "Expecting ARROW type, but given BASE type"
    applytypes ((:->) t1 t2) t3
        | t1 == t3      = t2 
        | otherwise     = error $ "Expecting type " ++ show t1 ++ ", but given type " ++ show t3



example8 = Lambda "x" Base ((Apply (Apply (Variable "f") (Variable "x")) (Variable "x")))



------------------------- Assignment 3: Functionals

data Functional =
    Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f


-- - - - - - - - - - - -- Examples

-- Using lambdas here to mimic intuition from lambda calculus

-- plussix : N -> N
plussix :: Functional
plussix = (Fun (\(Num i) -> (Num (i + 6))))


-- plus : N -> (N -> N)
plus :: Functional
plus = (Fun (\(Num i) -> 
       (Fun (\(Num j) -> (Num (i + j))))))


-- twice : (N -> N) -> N -> N
twice :: Functional
twice = (Fun (\(Fun f) -> 
        (Fun (\(Num i) -> fun (Fun f) (fun (Fun f) (Num i))))))


-- - - - - - - - - - - -- Constructing functionals

dummy :: Type -> Functional
dummy (Base)        = (Num 0)
dummy ((:->) t1 t2) = (Fun (\x -> (dummy t2)))

count :: Type -> Functional -> Int
count (Base) (Num i)      = i
count (Base) (Fun _)      = error "Expecting ARROW type, but given BASE type"
count ((:->) _ _) (Num _) = error "Expecting BASE type, but given ARROW type"
count ((:->) t1 t2) f     = count t2 (fun f (dummy t1))

increment :: Functional -> Int -> Functional
increment (Num i) n = (Num (i + n))
increment f n       = (Fun (\x -> (increment (fun f x) n)))


------------------------- Assignment 4 : Counting reduction steps

type Valuation = [(Var, Functional)]

interpret :: Context -> Valuation -> Term -> Functional
interpret _ valuation (Variable var) = case (lookup var valuation) of 
    Just func -> func
    Nothing   -> error $ "Variable " ++ var ++ " not in valuation"
interpret context valuation (Lambda x t m)      = (Fun (\g -> (interpret ((x, t):context) ((x, g):valuation) m)))
interpret context valuation (Apply m n) = increment (fun f g) (1 + count (typeof context n) g) where
    f :: Functional
    f = interpret context valuation m

    g :: Functional
    g = interpret context valuation n


bound :: Term -> Int
bound term = count (typeof [] term) (interpret [] [] term)

