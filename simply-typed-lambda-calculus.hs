------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x : xs) (y : ys)
  | x == y = x : merge xs ys
  | x <= y = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x : xs) (y : ys)
  | x < y = x : minus xs (y : ys)
  | x == y = minus xs ys
  | otherwise = minus (x : xs) ys

variables :: [Var]
variables = [[x] | x <- ['a' .. 'z']] ++ [x : show i | i <- [1 ..], x <- ['a' .. 'z']]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [x | x <- xs, x `notElem` ys]

fresh :: [Var] -> Var
fresh = head . removeAll variables

------------------------- Simple types

data Type
  = Base
  | (:->) Type Type
  deriving (Eq)

nice :: Type -> String
nice Base = "o"
nice (Base :-> rhs) = "o -> " ++ nice rhs
nice (lhs :-> rhs) = "(" ++ nice lhs ++ ") -> " ++ nice rhs

instance Show Type where
  show = nice

------------------------- Terms

type Var = String

data Term
  = Variable Var
  | Lambda Var Type Term
  | Apply Term Term

pretty :: Term -> String
pretty = f 0
  where
    f :: Int -> Term -> String
    f _ (Variable x) = x
    f i (Lambda var t term) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ var ++ ": " ++ nice t ++ " . " ++ f 0 term
    f i (Apply lhs rhs) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 lhs ++ " " ++ f 2 rhs

instance Show Term where
  show = pretty

------------------------- Numerals

numeral :: Int -> Term
numeral i = Lambda "f" (Base :-> Base) (Lambda "x" Base (numeral' i))
  where
    numeral' i
      | i <= 0 = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i - 1))

sucterm :: Term
sucterm =
  Lambda
    "m"
    ((Base :-> Base) :-> (Base :-> Base))
    ( Lambda
        "f"
        (Base :-> Base)
        ( Lambda
            "x"
            Base
            ( Apply
                (Apply (Variable "m") (Variable "f"))
                (Apply (Variable "f") (Variable "x"))
            )
        )
    )

addterm :: Term
addterm =
  Lambda
    "m"
    ((Base :-> Base) :-> (Base :-> Base))
    ( Lambda
        "n"
        ((Base :-> Base) :-> (Base :-> Base))
        ( Lambda
            "f"
            (Base :-> Base)
            ( Lambda
                "x"
                Base
                ( Apply
                    (Apply (Variable "m") (Variable "f"))
                    (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
                )
            )
        )
    )

multerm :: Term
multerm =
  Lambda
    "m"
    ((Base :-> Base) :-> (Base :-> Base))
    ( Lambda
        "n"
        ((Base :-> Base) :-> (Base :-> Base))
        ( Lambda
            "f"
            (Base :-> Base)
            ( Apply
                (Variable "m")
                (Apply (Variable "n") (Variable "f"))
            )
        )
    )

suc :: Term -> Term
suc = Apply sucterm

add :: Term -> Term -> Term
add m = Apply (Apply addterm m)

mul :: Term -> Term -> Term
mul m = Apply (Apply multerm m)

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` suc (numeral 2)

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

------------------------- Renaming, substitution, beta-reduction

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda var _ term) = [var] `merge` used term
used (Apply lhs rhs) = used lhs `merge` used rhs

rename :: Var -> Var -> Term -> Term
rename old new (Variable x)
  | x == old = Variable new
  | otherwise = Variable x
rename old new (Lambda var t term)
  | var == old = Lambda var t term
  | otherwise = Lambda var t (rename old new term)
rename old new (Apply lhs rhs) = Apply (rename old new lhs) (rename old new rhs)

substitute :: Var -> Term -> Term -> Term
substitute old new (Variable x)
  | old == x = new
  | otherwise = Variable x
substitute old new (Lambda var t term)
  | old == var = Lambda var t term
  | otherwise = Lambda freshVar t (substitute old new (rename var freshVar term))
  where
    freshVar :: Var
    freshVar = fresh (used new `merge` used term `merge` [old, var])
substitute old new (Apply lhs rhs) = Apply (substitute old new lhs) (substitute old new rhs)

beta :: Term -> [Term]
beta (Apply (Lambda var t term) rhs) =
  [substitute var rhs term]
    ++ [Apply (Lambda var t n') rhs | n' <- beta term]
    ++ [Apply (Lambda var t term) term' | term' <- beta rhs]
beta (Apply lhs rhs) =
  [Apply lhs' rhs | lhs' <- beta lhs]
    ++ [Apply lhs rhs' | rhs' <- beta rhs]
beta (Lambda var t term) = [Lambda var t term' | term' <- beta term]
beta (Variable _) = []

------------------------- Normalize

normalize :: Term -> IO ()
normalize term = do
  putStrLn $ show (bound term) ++ " -- " ++ show term
  let terms = beta term
  if null terms
    then return ()
    else normalize (head terms)

------------------------- Type checking

type Context = [(Var, Type)]

typeof :: Context -> Term -> Type
typeof context (Variable x) = case lookup x context of
  Just t -> t
  Nothing -> error $ "Variable " ++ x ++ " not in context"
typeof context (Lambda var t term) = t :-> typeof ((var, t) : context) term
typeof context (Apply lhs rhs) = applytypes (typeof context lhs) (typeof context rhs)
  where
    applytypes :: Type -> Type -> Type
    applytypes Base _ = error "Expecting ARROW type, but given BASE type"
    applytypes (lhs :-> rhs) other
      | lhs == other = rhs
      | otherwise = error $ "Expecting type " ++ show lhs ++ ", but given type " ++ show other

example8 = Lambda "x" Base (Apply (Apply (Variable "y") (Variable "x")) (Variable "x"))

------------------------- Functionals

data Functional
  = Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f

------------------------- Examples

-- plussix : N -> N
plussix :: Functional
plussix = Fun (\(Num i) -> Num (i + 6))

-- plus : N -> (N -> N)
plus :: Functional
plus = Fun (\(Num i) -> Fun (\(Num j) -> Num (i + j)))

-- twice : (N -> N) -> N -> N
twice :: Functional
twice = Fun (\(Fun f) -> Fun (\(Num i) -> f (f (Num i))))

------------------------- Constructing functionals

dummy :: Type -> Functional
dummy Base = Num 0
dummy (_ :-> rhs) = Fun (\x -> dummy rhs)

count :: Type -> Functional -> Int
count Base (Num i) = i
count Base (Fun _) = error "Expecting ARROW type, but given BASE type"
count (_ :-> _) (Num _) = error "Expecting BASE type, but given ARROW type"
count (lhs :-> rhs) (Fun f) = count rhs (f (dummy lhs))

increment :: Functional -> Int -> Functional
increment (Num i) n = Num (i + n)
increment (Fun f) n = Fun (\x -> increment (f x) n)

------------------------- Counting reduction steps

type Valuation = [(Var, Functional)]

interpret :: Context -> Valuation -> Term -> Functional
interpret _ valuation (Variable var) = case lookup var valuation of
  Just func -> func
  Nothing -> error $ "Variable " ++ var ++ " not in valuation"
interpret context valuation (Lambda var t term) = Fun (\g -> interpret ((var, t) : context) ((var, g) : valuation) term)
interpret context valuation (Apply lhs rhs) = increment (fun f g) (1 + count (typeof context rhs) g)
  where
    f :: Functional
    f = interpret context valuation lhs

    g :: Functional
    g = interpret context valuation rhs

bound :: Term -> Int
bound term = count (typeof [] term) (interpret [] [] term)
