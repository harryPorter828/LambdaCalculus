

-------------------------
-------- PART A --------- 
-------------------------

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
 -- deriving Show

instance Show Term where
  show = pretty

example :: Term
example = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Variable "a")) (Variable "x")) (Variable "b")))

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m


------------------------- Assignment 1

numeral :: Int -> Term 
numeral i = Lambda "f" (Lambda "x" (f i))
    where 
        f 0 = Variable "x"
        f i = Apply (Variable "f") (f (i-1))
        
            

-------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys
    
elementInList :: Var -> [Var] -> Bool
elementInList i [] = False 
elementInList i (x:xs)
    | i == x = True
    | otherwise= elementInList i xs
    
filterIt :: Var -> [Var] -> [Var]
filterIt i []= []
filterIt i (x:xs)
    |i == x = (filterIt i xs)
    |otherwise = x : (filterIt i xs )
    



------------------------- Assignment 2
alphabet = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"]
infiniteAlphabet= [alphabet!!(mod i 26) | i<-[0..] ]

multipleElements :: Int -> Int -> [Int]
multipleElements 1 i = i : multipleElements 26 (i+1)
multipleElements n i = i : multipleElements (n-1) i

numbers26 = [ multipleElements 26 1 ]

variables :: [Var]
variables =  alphabet ++ [ (infiniteAlphabet!!i) ++ (Prelude.show (numbers26!!0!!i)) | i <- [0..] ]



filterVariables :: [Var] -> [Var] -> [Var]
filterVariables [] [] = []
filterVariables []  ys = []
filterVariables xs [] = xs 
filterVariables xs (y:ys) 
    |elementInList y xs = filterVariables (filterIt y xs) ys
    |otherwise = filterVariables xs ys
    


fresh :: [Var] -> Var
fresh xs = freshMain xs variables

freshMain ::[Var] -> [Var]->Var
freshMain xs (y:ys)
    |elementInList y xs = freshMain xs ys
    |otherwise = y
    
    


used :: Term -> [Var]
used (Lambda x m) = merge [x] (used m)
used (Variable x) = [x] 
used (Apply n m) = merge (used n) (used m)
    
    


------------------------- Assignment 3

rename :: Var -> Var -> Term -> Term
rename x y (Variable z)  
    | z==x = Variable y
    | otherwise = Variable z
rename x y (Lambda z n) 
    | z==x = Lambda y (rename x y n) 
    | otherwise = Lambda z (rename x y n)
    
rename x y (Apply  n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x y (Apply  n m) = Apply (substitute x y n) (substitute x y m)
substitute x y (Lambda z n) 
    | z==x = Lambda z n
    | otherwise = Lambda (fresh((used y)++(used n)++[x])) (substitute x y (rename z (fresh((used y)++(used n)++[x])) n ))
substitute x y (Variable z)  
    | z==x = y
    | otherwise = Variable z




------------------------- Assignment 4
elementInList2 :: Term -> [Term] -> Bool
elementInList2 i [] = False 
elementInList2 i (x:xs)
    | pretty i == pretty x = True
    | otherwise= elementInList2 i xs
    
    

removeDuplicates :: [Term] -> [Term]
removeDuplicates [] = []
removeDuplicates (x:xs)
    | elementInList2 x xs = removeDuplicates xs
    | otherwise = x : removeDuplicates xs
    
isReducible :: Term -> Bool
isReducible (Apply (Lambda z n) m) = True
isReducible (Apply n m) = (isReducible n) || (isReducible m)
isReducible (Lambda z n) = isReducible n
isReducible (Variable a) = False 

    
beta :: Term -> [Term]
beta (Apply (Lambda z n) m) = [substitute z m n]  ++ [Apply (Lambda z i) m| i<- beta n] ++ [Apply (Lambda z n) i | i<- beta m]
beta (Variable a) = []
beta (Lambda z n) = [(Lambda z i)| i<- beta n]
beta (Apply n m) = [Apply i m| i<- beta n] ++[Apply n i| i<- beta m]



normalize :: Term -> IO ()
normalize x  
    |isReducible x= do         
        putStrLn (pretty x)
        let y = ((beta x)!!0)
        normalize y
    |otherwise = putStrLn (pretty x)
    


------------------------- 
a_beta :: Term -> [Term]
a_beta (Apply (Lambda z n) m) = [Apply (Lambda z i) m| i<- a_beta n] ++[Apply (Lambda z n) i | i<- a_beta m]   ++ [substitute z m n]
a_beta (Variable a) = []
a_beta (Lambda z n) = [(Lambda z i)| i<- a_beta n]
a_beta (Apply n m) = [Apply i m| i<- a_beta n] ++[Apply n i| i<- a_beta m]


a_normalize :: Term -> IO ()
a_normalize x  
    |length (a_beta x) /= 0= do         
        putStrLn (pretty x)
        let y = ((a_beta x)!!0)
        a_normalize y
    |otherwise = putStrLn (pretty x)


-------------------------

example1 :: Term
example1 = Apply (numeral 2) (example)
example2 :: Term
example2= Apply (Lambda "y" (Variable "a")) (Apply (Lambda "x" (Apply (Variable "x") (Variable "b"))) (Lambda "x" (Apply (Variable "x") (Variable "x"))))


-------------------------
-------- PART B --------- 
-------------------------


------------------------- Assignment 5 (PAM)

type PState = (Term, [Term])

state1 = (Lambda "x" (Lambda "y" (Variable "x")) , [Variable "Yes", Variable "No"])

term1 = Apply (Apply (Lambda "x" (Lambda "y" (Variable "x"))) (Variable "Yes")) (Variable "No")

term2 = Apply (Apply (Lambda "b" (Apply example (Variable "Yes"))) (Lambda "z" (Variable "z"))) (Variable "No")

--used as an alternative to substitute
--The KAM relies on two restrictions. 
--First, it assumes closed terms, i.e. terms with no free variables, or at least where free variables have different names from bound variables. 
--Second is the reduction strategy, weak head reduction

subSimple :: Var -> Term -> Term -> Term
subSimple x y (Apply  n m) = Apply (subSimple x y n) (subSimple x y m)
subSimple x y (Lambda z n) = Lambda z (subSimple x y n)
subSimple x y (Variable z)  
    | z==x = y
    | otherwise = Variable z
    
p_start :: Term -> PState
p_start x = (x, []) 

isLast :: Term -> Bool
isLast (Apply (n)(m)) = False
isLast n = True 

splitApply :: Term -> (Term, Term)
splitApply (Apply (n)(m))
    |isLast m = (n,m)
    |otherwise = ((Apply (n) (fst (splitApply m))),(snd (splitApply m)))


p_step :: PState -> PState
p_step ((Lambda z n),x:xs)= ((substitute z x n), xs)
p_step ((Apply (n)(m)), xs) 
    |isLast m = (n, m:xs)
    |otherwise = ((Apply (n) (fst (splitApply m))),((snd (splitApply m)):xs))
        


p_final :: PState -> Bool
p_final ((Lambda z n),[])  
    |isLast n =True
    |otherwise = False
p_final ((Lambda z n),xs) =False
p_final ((Variable x), []) =True
p_final ((Variable x),xs) =True
p_final ((Apply m n), [])= False
p_final ((Apply m n), xs)= False


p_runMain :: PState -> IO ()
p_runMain i
    |p_final i = do
                print (i)
                print (p_readback i)
    |otherwise = do
                print (i)
                (p_runMain(p_step i))
                
    
p_run :: Term -> IO ()
p_run i = p_runMain (p_start i)
   





p_readback :: PState -> Term
p_readback (i, []) = i
p_readback (i,[x]) = (Apply (i) (x))
p_readback (i,x:xs) = p_readback((Apply (i) (x)),xs)



------------------------- Assignment 6 (KAM)
{-data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
 -- deriving Show
-}
stringToList :: [String] -> String
stringToList [] = ""
--stringToList x = x 
stringToList (x:xs) 
    |length xs == 0 = x
    |otherwise = x ++ "," ++ (stringToList xs)



data EnvMain = EnvMain Var  Term  Env


instance Show EnvMain where
    show = pretty2
pretty2 :: EnvMain -> String
pretty2 (EnvMain x y xs) = "(\"" ++ x ++ "\"," ++ (pretty y) ++ ",[" ++ (stringToList [pretty2 i | i<-xs]) ++ "])"


type Env = [EnvMain]


    
type State = (Term, Env, [(Term, Env)])
 
envExample :: Env
envExample = [(EnvMain ("y") (example) [])] 
 
--state6 :: State 
--state6 = (example , envExample, [("y",envExample)] )

--Apply (Lambda "x" (Variable "x")) (Variable "y")
--[(EnvMain ("y") (Lambda "z" (Variable "z")) [])]

state2 :: State      
state2 =  (Apply (Lambda "x" (Variable "x")) (Variable "y") , [(EnvMain ("y") (Lambda "z" (Variable "z")) [])], [] )

--Apply (Variable "x") (Variable "x")
--[(EnvMain ("x") (Lambda "x" (Apply (Variable "x") (Variable "x"))) [])]


state3 :: State
state3 = (Apply (Variable "x") (Variable "x") , [(EnvMain ("x") (Lambda "x" (Apply (Variable "x") (Variable "x"))) [])], [] )

--Lambda "y" (Variable "x")
--[(Variable "z", [(EnvMain ("z") (Lambda "a" (Variable "b")) ([(EnvMain ("b") (Variable "c") [])]))])]

state4:: State
state4 = (Lambda "y" (Variable "x") , [], [( Variable "z", [(EnvMain ("z") (Lambda "a" (Variable "b")) ([(EnvMain ("b") (Variable "c") [] )]))])] )



start :: Term -> State
start i = (i,[],[])

step :: State -> State
step (Variable x, ((EnvMain y n f):xs), ys)
    |x==y = (n, f, ys)
    |otherwise =(Variable x, xs, ys)
step ((Lambda x n), xs, ((m,f):ys)) = (n, ((EnvMain x m f):xs) , ys)
step ((Apply n m), xs, ys) = (n, xs, ((m, xs):ys))

final :: State -> Bool
final ((Lambda x n), xs, []) = True
final ((Variable x), [], xs)= True
final i = False

run :: Term -> IO ()
run i = runMain (start i)


runMain :: State -> IO ()
runMain i
    |final i = do
                print (i)
                print (readback (i))
    |otherwise = do
                print (i)
                (runMain(step i))
                
                
-- simplify :: Env -> Env 
-- simplify [] = [] 
-- simplify ((EnvMain a b []):xs)= ((EnvMain a b []) : (simplify xs))
-- simplify ((EnvMain a b ((EnvMain i j []):ns)):xs) = simplify((EnvMain a (substitute i j b) (simplify ns)): xs)


-- readback :: State -> Term 
-- readback (i, [], []) = i 
-- readback (i, [], ((j,[]):ls))= readback((Apply i j) , [] , ls)
-- readback (i, [], ((j, ((EnvMain a b []):xs)):ls))= readback (i, [], (((substitute a b j) , xs):ls))
-- readback (i, [], ((j,k):ls))= readback(i, [], ((j,(simplify k)):ls))
-- readback (i,((EnvMain a b []):js),k) = readback((substitute (a) (b) (i)) , js , k)
-- readback (i, j, k) = readback (i , (simplify j) , k)

readback :: State -> Term 
readback (i, [], []) = i 
readback (i, [], (l:ls))= readback((Apply i (retrieveTerm(l))) , [] , ls)
readback (i,j,k) = readback ((retrieveTerm(i,j)), [],k)



retrieveTerm :: (Term, Env) -> Term
retrieveTerm  ((Variable x), []) = Variable x
retrieveTerm ((Variable x), ((EnvMain a b c):ks))
    |a==x = retrieveTerm (b, c)
    |otherwise = retrieveTerm ((Variable x), ks)
retrieveTerm  ((Lambda x n), ks) = (Lambda x (retrieveTerm (n,((EnvMain  x (Variable x) []):ks))))
retrieveTerm ((Apply a b), c) = (Apply (retrieveTerm (a,c)) (retrieveTerm (b,c)))

                
 
