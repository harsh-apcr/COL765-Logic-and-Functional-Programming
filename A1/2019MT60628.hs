import Data.List
import System.Random
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad (replicateM)
import Data.Array

-- Problem 1

-- "tail-recursive reversal of a list" 

reverseA1 :: [a] -> [a]
reverseA1 ls = reverseIter ls []
        where
            reverseIter ls m =
                case ls of
                    [] -> m
                    (x:xs) -> reverseIter xs (x:m)

{-
Correctness : Invariant : reverseIter ls m = (reverse ls) ++ m 
                        , where reverse : [a] -> [a] , reverses the input list
              Induction on size of ls (say n)
              Base case : n = 0  
                        reverseIter [] m = m = [] ++ m = (reverse []) ++ m
              Inductive step : for n > 0 
                        reverseIter (x:xs) m = reverseIter xs (x:m)
                                             = (reverse xs) ++ (x:m) (induction hypothesis size(xs) = n-1)  
                                             = (reverse xs) ++ [x] ++ m
                                             = (reverse x:xs) ++ m (front of the list goes to the tail on reversal)
                                             = (reverse ls) ++ m

             Thus reverseA1 ls = reverseIter ls [] = (reverse ls)++[] = reverse ls       

Time Complexity Analysis : O(n) , where n is the length of the list\
    let x[i,j] denote elements of the list from index i to j
    x[1,n] = [x1,x2,...,xn]

    reverseIter x[1,n] [] = reverseIter x[2,n] (x1:[])
                          = reverseIter x[3,n] (x2:x1:[])
                          ...
                          = reverseIter [] (xn:x(n-1):...:x2:x1:[])
                          = (xn:...x2:x1:[]) - (*)
        -- O(n) machine steps to go to equation (*) last recursive call --

    Total time = O(n)    
-}

-- "tail-recursive merge function"

-- inputs l1 and l2 must be sorted lists 
mergeA1 :: Ord a => [a] -> [a] -> [a]
mergeA1 l1 l2 = reverseA1 (mergeIter l1 l2 [])
        where
            mergeIter [] l2 m = reverseA1 l2 ++ m
            mergeIter l1 [] m = reverseA1 l1 ++ m
            mergeIter (x:xs) (y:ys) m =
                if x <= y then
                    mergeIter xs (y:ys) (x:m)
                else
                    mergeIter (x:xs) ys (y:m)

{-
Correctness : 
    (Invariant : mergeIter l1 l2 m = reverse (merge l1 l2) ++ m , where merge is actual "correct" merge function
    Induction on (n,m) where n = length l1 , m = length l2 and l1,l2 are sorted
    Base Case : n = 0 or m = 0
                if n = 0 then mergeIter [] l2 m = reverseA1 l2 ++ m
                = reverse l2 ++ m = reverse (merge [] l2) ++ m
                Similarly m = 0 case holds true
    Inductive step : n > 0 and m > 0
                mergeIter (x:xs) (y:ys) m =
                    if (x <= y) then mergeIter xs l2 (x:m)
                    = reverse (merge xs l2) ++ (x:m) (Induction Hypothesis , since length xs = n-1) 
                    = reverse (merge xs l2) ++ [x] ++ m 
                    since x <= x' for all x' in xs and x <= y' for all y' in l2
                    x is the head of merge (x:xs) (y:ys)
                    = reverse (merge (x:xs) l2) ++ m
                    = reverse (merge l1 l2) ++ m
                    Similarly the other case (y < x) will follow

    Thus ,mergeA1 l1 l2 = reverseA1 (mergeIter l1 l2 [])
                        = reverse (reverse (merge l1 l2) ++ []) = reverse (reverse (merge l1 l2)) = merge l1 l2
Time Complexity Analysis
        Since in each step of the algorithm n or m is decreasing by 1 (unless it is 0)
        Incase ,WLOG say n = 0 then reverse l2 ++ m (here m is the list in mergeIter function) takes O(length l2) time 
        It wil take atmost n+m machine steps to complete the function
        time = O(n+m)                     
-}


-- "tail-recursive fibonacci function"

-- Word in haskell is Unsigned Integer type
fibA1 :: Word -> Word
fibA1 = fibIter 0 1
    where
        fibIter a b m
            | m == 0 = b
            | otherwise = fibIter b (a+b) (m-1)
{-
Correctness : 
Invariant : fibIter a b m = F_{m-1}*a + F_{m}*b for all m >= 0
            where F_{~1} = 0 , F_{0} = 1 , F_{m} = F_{m-1} + F_{m-2} for all m >= 1 (i.e. Fibbonacci numbers)
            Induction on m
            Base Case : m = 0 , fibIter a b 0 = b = F_{~1}*a+F_{0}*b 
            Induction Step : m > 0
                      fibIter a b m = fibIter b (a+b) (m-1)
                                    = b*F_{m-2} + (a+b)*F_{m-1}  (Induction Hypothesis)
                                    = a*F_{m-1} + b*F_{m}  
Timing Analysis : 
            Let T(n) be the time to compute fibIter 0 1 n
            T(n) = T(n-1) + O(1)
         => T(n) = O(n)
-}

-- Tail Recursive inserion Sort

insertSortA1 :: Ord a => [a] -> [a]
insertSortA1 [] = []
insertSortA1 (x:xs) = insertSortIter (x:xs) []
    where
        insertSortIter ls m =
            case ls of
                [] -> m
                x:xs -> insertSortIter xs (insertA1 x m)
            where
                insertIter e ls m =
                        case ls of
                            [] -> e:m
                            (x:xs) -> if e > x then insertIter e xs (x:m)
                                      else insertIter x xs (e:m)
                insertA1 e l = reverseA1 (insertIter e l [])

{-
Correctness : 
Invariant1: **insertIter e ls m = reverse (insert e ls) ++ m**
            where ls is sorted up , insert puts e in the correct location into ls so that resultant list is sorted
            Induction on n = length ls
            Base case : n = 0 , insertIter e [] m = e:m 
                                                  = [e] ++ m
                                                  = reverse (insert e []) ++ m 
            Induction Step : for n > 0
                            insertIter e (x:xs) m = 
                                if (e>x) then insertIter e xs (x:m)
                                = reverse (insert e xs) ++ (x:m) (Induction hypothesis , length xs = n-1)
                                = reverse (insert e xs) ++ [x] ++ m
                                since x < e and x <= x' for all x' in xs (x:xs is sorted up)
                                x is head of insert e (x:xs) and insert e (x:xs) = x:(insert e xs)
                                = reverse (insert e (x:xs))++m
                                = reverse (insert e ls) ++ m

Thus , we have insertA1 e l = insert e l (where e is inserted in the sorted list l at the right position)
    as insertA1 e l = reverseA1 (insertIter e l []) 
                    = reverse (reverse (insert e ls) ++ [])                 
                    = reverse (reverse (insert e ls)) = insert e ls     
                                                                    Q.E.D    
***             
Lemma : merge l1 l2 = merge (l1.delete(l')) (insert l' l2) for any l' in l1
        where l2 is sorted list and l1 is any list
        merge l1 l2 merges the two lists such that result is sorte
Proof : By induction on n = length l1
        Base Case : n = 1
        merge [l'] l2 = merge [] (insert l' l2) = sorted list with elements from l1 as well as l2
        Inductive Step : for any n > 1
        merge l1 l2 = merge (l1') (l2') where l1' = l1.delete(l') for some l' in l1 
                                              l2' = insert l' l2 (sorted list)
                    = sorted list with elements from l1 as well as l2 (Induction hypothesis as length l1' = n-1)                                
***

Invariant2: insertSortIter ls m = merge (sorted ls) m
            where m is sorted and merge merges to sorted list 
            Induction on n = length ls
            Base case :  n = 0 , insertSortIter [] m = m = merge (sorted []) m
            Inductive Step : for n > 0
                        insertSortIter (x:xs) m = insertSortIter xs (insertA1 x m)
                                                = merge (sorted xs) (insert x m) (Induction hypothesis)
                                                = merge (sorted x:xs) m (from ***lemma***)
                                                = merge (sorted ls) m 

Thus , we have insertSortA1 ls = inserSortIter ls []
                               = merge (sorted ls) [] = sorted ls   
                                                                 Q.E.D

Time Complexity Analysis : 
    for insertA1
    n = length l , let T(n) be time required to perform insertIter e l []
    T(n) = T(n-1) + O(1) (T(n-1) for tail recursive call on smaller l and O(1) to prepend element into 'm' after last recursive call)
         => T(n) = O(n)
    time for insertA1 = O(n) + O(n) = O(n) (to compute insertIter and reverse the list)
    for insertSort 
    T(n) = T(n-1) + O(n) (where T(n-1) for tail recursive call to the function and call to insertA1 )
    *T(n) = O(n^2) (triangular number recursion equation for T)*
-}

-- Recursive qsort

qsortA1 :: Ord a => [a] -> [a]
qsortA1 ls =
    case ls of
        [] -> []
        [x] -> [x]
        x:xs ->
            let
                (p1,p2) = partitionA1 x (x:xs) [] []    -- pivot element is x
            in qsortA1 (init p1) ++ [last p1] ++ qsortA1 p2
    where
        partitionA1 e ls p1 p2 =
            case ls of
                [] -> (p1,p2)
                x:xs -> if x <= e then partitionA1 e xs (x:p1) p2
                        else partitionA1 e xs p1 (x:p2)

{-
Correctness : 
Invariant : partitionA1 e ls p1 p2 = (p1',p2') 
            where p1' contains all the elements from ls <= e as well as elements from p1
                  p2' contains all the elements from ls > e as well as elements from p2
            Induction on n , n = length ls      
Base Case : n = 0
            partitionA1 e [] p1 p2 = (p1,p2) (vacuously true)
Inductive Step : n > 0 
            partitionA1 e (x:xs) p1 p2 =
                if (x <= e) then partitionA1 e xs (x:p1) p2
                = (p1',p2') (induction hypothesis) 
                where
                p1' contains all the elements from xs <= e as well as elements from (x:p1)
             => p1' contains all the elements from x:xs <= e as well as from p1
                p2' contains all the elements from ls > e as well as elements from p2

                else i.e. x > e
                then partitionA1 e xs p1 (x:p2) 
                = (p1',p2')
                where 
                p1' contains all the elements from ls <= e as well as elements from p1
                p2' contains all the elements from xs > e as well as elements from (x:p2)  
             => p1' contains all the elements from ls = x:xs > e as well as elements from p2   

qsortA1 ls = sorted ls
Induction on n = length ls
Base case : n = 0 , qsortA1 [] = []
            n = 1 , qsortA1 [x] = [x]
Inductive Step : for n > 1
            (p1',p2') = partitionA1 x (x:xs) [] []
            from invariant p1' = all the elements from x:xs <= x (as initial value p1 = [])
                           p2' = all the elements from x:xs > x (p2 = [])

            i.e. p1' , p2' partitions ls (= x:xs)
            length (init p1') < length ls (init returns the list with last element removed)      
            length p2' < length ls (p2' cannot contain x)
            thus qsort p1' = sorted p1' , qsort p2' = sorted p2' (Induction hypothesis)
            qsort (init p1') ++ [last p1'] ++ qsortp2' = sorted ls                             
-}


-- Recursive Binary Search in a sorted "array"
binSearchA1 :: (Ord a2, Ix a1, Integral a1) => a2 -> Array a1 a2 -> a1 -> a1 -> a1
binSearchA1 e a low high
                            | low > high = error "Not Found"
                            | a ! ((low+high) `div` 2) < e = binSearchA1 e a ((low+high) `div` 2) high
                            | a ! ((low+high) `div` 2) == e = (low+high)`div`2
                            | otherwise = binSearchA1 e a low ((low+high) `div` 2)
                            
                                                    
{-
Correctness Analysis :
binSearchA1 e a low high searches e in a[low..high]
Induction on n = high-low+1
Base case : n = 1
            => high = low = (low+high) div 2
            => binSearch A1 e a low high = if (e == a[(low+high)/2] then return the index else  )
                                           else throws an error indicating "not found"
                                         == search e in a[low..high] = a[high] = a[low]  
Inductive Step :
            n > 1 => high > low
            if a[(low+high)/2] < e => e cannot be in a[low..(high+low)/2] as array is sorted
            binSearchA1 e a low high = binSearchA1 e a (low+high div 2) high
                                     = searches e in a[low+high div 2 .. high] (I.H. as high - (low+high)/2 < high - low)
            else if a[(low+high)/2] > e => e cannot be in a[(low+high)/2..high] as again a is sorted
            binSearchA1 e a low high = binSearchA1 e a low (low+high div 2)
                                     = searches e in a[low .. low+high/2]   (I.H as (low+high)/2 - low < high - low)
            else a[low+high/2] == e then returns (low+high)/2  

Timing Analysis :
    let n = high-low
    At each recursive call length of array to decreases by 1/2
    Let T(n) : time to binary search in sorted array a
    T(n) = T(n/2) + O(1) => T(n) = O(log n)             
-}





-- Problem 2 (Probabilistic Primality Testing Algorithm)

prime :: Int -> Int -> String
prime n q
    | primeTest n q = "Probably A Prime"
    | otherwise = "Not a Prime"
    where
        primeTest n q =
            (q == 0) || (
            let
                a = (unsafePerformIO (randomIO :: IO Int)+n) `mod` n
            in
                a == 0 || a == 1 || fermatTest a n && primeTest n (q-1)
            )
        fermatTest a n = powerModIter a n 1 n == a
        powerModIter a n p k =
                if k == 0 then p
                else powerModIter a n (p*a `mod` n) (k-1)

-- Reference for Problem 2 (Generating random numbers in Haskell) : https://www.schoolofhaskell.com/school/starting-with-haskell/libraries-and-frameworks/randoms



-- Higher order function

-- Newton's method

computeRootA1 f guess tol = computeRootIter f guess tol (guess - f guess / der f guess)
        where
            computeRootIter f guess tol newGuess =
                if abs (newGuess - guess) < tol then newGuess
                else computeRootIter f newGuess tol (newGuess - f newGuess / der f newGuess)
            der f = \x -> (f (x+1e-4) - f x)/1e-4

-- Higher order double sum

computeDoubleSumA1 f a b c d =
    if a > b then
        0
    else
        sum (f a) c d + computeDoubleSumA1 f (a+1) b c d
    where
        sum f a b = if a > b then 0
                    else f a + sum f (a+1) b


{-
Correctness :
Lemma : sum f a b = \sum_{i = a}^b f(i)
Induction on b-a
Base case : a > b then sum f a b = 0 = \sum_{i=a}^b f(i)  -- in Latex notation
Induction step : sum f a b = f a + sum f (a+1) b
                           = f(a) + \sum_{i = a+1}^b f(i) (Induction hypothesis as b-(a+1) < b-a)
                           = \sum_{i = a}^b f(i)

computeDoubleSumA1 f a b c d = \sum_{i = a}^b \sum_{j = c}^d f(i,j) -- in Latex notation
Induction on b-a
Base Case : 
    a > b => \sum_{i = a}^b \sum_{j=c}^d f(i,j) = 0 = computeDoubleSumA1 f a b c d
    Inductive Step :
    computeDoubleSumA1 f a b c d =
        = sum (f a) c d + computeDoubleSumA1 f (a+1) b c d
        = sum_{j = c}^d f(a,j) + \sum_{i = a+1}^b \sum_{j = c}^d f(i,j) (Induction Hypothesis as  b - (a+1) < b-a )
        = sum_{i = a}^b \sum_{j = c}^d f(i,j)

Timing Analysis : 
Assume for every i,j time to compute f(i,j) is O(1)
then 
    T(a,b,c,d) - denotes time to compute aforementioned double sum
    T(a,b,c,d) = O(d-c) + T(a+1,b,c,d) -- time to compute single sum from c to d , and recursive call of the function
    and T(b+1,b,c,d) = O(1)
    thus T(a,b,c,d) = O((a-b)(c-d))        
-}
