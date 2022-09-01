
module BigInteger (BigInteger,toString,fromString,add,karatsuba) where

    -- export list info
    import Data.List
    type BigInteger = [Int]
    -- **Integers are stored in list in reverse order of digits**
    -- default base for toString function is 10
    toString :: [Int] -> String
    toString = reverse.concatMap show

    -- default base for fromString function is 10
    fromString :: String -> [Int]
    fromString = reverse.foldr ((:).read.pure.filterDigit) []
        where
            filterDigit ch = if ch >= '0' && ch <= '9' then ch
                         else error "Invalid_Input_Exception"

    -- add takes list of integers in base b and outputs the number back
    -- input must be in reverse order of digits
    -- output is also in reverse order of digits
    add b x y = reverse $ addIter x y [] 0 b
        where
            addIter [] [] m c b = if c == 0 then m
                          else c:m
            addIter [] ys m c b = addc ys c b++m
            addIter xs [] m c b = addc xs c b++m
            addIter (x:xs) (y:ys) m c b = addIter xs ys ((x+y+c) `mod` b : m) ((x+y+c) `div` b) b

            addc x c b = addcIter x c b []
            addcIter [] c b m = if c == 0 then m
                                else c:m
            addcIter (y:ys) c b m =
                    addcIter ys ((y+c) `div` b) b ((y+c) `mod` b:m)
    
    
    -- subtract function
    -- unsafe subtract
    sub b x y = reverse $ clearTrailingZeros $ subIter [] x y 0 b
        where
            sbbIter m [] br b = if br == 0 then m
                        else error "Unsafe_Subtraction_Exception"
            sbbIter m (x:xs) br b = sbbIter ((x-br):m) xs 0 b
            subIter m xs [] br b = sbbIter [] xs br b ++ m
            subIter m (x:xs) (y:ys) br b =
                if x - br >= y then
                    subIter ((x-br-y):m) xs ys 0 b
                else
                    subIter ((b+x-br-y):m) xs ys 1 b
            -- clear all the intial zeros in the list        
            clearTrailingZeros [] = []
            clearTrailingZeros (x:xs) =
                        if x == 0 then clearTrailingZeros xs
                        else x:xs        


    -- karatsuba multiplication

    -- some auxilliary functions to implement karatsuba
    -- input z must be in decimal expansion
    toBase b 0 = []
    toBase b z = (z `mod` b):toBase b (z `div` b)

    toDecimal b l =
        case l of
            [] -> 0
            (x:xs) -> x + b*toDecimal b xs

    -- (x0,x1) such that x0 contains first k elements
    myPartition x k = partitionIter [] x k
        where
            partitionIter m x k
                        | k <= 0 = (reverse m,x)
                        | otherwise = partitionIter (head x:m) (tail x) (k-1)

    appendZero :: [Int] -> Int -> [Int]
    appendZero y k = reverse (lshift (reverse y) k)

    lshift :: [Int] -> Int -> [Int]
    lshift z k
        | k <= 0 = z
        | otherwise = 0:lshift z (k-1)

    karatsuba :: Int -> [Int] -> [Int] -> [Int]
    karatsuba b x y =
        let
            n = length x
            m = length y
        in
            if n > m then karatsuba b x (appendZero y (n-m))
            else if m < n then karatsuba b (appendZero x (m-n)) y
            else
                if n <= 2 then
                    let
                        z = toDecimal b x*toDecimal b y
                    in
                        toBase b z
                else
                    let
                        (x0,x1) = myPartition x $ n `div` 2
                        (y0,y1) = myPartition y $ n `div` 2
                        z0 = karatsuba b x0 y0
                        z1 = karatsuba b x1 y1
                        z2 = sub b (karatsuba b (add b x0 x1) (add b y0 y1)) (add b z0 z1)
                    in
                        add b (add b z0 (lshift z2 $ n `div` 2)) (lshift z1 $ 2*(n `div` 2))
