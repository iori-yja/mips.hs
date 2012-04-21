import Data.Bits
--mips primary emuration

data Instraction = Rinst [Char] Int Int Int Int
                 | Iinst [Char] Int Int Int
		 | Jinst [Char] Int 
		 | Meta [Char]
	deriving (Eq, Show, Read)

newtype Set = Set ((Int,Int,Int),[Int],[Int])
	deriving (Eq, Show, Read)
data Status = Interrupt Set | Running Set
	deriving (Eq, Show, Read)

initenv :: IO ()
initenv = runenv $ Set ((0,0,0),(fillout 0 32),[])

fillout :: Int -> Int -> [Int]
fillout _ 0 = []
fillout a b = a : fillout a (b - 1)

runenv :: Set -> IO ()
runenv rs = do
	putStrLn $ show rs
	x <- getLine
	case (exc (rs, fetch x)) of
	     Interrupt y -> do
		      putStrLn "Interrupted"
		      runenv y
	     Running y -> runenv y
	where
	   fetch :: [Char] -> Instraction
	   fetch xs = read (parse $ words xs) :: Instraction
	   parse :: [[Char]] -> [Char]
	   parse (a:b:xs) = unwords $ a : ('"' : b ++ ['"']) : xs

exc :: (Set, Instraction) -> Status
exc (Set (sr,rs,mem) , Meta "clear") | rs !! 0 == 1 = Running $ Set (sr, fillout 0 32,mem)
exc (Set (sr,rs,mem) , Meta "fill") | rs !! 0 == 0  = Running $ Set (sr, fillout 1 32,mem)
exc (Set (sr,rs,mem) , Meta "hlt")                  = Interrupt $ Set (sr, fillout 0 32,mem)

exc (st , Rinst "addu" d s t _)        = rctrl (+) True st d s t
exc (st , Rinst "subu" d s t _)        = rctrl (-) True st d s t
exc (st , Rinst "add" d s t _)         = rctrl (+) False st d s t
exc (st , Rinst "sub" d s t _)         = rctrl (-) False st d s t
exc (st , Rinst "xor" d s t _)         = rctrl xor False st d s t
exc (st , Rinst "and" d s t _)         = rctrl (.&.) False st d s t
exc (st , Rinst "or" d s t _)          = rctrl (.|.) False st d s t

exc (st , Rinst "sll" d s _ q)         = ictrl shiftL True st d s q
exc (st , Rinst "sllv" d s _ q)        = ictrl shiftL True st d s q
exc (st , Rinst "srl" d s _ q)         = ictrl shiftR True st d s q
exc (st , Rinst "sra" d s _ q)         = ictrl (\x y -> if ( testBit x 31 )
   						     then foldr setBit (x `shiftR` y) [31..(32-y)] else x `shiftR` y)
   					 True st d s q
exc (st , Rinst "srav" d s _ q)        = ictrl shiftR True st d s q
exc (st , Rinst "srlv" d s _ q)        = ictrl shiftR True st d s q
exc (st , Iinst "addi" d s im)         = ictrl (+) False st d s im
exc (st , Iinst "subi" d s im)         = ictrl (-) False st d s im
exc (st , _)                           = Interrupt $ Set ((0,0,0),[],[])

rctrl :: (Int -> Int -> Int) -> Bool -> Set -> Int -> Int -> Int -> Status
rctrl f u st@(Set(sr,rs,mem)) d s t  = let p = f (rs !! s) (rs !! t)
		                           rg = ( take d rs ) ++ p `mod` (1 `shift` 30) : drop (d+1) rs
					   stn = Set (sr, rg, mem)
	              in if p < (1 `shift` 30) || u then Running stn
						    else Interrupt stn

ictrl :: (Int -> Int -> Int) -> Bool -> Set -> Int -> Int -> Int -> Status
ictrl f u st@(Set(sr,rs,mem)) d s im  = let p = f (rs !! s) im
		                            rg = ( take d rs ) ++ p `mod` (1 `shift` 30) : drop (d+1) rs
		 			    stn = Set (sr, rg, mem)
	              in if p < (1 `shift` 30) || u then Running stn
						    else Interrupt stn

main :: IO()
main = initenv

