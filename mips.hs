import Data.Bits
import qualified Data.Map as M
import Numeric
--mips primary emuration

data Instraction = Rinst [Char] Int Int Int Int
                 | Iinst [Char] Int Int Int
		 | Jinst [Char] Int 
		 | Meta [Char]
	deriving (Eq, Show, Read)

newtype Set = Set ((Int,Int,Int),[Int],M.Map Int Int) deriving (Eq, Show, Read)
data Status = Interrupt Set | Running Set deriving (Eq, Show, Read)
data SndOp = Imm | Reg deriving (Eq, Show, Read)

initenv :: IO ()
initenv = runenv $ Set ((0,0,0),(fillout 0 32),M.empty)

fillout :: Int -> Int -> [Int]
fillout _ 0 = []
fillout a b = a : fillout a (b - 1)

runenv :: Set -> IO ()
runenv rs@(Set (sr,rg,m)) = do
	mapM (\x -> putStr ( showHex x " : ")) rg
	putStrLn ""
	x <- getLine
	case (exc (rs, fetch x)) of
	     Interrupt y@(Set (_,_,mem)) -> do
		      putStrLn "Interrupted"
		      putStr $ M.showTree mem
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
exc (context , Meta "mem")                      = Interrupt context

exc (st , Rinst "add" d s t _)         = ctrl (+)   False Reg st d s t
exc (st , Rinst "addu" d s t _)        = ctrl (+)   True  Reg st d s t
exc (st , Rinst "sub" d s t _)         = ctrl (-)   False Reg st d s t
exc (st , Rinst "subu" d s t _)        = ctrl (-)   True  Reg st d s t
exc (st , Rinst "slt" d s t _)         = ctrl (\x y -> if ( x < y ) then 1 else 0 ) True Reg st d s t
exc (st , Rinst "sltu" d s t _)        = ctrl (\x y -> if ( x < y ) then 1 else 0 ) True Reg st d s t
exc (st , Rinst "and" d s t _)         = ctrl (.&.) True Reg st d s t
exc (st , Rinst "or" d s t _)          = ctrl (.|.) True Reg st d s t
exc (st , Rinst "nor" d s t _)         = ctrl (\x y -> xor 0xffffffff $ x .|. y ) True Reg st d s t
exc (st , Rinst "xor" d s t _)         = ctrl xor   True Reg st d s t

exc (st , Rinst "sll" d _ t q)         = ctrl shiftL True Imm st d t q
exc (st , Rinst "sllv" d s t _)        = ctrl shiftL True Reg st d s t
exc (st , Rinst "srl" d _ t q)         = ctrl shiftR True Imm st d t q
exc (st , Rinst "sra" d _ t q)         = ctrl (\x y -> if ( testBit x 31 )
   						     then foldl setBit (x `shiftR` y) [(32-y)..31] else x `shiftR` y)
   					 True Imm st d t q
exc (st , Rinst "srav" d s _ q)        = ctrl (\x y -> if ( testBit x 31 )
   						     then foldl setBit (x `shiftR` y) [(32-y)..31] else x `shiftR` y)
					 True Imm st d s q
exc (st , Rinst "srlv" t s _ q)        = ctrl shiftR True  Imm st t s q
exc (st , Iinst "addi" t s im)         = ctrl (+)    False Imm st t s im
exc (st , Iinst "subi" t s im)         = ctrl (-)    False Imm st t s im
exc (st , Iinst "addiu" t s im)        = ctrl (+)    True  Imm st t s im
exc (st , Iinst "subiu" t s im)        = ctrl (-)    True  Imm st t s im

exc (st , Iinst "slti" t s im)         = ctrl (\x y -> if ( x < y ) then 1 else 0 ) True Imm st t s im
exc (st , Iinst "sltiu" t s im)        = ctrl (\x y -> if ( x < y ) then 1 else 0 ) True Imm st t s im

exc (st , Iinst "andi" t s im)         = ctrl (.&.) True Imm st t s ( im .&. 0xffff )
exc (st , Iinst "ori" t s im)          = ctrl (.|.) True Imm st t s ( im .&. 0xffff )
exc (st , Iinst "xori" t s im )        = ctrl xor   True Imm st t s ( im .&. 0xffff )
exc (st , Iinst "lui" t s im )         = ctrl (\x _-> x `shiftL` 16 ) True Imm st t s ( im .&. 0xffff )

exc (st@(Set (sr,rs,mem)), Iinst "sw" r b o) = let addr = ( (rs !! b) + o )
					       in  case ( addr `mod` 4 ) of
							0 -> Running $ Set (sr, rs, M.insert ((rs !! b) + o) (rs !! r) mem)
							_ -> Interrupt st
exc (st@(Set (sr,rs,mem)), Iinst "lw" r b o) = let addr = ( (rs !! b) + o )
						   p = memlook addr mem
						   rg = ( take r rs ) ++ p `mod` (1 `shift` 32) : drop (r+1) rs
					       in  case ( addr `mod` 4 ) of
							0 -> Running $ Set (sr, rg, mem)
							_ -> Interrupt $ Set (sr, rs, mem)
					       where
					           memlook x m = case (M.lookup x m) of
								      Just a -> a
								      Nothing -> 0

exc (st@(Set ( _ , a , _ ) , _) )      = Interrupt $ Set ( ( 0 , 0 , 0 ) , a , M.empty)

ctrl :: (Int -> Int -> Int) -> Bool -> SndOp -> Set -> Int -> Int -> Int -> Status
ctrl f u i st@(Set(sr,rs,mem)) d s t  = let p = f (rs !! s) (if i == Reg then (rs !! t) else t)
		                            rg = ( take d rs ) ++ p `mod` (1 `shift` 32) : drop (d+1) rs
					    stn = Set (sr, rg, mem)
	              in if p < (1 `shift` 32) || u then Running stn
						    else Interrupt stn

main :: IO()
main = initenv

