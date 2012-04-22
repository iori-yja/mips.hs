import Data.Bits
import qualified Data.Map as M
import Numeric
--mips primary emuration

data Instraction = Rinst Op Int Int Int Int
                 | Iinst Op Int Int Int
		 | Jinst Op Int 
		 | Meta [Char]
	deriving (Eq, Show, Read)

newtype Set = Set ((Int,Int,Int),[Int],M.Map Int Int) deriving (Eq, Show, Read)
data Context = Interrupt Set | Running Set | Entry Set deriving (Eq, Show, Read)
data Status = Byhand | Auto deriving (Eq, Show, Read)

data SndOp  = Imm | Reg deriving (Eq, Show, Read)
data Op     = Sll | Srl | Sra | Sllv | Srav | Srlv | Add | Addu | Sub | Subu
            | Slt | Sltu | And | Or | Xor | Nor | Addi | Addiu | Slti | Sltiu | Andi | Ori | Xori | Lui | J
                        deriving (Eq, Show, Read)

initenv :: IO ()
initenv = runenv Byhand 0 $ Set ((0,0,0),(fillout 0 32),M.empty)

fillout :: Int -> Int -> [Int]
fillout _ 0 = []
fillout a b = a : fillout a (b - 1)

runenv :: Status -> Int -> Set -> IO ()
runenv st pc rs@(Set (sr,rg,m)) = let runner' = runner st pc rs
				      runner'' = runner' 
		  in case st of
			  Byhand -> do
				  mapM (\x -> putStr $ showHex x " : ") rg
				  putStrLn ""
				  x <- getLine
                               	  case mfetch x of
					      Meta y ->
						      case y of
							   "mem" ->
								   putStr $ M.showTree m
							   "run" ->
								   runenv Auto 0 rs
				              a -> runner' a
			  Auto -> 
				  case M.lookup pc m of
				       Just x -> do
					       mapM (\x -> putStr ( showHex x " : ")) rg
					       putStrLn ""
					       runner' $ decoder x
				       Nothing -> putStrLn "mem empty" >> runenv Byhand pc rs
		  where
		      mfetch :: [Char] -> Instraction
		      mfetch xs = read (parse $ words xs) :: Instraction
   	              parse :: [[Char]] -> [Char]
		      parse (a:b:xs) = unwords $ a : ('"' : b ++ ['"']) : xs

runner :: Status -> Int -> Set -> Instraction -> IO ()
runner st pc rs@(Set (sr,rg,m)) x = let pc' = case x of
					          Jinst "j" addr -> addr
					          _ -> pc + 4
					in do
   	                              	case (exc (rs, x)) of
   	                              	     Interrupt (Set (a,b,mem)) -> do
   	                              		      putStrLn $ "Interrupted at" ++ (show pc)
   	                              		      putStr $ M.showTree $ M.insert pc (iitable x) mem
   	                              		      runenv st pc' $ Set (a, b, M.insert pc (iitable x) mem)
   	                              	     Running (Set (a,b,mem)) -> runenv st pc' $ Set (a, b, M.insert pc (iitable x) mem)

exc :: (Set, Instraction) -> Context
exc (st , Rinst Add d s t _)         = ctrl (+)   True  Reg st d s t
exc (st , Rinst Addu d s t _)        = ctrl (+)   False Reg st d s t
exc (st , Rinst Sub d s t _)         = ctrl (-)   True  Reg st d s t
exc (st , Rinst Subu d s t _)        = ctrl (-)   False Reg st d s t
exc (st , Rinst Slt d s t _)         = ctrl (\x y -> if ( x < y ) then 1 else 0 ) False Reg st d s t
exc (st , Rinst Sltu d s t _)        = ctrl (\x y -> if ( x < y ) then 1 else 0 ) False Reg st d s t
exc (st , Rinst And d s t _)         = ctrl (.&.) False Reg st d s t
exc (st , Rinst Or d s t _)          = ctrl (.|.) False Reg st d s t
exc (st , Rinst Xor d s t _)         = ctrl xor   False Reg st d s t
exc (st , Rinst Nor d s t _)         = ctrl (\x y -> xor 0xffffffff $ x .|. y ) False Reg st d s t

exc (st , Rinst Sll d _ t q)         = ctrl shiftL False Imm st d t q
exc (st , Rinst Srl d _ t q)         = ctrl shiftR False Imm st d t q
exc (st , Rinst Sra d _ t q)         = ctrl (\x y -> if ( testBit x 31 )
   						     then foldl setBit (x `shiftR` y) [(32-y)..31] else x `shiftR` y)
   					 False Imm st d t q
exc (st , Rinst Sllv d s t _)        = ctrl shiftL False Reg st d s t
exc (st , Rinst Srav d s _ q)        = ctrl (\x y -> if ( testBit x 31 )
   						     then foldl setBit (x `shiftR` y) [(32-y)..31] else x `shiftR` y)
					 False Imm st d s q
exc (st , Rinst Srlv t s _ q)        = ctrl shiftR False  Imm st t s q

exc (st , Iinst Addi t s im)         = ctrl (+)    True Imm st t s im
exc (st , Iinst Addiu t s im)        = ctrl (+)    False  Imm st t s im

exc (st , Iinst Slti t s im)         = ctrl (\x y -> if ( x < y ) then 1 else 0 ) False Imm st t s im
exc (st , Iinst Sltiu t s im)        = ctrl (\x y -> if ( x < y ) then 1 else 0 ) False Imm st t s im

exc (st , Iinst Andi t s im)         = ctrl (.&.) False Imm st t s ( im .&. 0xffff )
exc (st , Iinst Ori t s im)          = ctrl (.|.) False Imm st t s ( im .&. 0xffff )
exc (st , Iinst Xori t s im )        = ctrl xor   False Imm st t s ( im .&. 0xffff )
exc (st , Iinst Lui t s im )         = ctrl (\x _-> x `shiftL` 16 ) False Imm st t s ( im .&. 0xffff )

exc (st , Jinst J _ )                = Running st

exc (st@(Set (sr,rs,mem)), Iinst Sw r b o) = let addr = ( (rs !! b) + o )
					       in  case ( addr `mod` 4 ) of
							0 -> Running $ Set (sr, rs, M.insert ((rs !! b) + o) (rs !! r) mem)
							_ -> Interrupt st
exc (st@(Set (sr,rs,mem)), Iinst Lw r b o) = let addr = ( (rs !! b) + o )
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

ctrl :: (Int -> Int -> Int) -> Bool -> SndOp -> Set -> Int -> Int -> Int -> Context
ctrl f u i st@(Set(sr,rs,mem)) d s t  = let p = f (rs !! s) (if i == Reg then (rs !! t) else t)
		                            rg = ( take d rs ) ++ p `mod` (1 `shift` 32) : drop (d+1) rs
					    stn = Set (sr, rg, mem)
	              in if testBit (xor p $ rs !! d) 31 && u then Interrupt stn
						    else Running stn
iitable:: Instraction -> Int
iitable (Rinst "nop" _ _ _ _)          =     0
iitable (Rinst "add" d s t _ )         =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x20
iitable (Rinst "addu" d s t _ )        =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x21
iitable (Rinst "sub" d s t _ )         =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x22
iitable (Rinst "subu" d s t _ )        =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x23
iitable (Rinst "slt" d s t _ )         =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x2a
iitable (Rinst "sltu" d s t _ )        =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x2b
iitable (Rinst "and" d s t _ )         =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x24
iitable (Rinst "or" d s t _ )          =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x25
iitable (Rinst "xor" d s t _ )         =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x26
iitable (Rinst "nor" d s t _ )         =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x27

iitable (Rinst "sll" d _ t q )         =     t `shiftL` 16 .|. d `shiftL` 11 .|. q `shiftL` 6  .|. 0x00
iitable (Rinst "srl" d _ t q )         =     t `shiftL` 16 .|. d `shiftL` 11 .|. q `shiftL` 6  .|. 0x02
iitable (Rinst "sra" d _ t q )         =     t `shiftL` 16 .|. d `shiftL` 11 .|. q `shiftL` 6  .|. 0x03
iitable (Rinst "sllv" d s t _ )        =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x04
iitable (Rinst "srav" d s t _ )        =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x07
iitable (Rinst "srlv" d s t _ )        =     s `shiftL` 21 .|. t `shiftL` 16 .|. d `shiftL` 11 .|. 0x06

iitable (Iinst "addi" t s im )         =  0x08 `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "addiu" t s im )        =  0x09 `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "slti" t s im )         =  0x0a `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "sltiu" t s im )        =  0x0b `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "andi" t s im )         =  0x0c `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "ori" t s im )          =  0x0d `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "xori" t s im )         =  0x0e `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im
iitable (Iinst "lui" t s im )          =  0x0f `shiftL` 26 .|. s `shiftL` 21 .|. t `shiftL` 16 .|. im

iitable (Jinst "J" addr)               = 0x02 `shiftL` 26 .|. 0x3fffffff .&. addr

decoder :: Int -> Instraction
decoder 0     = Meta "mem"
decoder inst  = case (shiftR ( 0xfc000000 .&. inst ) 26) of
		    0 -> Rinst ( ( \inst -> case ( inst .&. 0x3f ) of
	         			    0x00 -> "sll"  
                                            0x02 -> "srl" 
                                            0x03 -> "sra" 
                                            0x04 -> "sllv"
                                            0x07 -> "srav"
                                            0x06 -> "srlv"
                                            0x20 -> "add" 
                                            0x21 -> "addu"
	         		            0x22 -> "sub" 
	         		            0x23 -> "subu"
                                            0x2a -> "slt" 
                                            0x2b -> "sltu"
                                            0x24 -> "and" 
                                            0x25 -> "or" 
                                            0x26 -> "xor" 
                                            0x27 -> "nor"
				   ) inst ) (cut inst 11) (cut inst 21) (cut inst 16) (cut inst 6)
		    0x2 -> Jinst "J"     (0x3fffffff .&. inst)
		    0x8 -> Iinst "addi"  (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0x9 -> Iinst "addiu" (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0xa -> Iinst "slti"  (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0xb -> Iinst "sltiu" (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0xc -> Iinst "andi"  (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0xd -> Iinst "ori"   (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0xe -> Iinst "xori"  (cut inst 16) (cut inst 21) (0xffff .&. inst)
		    0xf -> Iinst "lui"   (cut inst 16) (cut inst 21) (0xffff .&. inst)
	        where
		    cut x y = 0x1f .&. (shiftR x y) --inst offset

main :: IO()
main = initenv

