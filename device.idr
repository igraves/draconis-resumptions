import Resumption


data Bit : Type where
  Zero : Bit 
  One  : Bit 


xor : [static] Bit -> [static] Bit -> Bit
xor Zero Zero = Zero
xor One One   = Zero
xor _   _     = One

--Bit 8 type synonym
Bit8 : Type 
Bit8 = Vect 8 Bit 


zeros : Bit8
zeros = Zero :: Zero :: Zero :: Zero :: Zero :: Zero :: Zero :: Zero :: Nil

parity : (Vect (S(n)) Bit) ->  Bit
parity (x :: Nil) = x
parity (x :: xs)  = parity' x xs
  where
    parity' : Bit -> (Vect n Bit) -> Bit
    parity' b Nil = b
    parity' b (x :: xs) = parity' (b `xor` x) xs



device : [static] (a -> b) -> (a -> React a b ())
device f = \i => P (f i) (device f) 


s : Bit8 -> React Bit8 Bit () 
s = device parity --zeros


pcrap : Bit
pcrap = parity zeros
