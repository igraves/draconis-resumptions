module Resumption

{-
data Res a = Done a | Pause (Res a)
-}

data Res : Type -> Type where
  Done  : a -> Res a
  Pause : (Res a) -> (Res a)


instance Functor Res where
  map f (Done a)  = Done (f a)
  map f (Pause r) = Pause (map f r)

instance Applicative Res where
  pure a            = Done a
  (Done f)  <$> res = map f res
  (Pause p) <$> res = p <$> res

instance Monad Res where
  (Done a)  >>= f = f a
  (Pause a) >>= f = a >>= f


{-
data React i o a = Done a | Pause o (i -> o)
-}


data React : Type -> Type -> Type -> Type where
  D : a -> React i o a
  P : o -> (i -> React i o a) -> React i o a

instance Functor (React i o) where
  map f (D a)   = D (f a)
  map f (P o r) = P o (\i => map f (r i))

instance Applicative (React i o) where
  pure a = D a
  (D f)   <$> res = map f res
  (P o f) <$> res = P o (\i => (f i) <$> res)

instance Monad (React i o) where
  (D a)   >>= f = f a
  (P o r) >>= f = P o (\i => (r i) >>= f)


par : React i o a -> React j n a -> React (i,j) (o,n) a
par (D a) _ = D a
par _ (D a) = D a
par (P o r1) (P n r2) = P (o,n) (\(i1,i2) => par (r1 i1) (r2 i2))

refold : (o1 -> o2) -> (i2 -> o1 -> i1) -> React i1 o1 a -> React i2 o2 a
refold _ _ (D a)      = D a
refold fo fi (P o ii) = P (fo o) (\i2 => refold fo fi (ii (fi i2 o)))

parvect : React (Vect k s) (Vect k' t) a -> 
          React (Vect n s) (Vect n' t) a ->
          React (Vect (k+n) s) (Vect (k'+n') t) a
parvect (D a) _ = D a
parvect _ (D a) = D a
parvect {k} (P ol r1) (P or r2) = P (ol ++ or) (\i => let (i1,i2) = splitAt k i
                                                   in parvect (r1 i1) (r2 i2))
