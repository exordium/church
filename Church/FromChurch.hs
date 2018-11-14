{-# language UndecidableInstances #-}
module Church.FromChurch where
import GHC.Generics
import Church.TF
import Prelude

data Traverse a c = Meta a c a | InL a a | InR a a | Term a

type family PathArg (t :: [Traverse * Meta]) where
  PathArg (Term a     ': '[] ) = a
  PathArg ('Meta a b p ': rest) = PathArg rest
  PathArg (InR l p    ': rest) = PathArg rest
  PathArg (InL r p    ': rest) = PathArg rest

-- | Construct a product type where all the fields are
-- _|_
class GEmpty a where empty :: a
instance GEmpty (U1 p) where empty = U1
instance GEmpty (K1 a t p) where empty = K1 (error "Error! The impossible has happened.")
instance GEmpty (f p) => GEmpty (M1 a b f p) where empty = M1 empty
instance (GEmpty (l p), GEmpty (r p)) => GEmpty ((:*:) l r p) where empty = empty :*: empty

type family MakeProdPaths v (m :: [Traverse * Meta]) (r :: [ [Traverse * Meta] ]) :: [[Traverse * Meta]] where
  MakeProdPaths (K1 a t p) s all    = Reverse (Term (K1 a t p) ': s) ': all
  MakeProdPaths (M1 a b f p) s all  = MakeProdPaths (f p) ('Meta a b p ': s) all
  MakeProdPaths ((:*:) l r p) s all =
    Append (MakeProdPaths (l p) (InL (r p) p ': s) '[])
            (Append (MakeProdPaths (r p) (InR (l p) p ': s) '[]) all)

class GUpdate (path :: [Traverse * Meta]) a where update :: a -> PathArg path -> a
instance GUpdate (Term (K1 a t p) ': '[]) (K1 a t p) where update _ a = a
instance GUpdate rest (l p) => GUpdate (InL (r p) p ': rest) ((:*:) l r p) where
  update (l :*: r) a = update @rest l a :*: r
instance GUpdate rest (r p) => GUpdate (InR (l p) p ': rest) ((:*:) l r p) where
  update (l :*: r) a = l :*: update @rest r a 
instance GUpdate rest (f p) => GUpdate ('Meta a b p ': rest) (M1 a b f p) where
  update (M1 f) a = M1 (update @rest f a)

type family Fill (paths :: [[Traverse * Meta]]) r where
  Fill (x ': xs) r = StripK (PathArg x) -> Fill xs r
  Fill '[] r = r

class GFill (paths :: [[Traverse * Meta]]) a where
  fill :: (a -> r) -> a -> Fill paths r
instance GFill '[] a where
  fill f a = f a
instance (PathArg x ~ K1 m t p, StripK (PathArg x) ~ t, GUpdate x a, GFill xs a) =>
         GFill (x ': xs) a where
  fill f a = \x -> fill @xs f $ update @x a (K1 x)

type family MakePaths v (m :: [Traverse * Meta]) (r :: [ [Traverse * Meta] ]) :: [[Traverse * Meta]] where
  MakePaths ((:+:) l r p) s all =
    Append (MakePaths (l p) (InL (r p) p ': s) '[])
            (Append (MakePaths (r p) (InR (l p) p ': s) '[]) all)
  MakePaths (M1 a b f p) s all  = MakePaths (f p) ('Meta a b p ': s) all
  MakePaths (K1 a t p) s all    =  Reverse (Term (K1 a t p) ': s)    ': all
  MakePaths (U1 p) s all        =  Reverse (Term (U1 p) ': s)        ': all
  MakePaths ((:*:) l r p) s all =  Reverse (Term ((:*:) l r p) ': s) ': all

type family ReconstructPath (t :: [Traverse * Meta]) where
  ReconstructPath (InL r p  ': rest) = (WithoutParam (ReconstructPath rest) :+: WithoutParam r) p
  ReconstructPath (InR l p  ': rest) = (WithoutParam l :+: WithoutParam (ReconstructPath rest)) p
  ReconstructPath ('Meta a b p ': rest) = M1 a b (WithoutParam (ReconstructPath rest)) p
  ReconstructPath (Term a     ': '[])  = a

class GPath' (p :: [Traverse * Meta]) where path' :: PathArg p -> ReconstructPath p
instance GPath' (Term a ': '[]) where path' = id
instance ((WithoutParam (ReconstructPath rest)) p ~ ReconstructPath rest, GPath' rest)
         => GPath' (InR r p ': rest) where path' a = R1 $ path' @rest a
instance ((WithoutParam (ReconstructPath rest)) p ~ ReconstructPath rest, GPath' rest)
         => GPath' (InL l p ': rest) where path' a = L1 $ path' @rest a
instance ((WithoutParam (ReconstructPath rest)) p ~ ReconstructPath rest, GPath' rest)
         => GPath' ('Meta a b p ': rest) where path' a = M1 $ path' @rest a

class GBuild (paths :: [[Traverse * Meta]]) f r where build :: f -> r
-- | Unit case. This represents constructors with no arguments
instance (ReconstructPath x ~ r, GPath' x, GBuild xs f' r, PathArg x ~ U1 p)
         => GBuild (x ': xs) (r -> f') r where build f = build @xs $ f (path' @x U1)
instance ((f -> g) ~ Fill (MakeProdPaths (PathArg x) '[] '[]) r,
          ReconstructPath x ~ r, GEmpty (PathArg x), GBuild xs f' r,
          (GFill (MakeProdPaths (PathArg x) '[] '[]) (PathArg x)),
          GPath' x)
         => GBuild (x ': xs) ((f -> g) -> f') r where
  build f = build @xs $ f (fill @(MakeProdPaths (PathArg x) '[] '[]) (path' @x) empty)
instance GBuild '[] r r where build = id
