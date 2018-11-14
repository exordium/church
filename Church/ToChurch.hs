{-# LANGUAGE TypeFamilies,          TypeOperators,     UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables                                            #-}
module Church.ToChurch where
import GHC.Generics
import Church.TF
import Prelude


-- | Eliminate a product type
type family ChurchProd v c where
  ChurchProd (K1 a t p)    c = t -> c
  ChurchProd (U1 p)        c = c
  ChurchProd ((:*:) l r p) c = ChurchProd (l p) (ChurchProd (r p) c)
  ChurchProd (ListTerm p)  c = c

-- | Reorder a product type into a list rather than
-- a balanced tree
type family ToListProd v rest where
  ToListProd ((:*:) l r' p) r = ToListProd (l p) (ToListProd (r' p) r)
  ToListProd (K1 a t p)     r = (K1 a t     :*: WithoutParam r) p
  ToListProd (U1 p)         r = U1 p

-- | Given a product type and a tail, reorder the product type
-- into a list according to 'ToListProd'.
class GListProd a r where
  toListProd :: a -> r -> ToListProd a r
instance (WithoutParam r) p ~ r => GListProd (U1 p) r where
  toListProd = const
instance (WithoutParam r) p ~ r => GListProd (K1 a t p) r where
  toListProd = (:*:)
instance (GListProd (l p) (ToListProd (r' p) r), GListProd (r' p) r) => GListProd ((:*:) l r' p) r where
  toListProd (l :*: r) rest = toListProd l (toListProd r rest)

-- | Eliminate a product type
class GChurchProd a where prod :: a -> ChurchProd a r -> r
instance GChurchProd (U1 p) where prod _ f = f
instance GChurchProd (K1 a t p) where prod (K1 r) f = f r
instance GChurchProd (r p) => GChurchProd ((K1 a t :*: r) p) where
  prod (K1 l :*: r) f = prod r (f l)
instance GChurchProd (ListTerm p) where prod _ f = f

-- | Reorder a sum type into a list rather than a balanced
-- tree of '(:+:)'s.
type family ToList v rest where
  ToList ((:+:) l r' p) r = ToList (l p) (ToList (r' p) r)
  ToList (K1 a t p)     r = (K1 a t     :+: WithoutParam r) p
  ToList ((:*:) l r' p) r = ((l :*: r') :+: WithoutParam r) p
  ToList (U1 p)         r = (U1         :+: WithoutParam r) p

-- | Given an optional sum type and a tail, reorder the
-- sum type into a list like structure.
class GList a r where
  toList :: Maybe a -> r -> ToList a r
instance (WithoutParam r) p ~ r => GList (U1 p) r where
  toList Nothing  r = R1 r
  toList (Just a) _ = L1 a
instance (WithoutParam r) p ~ r => GList (K1 a t p) r where
  toList Nothing  r = R1 r
  toList (Just a) _ = L1 a
instance (WithoutParam r) p ~ r => GList ((l :*: r') p) r where
  toList Nothing  r = R1 r
  toList (Just a) _ = L1 a
instance (GList (l p) (ToList (r' p) r),
          GList (r' p) r) => GList ((l :+: r') p) r where
  toList (Just sum@(L1 l)) r = toList (Just l) (toList (rNot sum) r)
    where rNot :: forall l r p. (l :+: r) p -> Maybe (r p)
          rNot _ = Nothing
  toList (Just sum@(R1 r')) r = toList (lNot sum) (toList (Just r') r)
    where lNot :: forall l r p. (l :+: r) p -> Maybe (l p)
          lNot _ = Nothing
  toList m r = toList (lNot m) (toList (rNot m) r)
    where lNot :: forall l r p. Maybe ((:+:) l r p) -> Maybe (l p)
          lNot _ = Nothing
          rNot :: forall l r p. Maybe ((:+:) l r p) -> Maybe (r p)
          rNot _ = Nothing

-- | The actual church representation of a type
-- once it's been properly reordered.
type family ChurchSum v c where
  ChurchSum ((:+:) l r p) c = ChurchProd (ToListProd (l p) (ListTerm ())) c -> ChurchSum (r p) c
  ChurchSum (ListTerm p) c  = c

-- | An odd version of `const` which will swallow
-- all arguments to a church representation and return
-- a value previously given to it.
class    Swallow a where swallow :: c -> ChurchSum a c
instance Swallow (ListTerm p) where swallow c = c
instance Swallow (r p) => Swallow ((:+:) l r p) where swallow c = \_ -> swallow @(r p) c

-- | Transform a reordered sum value into a church representation.

class GChurchSum a r where elim :: a -> ChurchSum a r
instance (GListProd (l p) (ListTerm ()), GChurchProd (ToListProd (l p) (ListTerm ())),
          GChurchSum (r' p) r, Swallow (r' p)) =>
         GChurchSum ((l :+: r') p) r where
  elim  sum@(L1 l) = \f -> swallow @(r' p) (prod @_ @r (toListProd l (ListTerm :: ListTerm ())) f)
  elim (R1 r) = \_ -> elim @_ @r r
instance GChurchSum (ListTerm p) r where elim _ = error "Malformed generic instance"
