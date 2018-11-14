{-# OPTIONS_HADDOCK show-extensions #-}
-- |   @'churchEncode'@ and @'churchDecode'@ form
--   an isomorphism between a type and its church representation of a type
--  Simply define an empty instance of @'Church'@ (or using @DeriveAnyClass@)
--  for a type with a 'Generic' instance and defaulting magic will take care of the rest.
--  For example:
--
-- >  {-# LANGUAGE DeriveGeneric #-}
-- >  {-# LANGUAGE DeriveAnyClass #-}
-- >  data MyType = Foo Int Bool | Bar | Baz Char deriving (Generic, Church, Show)
--
-- >>>  churchEncode (Foo 1 True) (\int bool -> int + 1) 0 (const 1)
-- 2
--
-- >>> churchDecode (\foo bar baz -> bar) :: MyType
-- Bar
--
-- Recursive datastructures only unfold one level:
--
-- > data Nat = Z | S Nat deriving (Generic,Church,Show)
--
-- >>> :t churchEncode N
-- r -> (Nat -> r) -> r
--
-- But we can still write recursive folds over such data:
--
-- > nat2int :: Nat -> Int
-- > nat2int a = churchEncode a 0 ((+1) . nat2int)
--
-- >>> nat2int (S (S (S Z)))
-- 3
--
-- Decoding recursive data is more cumbersome due to the 'Rep' wrappings,
-- but fortunately should not need to be done by hand often.
--
-- decodeNat :: (Rep Nat () -> (Rep Nat () -> Rep Nat ()) -> Rep Nat ()) -> Nat
-- decodeNat k = churchDecode (\z s -> k z (s . to))
--
-- >>> decodeNat (\z s -> s . s . s . s $ z)
-- S (S (S (S Z)))

module Church (ChurchRep, Church(churchEncode, churchDecode), churchCast) where

import Church.ToChurch
import Church.FromChurch
import Church.TF
import GHC.Generics

-- | This is the central type for this package. Unfortunately, it's
-- built around type families so it's not so easy to read. A helpful
-- algorithm for figuring out what the 'ChurchRep' of a type @Foo@ is,
--
--      1. For each constructor, write out its type signature
--
--      2. Replace the @Foo@ at the end of each signature with @r@
--
--      3. Join these type signatures together with arrows @(a -> b -> r) -> r -> ...@
--
--      4. Append a final @ -> r@ to the end of this
--
-- For example, for 'Maybe'
--
--   1. @'Nothing' :: Maybe a@ and @'Just' :: a -> Maybe a@.
--
--   2. We then have @r@ and @a -> r@.
--
--   3. Joining these gives @r -> (a -> r)@
--
--   4. @r -> (a -> r) -> r@ is our church representation
type ChurchRep t r = ChurchSum (ToList (StripMeta (Rep t ())) (ListTerm ())) r

class Church a where
  -- | Reify a type to its church representation
  churchEncode :: forall r. a -> ChurchRep a r
  default
    churchEncode :: forall r. (Generic a, GStripMeta (Rep a ()),
                       GList (StripMeta (Rep a ())) (ListTerm ()),
                       GChurchSum (ToList (StripMeta (Rep a ())) (ListTerm ())) r) =>
                  a -> ChurchRep a r
  churchEncode = elim @_ @r
               . (`toList` (ListTerm @()))
               . Just
               . stripMeta
               . from @_ @()

  -- | Create a value from its church representation.
  -- This method may require an explicit signature.
  churchDecode :: ChurchRep a (Rep a ()) -> a
  default
    churchDecode :: (Generic a,
                   (GBuild (MakePaths (Rep a ()) '[] '[])
                    (ChurchRep a (Rep a ()))
                    (Rep a ()))) =>
              ChurchRep a (Rep a ()) -> a
  churchDecode c = to (build @(MakePaths (Rep a ()) '[] '[]) c :: Rep a ())


-- | Since types with the same church representation are
-- identical, we can cast between them.
churchCast :: forall a b. (Church a, Church b, ChurchRep a (Rep b ()) ~ ChurchRep b (Rep b ()))
           => a -> b
churchCast = churchDecode @b . churchEncode @a @(Rep b ())

instance Church Bool
instance Church Ordering
instance Church [a]
instance Church ()
instance Church ((,) a b)
instance Church ((,,) a b c)
instance Church ((,,,) a b c d)
instance Church ((,,,,) a b c d e)
instance Church ((,,,,,) a b c d e f)
instance Church ((,,,,,,) a b c d e f g)
instance Church (Maybe a)
instance Church (Either a b)
