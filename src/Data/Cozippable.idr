module Data.Cozippable

import Control.Monad.Error.Interface

import Data.Colist
import Data.Colist1
import Data.Either
import Data.List.Lazy
import Data.List1
import public Data.These
import Data.SortedSet
import Data.SortedMap
import Data.Vect

%default total

||| The `Cozippable` interface describes how you can combine and split elements of a parameterised type, those elements may contain not equal amount of information.
|||
||| The easiest example is `List`. When you `zip` them using standard `Zippable` interface, only their prefixes of commit length are taken into account,
||| or else it is impossible to fulfill the interface.
||| Sometimes we may want to deal with such lack of information explicitly.
||| That's why zipping function of the `Cozippable` interface takes `These` data type, which is an inclusive "or", i.e. either one of elements, or both of them.
public export
interface Cozippable z where

  cozipWith : (These a b -> c) -> z a -> z b -> z c

  cozip : z a -> z b -> z (These a b)
  cozip = cozipWith id

  uncozipWith : (a -> These b c) -> z a -> These (z b) (z c)

  uncozip : z (These a b) -> These (z a) (z b)
  uncozip = uncozipWith id

export infixr 6 `cozip` -- same as `zip` from `Data.Zippable`

public export
cozipWith' : Cozippable z => Functor z => (These a b -> c) -> These (z a) (z b) -> z c
cozipWith' f (This x)   = map (f . This) x
cozipWith' f (That x)   = map (f . That) x
cozipWith' f (Both x y) = cozipWith f x y

public export
cozip' : Cozippable z => Functor z => These (z a) (z b) -> z (These a b)
cozip' = cozipWith' id

public export
[Compose] Cozippable f => Cozippable g => Functor g => Cozippable (f . g) where
  cozipWith f = cozipWith $ cozipWith' f
  uncozipWith f = uncozipWith $ uncozipWith f

--- Particular case ---

||| Cozip two cozippables taking a value from each one, and combining corresponding values if it is present in both using given function
export %inline
comergeWith : Cozippable z => (a -> a -> a) -> z a -> z a -> z a
comergeWith = cozipWith . these id id

public export %inline
comerge : Semigroup a => Cozippable z => z a -> z a -> z a
comerge = comergeWith (<+>)

export infixr 6 `comerge` -- same as `cozip` above

--- Particular implementations ---

public export
Semigroup a => Cozippable (Pair a) where
  cozipWith f (x, y) (x', y') = (x <+> x', f $ Both y y')
  uncozipWith f (x, y) = bimap (x,) (x,) $ f y

public export
Cozippable Maybe where
  cozipWith _ Nothing  Nothing  = Nothing
  cozipWith f Nothing  (Just y) = Just $ f $ That y
  cozipWith f (Just x) Nothing  = Just $ f $ This x
  cozipWith f (Just x) (Just y) = Just $ f $ Both x y

  uncozipWith f Nothing  = Both Nothing Nothing
  uncozipWith f (Just x) = bimap Just Just $ f x

-- Prefers left `Left` when both are `Left`s, as default `Zippable` implementation
public export
Cozippable (Either a) where
  cozipWith _ (Left x)  (Left _)  = Left x
  cozipWith f (Left _)  (Right y) = Right $ f $ That y
  cozipWith f (Right x) (Left _)  = Right $ f $ This x
  cozipWith f (Right x) (Right y) = Right $ f $ Both x y

  uncozipWith f (Left x)  = Both (Left x) (Left x)
  uncozipWith f (Right x) = bimap Right Right $ f x

-- Combines both `Left`s when there are both of them
public export
[CombineLeft] Semigroup a => Cozippable (Either a) where
  cozipWith _ (Left x)  (Left y)  = Left $ x <+> y
  cozipWith f (Left _)  (Right y) = Right $ f $ That y
  cozipWith f (Right x) (Left _)  = Right $ f $ This x
  cozipWith f (Right x) (Right y) = Right $ f $ Both x y

  uncozipWith f (Left x)  = Both (Left x) (Left x)
  uncozipWith f (Right x) = bimap Right Right $ f x

public export
Semigroup a => Cozippable (These a) where
  cozipWith f (This x)   (This y)   = This $ x <+> y
  cozipWith f (This x)   (That y)   = That $ f $ That y
  cozipWith f (This x)   (Both y z) = Both (x <+> y) $ f $ That z
  cozipWith f (That x)   (This y)   = Both y $ f $ This x
  cozipWith f (That x)   (That y)   = That $ f $ Both x y
  cozipWith f (That x)   (Both y z) = Both y $ f $ Both x z
  cozipWith f (Both x z) (This y)   = Both (x <+> y) $ f $ This z
  cozipWith f (Both x z) (That y)   = Both x $ f $ Both z y
  cozipWith f (Both x z) (Both y w) = Both (x <+> y) $ f $ Both z w

  uncozipWith f (This x)   = Both (This x) (This x)
  uncozipWith f (That x)   = bimap That That $ f x
  uncozipWith f (Both x y) = bimap (Both x) (Both x) $ f y

public export
Cozippable List where
  cozipWith f []      []      = []
  cozipWith f []      (y::ys) = f (That y) :: cozipWith f [] ys
  cozipWith f (x::xs) []      = f (This x) :: cozipWith f xs []
  cozipWith f (x::xs) (y::ys) = f (Both x y) :: cozipWith f xs ys

  uncozipWith f []      = Both [] []
  uncozipWith f (x::xs) = do
    let sub = uncozipWith f xs
    case f x of
      This y   => mapFst (y::) sub
      That y   => mapSnd (y::) sub
      Both y z => bimap (y::) (z::) sub

public export
Cozippable SnocList where
  cozipWith f [<]     [<]     = [<]
  cozipWith f [<]     (sy:<y) = cozipWith f [<] sy :< f (That y)
  cozipWith f (sx:<x) [<]     = cozipWith f sx [<] :< f (This x)
  cozipWith f (sx:<x) (sy:<y) = cozipWith f sx sy :< f (Both x y)

  uncozipWith f [<]     = Both [<] [<]
  uncozipWith f (sx:<x) = do
    let sub = uncozipWith f sx
    case f x of
      This y   => mapFst (:<y) sub
      That y   => mapSnd (:<y) sub
      Both y z => bimap (:<y) (:<z) sub

public export
Cozippable List1 where
  cozipWith f (x:::xs) (y:::ys) = f (Both x y) ::: cozipWith f xs ys
  uncozipWith f (x:::xs) = case (f x, uncozipWith f xs) of
    (This y  , This zs)         => This $ y:::zs
    (This y  , That [])         => This $ singleton y
    (This y  , That $ z::zs)    => Both (singleton y) (z:::zs)
    (This y  , Both zs [])      => This $ y:::zs
    (This y  , Both zs (w::ws)) => Both (y:::zs) (w:::ws)
    (That y  , This [])         => That $ singleton y
    (That y  , This (z::zs))    => Both (z:::zs) (singleton y)
    (That y  , That zs)         => That $ y:::zs
    (That y  , Both [] ws)      => That $ y:::ws
    (That y  , Both (z::zs) ws) => Both (z:::zs) (y:::ws)
    (Both y w, This zs)         => Both (y:::zs) (singleton w)
    (Both y w, That zs)         => Both (singleton y) (w:::zs)
    (Both y w, Both zs vs)      => Both (y:::zs) (w:::vs)

public export
[VectMaybe] Cozippable (Vect n . Maybe) where
  cozipWith f []      []      = []
  cozipWith f (x::xs) (y::ys) = cozipWith f x y :: cozipWith @{VectMaybe} f xs ys

  uncozipWith f []      = Both [] []
  uncozipWith f (x::xs) = do
    let (l, r) = fromBoth Nothing Nothing $ uncozipWith f x
    bimap (l::) (r::) $ uncozipWith @{VectMaybe} f xs

public export
Cozippable LazyList where
  cozipWith f []      []      = []
  cozipWith f []      (y::ys) = f (That y) :: cozipWith f [] ys
  cozipWith f (x::xs) []      = f (This x) :: cozipWith f xs []
  cozipWith f (x::xs) (y::ys) = f (Both x y) :: cozipWith f xs ys

  uncozipWith f []      = Both [] []
  uncozipWith f (x::xs) = do
    let left  : Lazy (LazyList b) = fromMaybe [] $ fromThis $ uncozipWith f xs
    let right : Lazy (LazyList c) = fromMaybe [] $ fromThat $ uncozipWith f xs
    case f x of
      This y   => Both (y::left) right
      That y   => Both left (y::right)
      Both y z => Both (y::left) (z::right)

public export
Ord k => Cozippable (SortedMap k) where
  cozipWith f mx my = SortedMap.fromList $ merge (SortedMap.toList mx) (SortedMap.toList my) where
    merge : List (k, a) -> List (k, b) -> List (k, c)
    merge [] [] = []
    merge [] ys = mapSnd (f . That) <$> ys
    merge xs [] = mapSnd (f . This) <$> xs
    merge xxs@((kx,x)::xs) yys@((ky,y)::ys) =
      if kx < ky then (kx, f $ This x) :: merge xs yys
      else if kx == ky then (kx, f $ Both x y) :: merge xs ys
      else (ky, f $ That y) :: merge xxs ys

  uncozipWith f mx = do
    let xs = mapSnd f <$> SortedMap.toList mx
    let ls = flip mapMaybe xs $ \kbc => (Builtin.fst kbc,) <$> fromThis (Builtin.snd kbc)
    let rs = flip mapMaybe xs $ \kbc => (Builtin.fst kbc,) <$> fromThat (Builtin.snd kbc)
    Both (fromList ls) (fromList rs)

public export
[MonadError] MonadError e m => Monoid e => Cozippable m where
  cozipWith f ex ey = liftEither =<< cozipWith f <$> tryError ex <*> tryError ey

  uncozipWith f ex = do
    let left  = liftEither . maybeToEither (neutral {ty=e}) . fromThis . f =<< ex
    let right = liftEither . maybeToEither (neutral {ty=e}) . fromThat . f =<< ex
    Both left right
