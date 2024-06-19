<!-- idris
module README

import Data.Cozippable
import Data.List
import Data.Primitives.Interpolation
import Data.So
import Data.SortedMap
import Data.String
import Data.Zippable
-->

# Cozippable interface

Well-known `Zippable` interface (due to its nature) works on a common subpart of collections being zipped.
Say, when you have

```idris
oneList : List Nat
oneList = [0, 1, 2, 3, 4]

anotherList : List Nat
anotherList = [10, 20, 30]
```

when you `zip` them

```idris
ZippedLists : List Nat
ZippedLists = zipWith (+) oneList anotherList
```

the resulting list has the length of the shortest one:

```idris
ZippedListsContents : ZippedLists = [10, 21, 32]
ZippedListsContents = Refl
```

But what if we would like to manage all the missing information too?
For that we have `cozip` from this library:

```idris
CozippedLists : List Nat
CozippedLists = cozipWith (these' 100 200 (+)) oneList anotherList
```

In this situation the resulting list has the length of the longest given one, giving us the ability to handle missing values.
In this particular example, we manage missing data by adding `100` and `200` in case of missing stuff in the left and right list, correspondingly.

Look at the results:

```idris
CozippedListsContents : CozippedLists = [10, 21, 32, 203, 204]
CozippedListsContents = Refl
```

Using the same interface we can manage other data types too.
For example, imagine you have the following maps:

<!-- idris
Id : Type
Id = Nat
-->

```idris
names : SortedMap Id String
names = fromList [ (0, "John"), (1, "Denis"), (3, "Edwin") ]

scores : SortedMap Id Nat
scores = fromList [ (1, 5), (3, 100), (15, 1) ]
```

Imagine that you want to have composite descriptions without losing any data.
Using `cozip` you can do the following:

```idris
desc : SortedMap Id String
desc = cozipWith f names scores where
  f : These String Nat -> String
  f $ This name = name
  f $ That score = "unnamed user with score \{score}"
  f $ Both name score = "\{name} with score \{score}"
```

We can check the result:

```idris
DescStr : String
DescStr = unlines $ map show $ SortedMap.toList $ desc

Expected : String
Expected = """
  (0, "John")
  (1, "Denis with score 5")
  (3, "Edwin with score 100")
  (15, "unnamed user with score 1")

  """

main_checkMap : IO ()
main_checkMap = printLn $ DescStr == Expected
```

(Notice that we are using runtime comparison because string primitives do not work well at the compile time)
