module Interfaces.Listable

import Data.Fin

public export
interface Listable a where
    allValues : List a

public export
fixpoints : (Listable x) => (x -> x -> Bool) -> List x
fixpoints f = filter (\x => f x x) allValues


public export
implementation Listable () where
  allValues = [()]


public export
implementation (Listable a, Listable b) => Listable (a, b) where
  allValues = [ (x, y) | x <- allValues, y <- allValues ]


public export
Listable a => Listable b => Listable (Either a b) where
  allValues = map Left allValues ++ map Right allValues

public export
Listable a => Listable b => Listable (a' : a ** b) where
  allValues = [ (x ** y) | x <- allValues, y <- allValues ]

public export
implementation {n : Nat} -> Listable (Fin n) where
  allValues = allFins n

