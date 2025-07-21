module Interfaces.Listable

public export
interface Listable a where
    allValues : List a

public export
fixpoints : (Listable x) => (x -> x -> Bool) -> List x
fixpoints f = filter (\x => f x x) allValues

public export
(Listable a, Listable b) => Listable ((a), b) where
    allValues {a} {b} = [ (x, y) | x <- allValues, y <- allValues ]
