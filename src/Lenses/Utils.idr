|||
||| This module provides general-purpose utilities for working with
||| ordered types and finding optimal values.
module Lenses.Utils

import Data.List
import Lenses.ParaDLens
import Interfaces.Listable

%default total

||| Maximum of a list with an initial value
|||
||| Computes the maximum element in a list, using the initial value
||| as the starting point for the fold.
|||
||| @ init The initial value
||| @ xs The list to search
public export
maximum : Ord a => a -> List a -> a
maximum = foldl max

||| Argument maximizer predicate
|||
||| Returns a predicate that checks if a given value maximizes the function f.
||| For finite enumerable types, this computes the argmax over all possible values.
|||
||| @ f The function to maximize
public export
argmax : (Listable x, Ord a, Eq a) => (x -> a) -> x -> Bool
argmax f x = (f x) == maximum (f x) (map f allValues ) 

