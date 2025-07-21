module Players.Argmax

import Players.Definition
import Interfaces.Listable
import Container.Definition
import Container.Morphism
import Lens.Definition

public export
maximum : Ord a => a -> List a -> a
maximum = foldl max

public export
argmax : Listable x => Ord a => Eq a
    =>  (x -> a) -> x -> Bool
argmax f x = f x == maximum (f x) (map f allValues)

public export
argmaxPlayer :
  (Listable s, Ord (u), Eq u) =>  Player s s (\s => u)
argmaxPlayer = MkPlayer (id !> (\x => ?coplay))