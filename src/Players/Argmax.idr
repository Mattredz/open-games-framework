module Players.Argmax

import Interfaces.Listable
import Optics.Lens
import Players.Definition

public export
maximum : Ord a => a -> List a -> a
maximum = foldl max

public export
argmax : Listable x => Ord a => Eq a
    =>  (x -> a) -> (x -> Bool)
argmax f x = f x == maximum (f x) (map f allValues)

public export
argmaxPlayer : {s, u : Type} -> (Listable s, Ord u, Eq u) => Player s s u
argmaxPlayer = MkDLens
                id
                (\_, k => argmax k )