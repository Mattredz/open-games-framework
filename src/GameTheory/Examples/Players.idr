module GameTheory.Examples.Players

import Interfaces.Listable
import GameTheory.Core

||| Argmax as a player's best response
|||
||| Specialized version of argmax for game theory contexts.
public export
Argmax : (Listable a, Ord u, Eq u) => 
         Player a a u
Argmax = MkDLens id (\a, k => argmax k)

