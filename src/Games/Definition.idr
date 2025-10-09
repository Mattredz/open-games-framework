module Games.Definition

import Optics.Lens
import Games.Arena
import Players.Definition

public export
record Game (profiles : Type) (actions : Type) (utility : Type) 
                (states : Type) (copayoffs : states -> Type)
                (moves : Type) (payoffs : moves -> Type) where
  constructor MkGame
  player : Player profiles actions utility
  arena  : Arena (MkCo actions (\a => utility)) (MkCo states copayoffs) (MkCo moves payoffs)