module Games.Definition

import Optics.Lens
import Games.Arena
import Players.Definition

public export
record Game (profiles : Type) (actions : Type) (utility : actions -> Type) (xs : ParaCont (MkCo actions utility)) (yr : Cont) where
  constructor MkGame
  player : Player profiles actions utility
  arena  : Arena (MkCo actions utility) xs yr