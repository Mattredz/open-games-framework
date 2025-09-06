module Games.Definition

import Container.Definition
import Lens.Definition
import Players.Definition
import Games.Arena

public export
record Game (profiles : Type ) (pq, xs, yr : Container) where
  constructor MkGame
  player : Player profiles (shape pq) (position pq)
  arena  : Arena pq xs yr