module Games.Context

import Container.Definition
import Lens.Definition
import Games.State
import Games.CoState

public export
record Context (xs, yr : Container) where
  constructor MkContext
  state   : State xs
  coState : CoState yr

