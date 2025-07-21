module Context

import Container.Definition
import Lens.Definition
import State.Definition
import CoState.Definition

public export
record Context (xs, yr : Container) where
  constructor MkContext
  state   : State xs
  coState : CoState yr

