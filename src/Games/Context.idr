module Games.Context

import Games.State
import Games.CoState
import Optics.Lens

public export
record Context xs yr where
  constructor MkContext
  state : State xs
  costate : CoState yr


