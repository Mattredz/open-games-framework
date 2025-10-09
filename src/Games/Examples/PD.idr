module Games.Examples.PD

import Optics.Lens
import Players.Definition
import Players.Argmax
import Interfaces.Listable
import Games.Context
import Games.State
import Games.CoState
import Games.Definition
import Games.Equilibria
import Games.Arena


public export
data MovesPD = C | D

Listable MovesPD where
  allValues = [C, D]


PDCont : Cont
PDCont = MkCo (MovesPD, MovesPD) (const (Int, Int))

payoffPD : (MovesPD, MovesPD) -> (Int, Int)
payoffPD (C, C) = (3, 3)
payoffPD (C, D) = (5, 0)
payoffPD (D, C) = (0, 5)
payoffPD (D, D) = (1, 1)

contextPD : Context (MkCo () (const ())) PDCont
contextPD = MkContext (scalarToState ()) (funToCostate payoffPD)

gamePD : Game (MovesPD, MovesPD) (MovesPD, MovesPD) (Int, Int) () (const ()) (MovesPD, MovesPD) (const (Int, Int))
gamePD = MkGame (nash argmaxPlayer argmaxPlayer) corner

equilibriaPD : List (MovesPD, MovesPD)
equilibriaPD = equilibrium gamePD contextPD

