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
payoffPD (C, C) = (1, 1)
payoffPD (C, D) = (5, 0)
payoffPD (D, C) = (0, 5)
payoffPD (D, D) = (3, 3)

contextPD : Context (MkCo () (const ())) PDCont
contextPD = MkContext (scalarToState ()) (funToCostate payoffPD)

playerPD : Player MovesPD MovesPD (const Int)
playerPD = argmaxPlayer

nash_gamePD : Game (MovesPD, MovesPD) (MovesPD, MovesPD) (const (Int, Int) )(MkParaCont (\p => ()) (\_ => const ())) PDCont
nash_gamePD = MkGame (nash playerPD playerPD) corner

equilibriaPD : List (MovesPD, MovesPD)
equilibriaPD = equilibrium nash_gamePD contextPD

socialUtilityPD : (MovesPD, MovesPD) -> Int
socialUtilityPD moves = let (u1, u2) = payoffPD moves in u1 + u2

contextHicksPD : Context (MkCo () (const ())) (MkCo (MovesPD, MovesPD) (const Int))
contextHicksPD = MkContext (scalarToState ()) (funToCostate socialUtilityPD)

hicks_gamePD : Game (MovesPD, MovesPD) (MovesPD, MovesPD) (const Int) (MkParaCont (\p => ()) (\_ => const ())) (MkCo (MovesPD, MovesPD) (const Int))
hicks_gamePD = MkGame argmaxPlayer corner


equilibriaHicksPD : List (MovesPD, MovesPD)
equilibriaHicksPD = equilibrium hicks_gamePD contextHicksPD