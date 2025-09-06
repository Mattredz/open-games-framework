module Games.Examples.PD

import Lens.Definition
import Container.Definition
import Container.Morphism
import Container.Product
import Container.RDiff
import Lens.Composition
import Lens.Product
import Players.Definition
import Players.Argmax
import Interfaces.Listable
import Context
import State.Definition
import CoState.Definition
import Games.Definition
import Games.Equilibria
import Games.Arena

%hide Prelude.Ops.infixl.(*)

public export
data MovesPD = C | D

Listable MovesPD where
  allValues = [C, D]

corner : (c : Container) -> ParaLens c CUnit c
corner c = MkPLens
    const
    (\_, _, r => ((), r))

ContPD : Container
ContPD = CMk ((MovesPD, MovesPD) ** (\_ => (Int, Int)))

ArenaPD : ParaLens ContPD CUnit ContPD
ArenaPD = corner ContPD

payoffPD : (MovesPD, MovesPD) -> (Int, Int)
payoffPD (C, C) = (3, 3)
payoffPD (C, D) = (0, 5)
payoffPD (D, C) = (5, 0)
payoffPD (D, D) = (1, 1)

PlayerPD : Player MovesPD MovesPD (\_ => Int)
PlayerPD = argmaxPlayer

PlayersPD : Player (MovesPD, MovesPD) (MovesPD, MovesPD) (\_ => (Int, Int))
PlayersPD = PlayerPD #### PlayerPD

contextPD : Context CUnit ContPD
contextPD = MkContext (scalarToState ()) (funToCostate payoffPD)

gamePD : Game (MovesPD, MovesPD) ContPD CUnit ContPD
gamePD = MkGame PlayersPD ArenaPD

equilibriaPD : ?
equilibriaPD = equilibrium gamePD contextPD