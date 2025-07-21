module Games.Examples.PD

import Lens.Definition
import Container.Definition
import Container.Morphism
import Container.Product
import Lens.Composition
import Lens.Tensor
import Players.Definition
import Players.Argmax
import Interfaces.Listable
import Arena
import Context
import State.Definition
import CoState.Definition
import Games.Definition

%hide Prelude.Ops.infixl.(*)

public export
data MovesPD = C | D

Listable MovesPD where
  allValues = [C, D]

corner : (c : Container) -> ParaLens c MkCUnit c
corner c = MkParaLens
    const
    (\_, _, r => ((), r))

ContPD : Container
ContPD = MkCont MovesPD (const Int)

cornerPD : ParaLens ContPD MkCUnit ContPD
cornerPD = corner ContPD

ArenaPD : Arena (ContPD * ContPD) MkCUnit (ContPD * ContPD)
ArenaPD = cornerPD *** cornerPD

payoffPD : (MovesPD, MovesPD) -> (Int, Int)
payoffPD (C, C) = (3, 3)
payoffPD (C, D) = (0, 5)
payoffPD (D, C) = (5, 0)
payoffPD (D, D) = (1, 1)

PlayerPD : Player (MovesPD, MovesPD) (MovesPD, MovesPD) (const (Int, Int))
PlayerPD = argmaxPlayer

contextPD : Context (MkCUnit * MkCUnit) (MkCont (MovesPD, MovesPD) (const (Int, Int)))
contextPD = MkContext (scalarToState ()) (funToCostate payoffPD)


gamePD : Game (MovesPD, MovesPD) ? ? ?
gamePD = MkGame ?pla ArenaPD