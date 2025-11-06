||| The Inspection Game
|||
||| A simultaneous game where an inspector decides whether to inspect
||| and an inspectee decides whether to comply or violate.
module GameTheory.Examples.InspectionGame

import Interfaces.Listable
import GameTheory.Core
import GameTheory.Combinators
import GameTheory.Examples.Players
import Lenses.States
import Lenses.Utils
import Lenses.Operators
import Lenses.DTypes

%default total

||| Inspector's move: inspect or not
public export
Inspect : Type
Inspect = ()

public export
NoInspect : Type
NoInspect = ()

public export
InspectorMove : Type
InspectorMove = Either Inspect NoInspect

||| Inspectee's move: comply or violate
public export
data InspecteeMove = Comply | Violate

export
implementation Listable InspecteeMove where
    allValues = [Comply, Violate]

||| Inspector's choice arena
|||
||| The inspector chooses whether to inspect, creating two branches.
public export
InspectorArena : Arena InspectorMove Int 
                       DUnit 
                       (InspectorMove ** SEither (const Int) (const Int))
InspectorArena = MkParaLens
    (const)
    (\o, _, ry => case o of
                     Left _   => ((), ry)
                     Right _  => ((), ry))

||| Arena when inspection occurs
|||
||| The inspectee chooses to comply or violate under inspection.
public export
InspectionArena : Arena InspecteeMove Int 
                        (Inspect ** const Int) 
                        (InspecteeMove ** const (Int, Int))
InspectionArena = MkParaLens
    const
    (\_, _, ry => ry)

||| Arena when no inspection occurs
|||
||| The inspectee chooses to comply or violate without inspection.
public export
NoInspectionArena : Arena InspecteeMove Int
                          (NoInspect ** const Int) 
                          (InspecteeMove ** const (Int, Int))
NoInspectionArena = MkParaLens
    const
    (\_, _, ry => ry)

||| Payoff when inspection occurs
|||
||| - Comply: (2, 2)
||| - Violate: (0, -5) - violator caught and punished
public export
InspectionPayoff : InspecteeMove -> (Int, Int)
InspectionPayoff Comply  = (2, 2)
InspectionPayoff Violate = (0, -5)

||| Payoff when no inspection occurs
|||
||| - Comply: (5, 1)
||| - Violate: (-1, 5) - violator benefits, inspector loses
public export
NoInspectionPayoff : InspecteeMove -> (Int, Int)
NoInspectionPayoff Comply  = (5, 1)
NoInspectionPayoff Violate = (-1, 5)


||| Mixed strategy Nash equilibrium of the Inspection Game
|||
||| Computes equilibria where both players randomize their strategies.
||| This game typically has no pure strategy Nash equilibrium but has
||| a unique mixed strategy equilibrium.
public export
InspectionE : List (InspectorMove, (InspecteeMove, InspecteeMove))
InspectionE = Equilibrium (InspectorArena >>> InspectionArena +++ NoInspectionArena) 
                          (Argmax $$ Argmax) 
                          (scalarToState ()) 
                          (DCoProd (FunToCoState InspectionPayoff) 
                                   (FunToCoState NoInspectionPayoff) <<| CoUnitor)
