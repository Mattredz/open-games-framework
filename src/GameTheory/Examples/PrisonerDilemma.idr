||| The Prisoner's Dilemma game
|||
||| Classic game theory example demonstrating Nash equilibrium
||| in a simultaneous two-player game with conflicting incentives.
module GameTheory.Examples.PrisonerDilemma

import Interfaces.Listable
import GameTheory.Core
import GameTheory.Combinators
import GameTheory.Examples.Players
import Lenses.States
import Lenses.Utils

%default total



||| Actions in the Prisoner's Dilemma
|||
||| @ C Cooperate with the other player
||| @ D Defect (betray) the other player
public export
data PDAction = C | D

export
implementation Listable PDAction where
    allValues = [C, D]

||| Payoff function for the Prisoner's Dilemma
|||
||| Standard payoff matrix:
||| - Both cooperate: (3, 3)
||| - Cooperate vs Defect: (0, 5)
||| - Defect vs Cooperate: (5, 0)
||| - Both defect: (1, 1)
public export
PDPayoff : (PDAction, PDAction) -> (Int, Int)
PDPayoff (C, C) = (3, 3)
PDPayoff (C, D) = (0, 5)
PDPayoff (D, C) = (5, 0)
PDPayoff (D, D) = (1, 1)

||| Nash equilibrium of the Prisoner's Dilemma
|||
||| Computes the Nash equilibrium strategy profile.
||| The unique Nash equilibrium is (D, D) - both players defect.
public export
PDNashE : List (PDAction, PDAction)
PDNashE = Equilibrium corner 
                      (Argmax $$ Argmax) 
                      (scalarToState ()) 
                      (FunToCoState PDPayoff)

||| Sum utility transformation
|||
||| Transforms a pair of utilities to their sum, used for computing
||| Pareto optimal outcomes.
public export
Sum : DLens (x ** const Int) (x ** const (Int, Int))
Sum = MkDLens id (\_, (u1, u2) => u1 + u2)

||| Hicksian equilibrium of the Prisoner's Dilemma
|||
||| Computes equilibria under utilitarian social welfare maximization.
||| This finds the Pareto optimal outcome (C, C).
public export
PDHicksE : List (PDAction, PDAction)
PDHicksE = Equilibrium corner 
                       Argmax 
                       (scalarToState ()) 
                       (Sum |>> FunToCoState PDPayoff)
