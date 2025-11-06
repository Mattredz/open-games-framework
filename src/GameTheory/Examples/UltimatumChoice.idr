module GameTheory.Examples.UltimatumChoice

import Interfaces.Listable
import GameTheory.Examples.UltimatumGame
import GameTheory.Examples.Players
import GameTheory.Core
import GameTheory.Combinators
import Lenses.States
import Lenses.Utils
import Lenses.Operators

%default total

||| Choice of offer type in the Ultimatum Game
COffer : Type
COffer = Either () ()

||| Arena for the choice of offer
ChoiceOffer : Arena COffer Int DUnit (COffer ** SEither (const Int) (const Int))
ChoiceOffer = MkParaLens 
    (const)
    (\o, _, ry => case o of
                     Left _   => ((), ry)
                     Right _  => ((), ry))

||| Arena for the responder
ChoiceResponder : Arena Response Int (() ** const Int) (Response ** const (Int, Int))
ChoiceResponder = MkParaLens
    (const)
    (\_, _ => id)

||| Payoff functions for fair and unfair offers
FairPayoff : Response -> (Int, Int)
FairPayoff Accept = (5, 5)
FairPayoff Reject = (0, 0)

UnfairPayoff : Response -> (Int, Int)
UnfairPayoff Accept = (8, 2)
UnfairPayoff Reject = (0, 0)

||| The choosing player's decision rule
ChP : Player Offer COffer Int
ChP = MkDLens convert (\o, k => argmax (k . convert))
  where
    convert : Offer -> COffer
    convert Fair  = Left ()
    convert Unfair = Right ()

||| Mixed strategy Nash equilibrium of the Ultimatum Choice Game
ChoiceE : List (Offer, (Response, Response))
ChoiceE = Equilibrium (ChoiceOffer >>> ChoiceResponder +++ ChoiceResponder) 
                      (ChP $$ Argmax)
                      (scalarToState (())) 
                      (DCoProd (FunToCoState FairPayoff) (FunToCoState UnfairPayoff) <<| CoUnitor)
