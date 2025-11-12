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
ChoiceOffer : Arena (COffer ** const Int) DUnit (COffer ** SEither (const Int) (const Int))
ChoiceOffer = MkParaLens 
    (const)
    (\case 
        Left x   => \_, payoff => ((), payoff)
        Right x'  => \_, payoff => ((), payoff))

||| Arena for the responder
ChoiceResponder : Arena (Response ** const Int) (() ** const Int) (Response ** const (Int, Int))
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
ChP : Player Offer COffer (const Int)
ChP = FArgmax convert
  where
    convert : Offer -> COffer
    convert Fair  = Left ()
    convert Unfair = Right ()


RhP : Player RespProfiles (Response, Response) (\x => Either (const Int x) (const Int x))
RhP = FArgmax convert
  where
    convert : RespProfiles -> (Response, Response)
    convert AlwaysAccept = (Accept, Accept)
    convert AlwaysReject = (Reject, Reject)
    convert RejectUnfair = (Accept, Reject)

||| Mixed strategy Nash equilibrium of the Ultimatum Choice Game
ChoiceE : List (Offer, RespProfiles)
ChoiceE = Equilibrium (MkGame (ChoiceOffer >>> ChoiceResponder ++++ ChoiceResponder) 
                      (scalarToState ()) 
                      (DCoProd (FunToCoState FairPayoff) (FunToCoState UnfairPayoff) <<| CoUnitor))
                      (ChP $$ RhP)
