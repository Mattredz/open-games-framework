||| The Ultimatum Game
|||
||| A sequential bargaining game where one player proposes a division
||| and the other accepts or rejects.
module GameTheory.Examples.UltimatumGame

import Interfaces.Listable
import GameTheory.Core
import GameTheory.Combinators
import GameTheory.Examples.Players
import Lenses.States
import Lenses.Utils
import Lenses.Operators

%default total

||| Offer types in the Ultimatum Game
public export
data Offer = Fair | Unfair

export
implementation Listable Offer where
    allValues = [Fair, Unfair]

||| Response types in the Ultimatum Game
public export
data Response = Accept | Reject

export
implementation Listable Response where
    allValues = [Accept, Reject]

||| Payoff function for the Ultimatum Game
|||
||| - Fair offer accepted: (5, 5)
||| - Unfair offer accepted: (8, 2)
||| - Any offer rejected: (0, 0)
public export
UGPayoff : (Offer, Response) -> (Int, Int)
UGPayoff (Fair, Accept)   = (5, 5)
UGPayoff (Unfair, Accept) = (8, 2)
UGPayoff (_, Reject)      = (0, 0)

||| Arena for the offering stage
|||
||| The first player chooses an offer which becomes visible to both players.
public export
OfferArena : Arena (Offer ** const Int) DUnit (Offer ** const Int)
OfferArena = corner

||| The offering player's decision rule
public export
Offerer : Player Offer Offer (const Int)
Offerer = Argmax

||| Arena for the response stage
|||
||| The second player observes the offer and decides to accept or reject.
public export
ResponseArena : Arena ((Offer -> Response) ** const Int) 
                      (Offer ** const Int) 
                      ((Offer, Response) ** const (Int, Int))
ResponseArena = MkParaLens
    (\p, o => (o, p o))
    (\_, _, ry => ry)

||| Response strategy profiles
public export
data RespProfiles = AlwaysAccept | AlwaysReject | RejectUnfair 

export
implementation Listable RespProfiles where
    allValues = [AlwaysAccept, AlwaysReject, RejectUnfair]

||| The responding player's decision rule
public export
Responder : Player RespProfiles (Offer -> Response) (const Int)
Responder = FArgmax profileToFun 
    where
    profileToFun : RespProfiles -> (Offer -> Response)
    profileToFun AlwaysAccept = const Accept
    profileToFun AlwaysReject = const Reject
    profileToFun RejectUnfair = \case
        Fair   => Accept
        Unfair => Reject

||| Subgame perfect Nash equilibrium of the Ultimatum Game
|||
||| Computes the equilibrium of the sequential game.
||| Standard prediction: Offerer proposes Unfair, Responder accepts everything.
public export
UltE : List (Offer, RespProfiles)
UltE = Equilibrium (MkGame (OfferArena >>> ResponseArena) 
                   (scalarToState ()) 
                   (FunToCoState UGPayoff))
                   (Offerer $$ Responder)
