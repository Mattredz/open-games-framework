module Players.Definition

import Optics.Lens

public export
Player : (profiles, actions, utility : Type)   -> Type
Player profiles actions utility = DLens (MkCo profiles (\p => profiles -> Bool)) (MkCo actions (\a => actions -> utility))

public export
nash : Player p1 a1 u1 -> Player p2 a2 u2 
     -> Player (p1, p2) (a1, a2) (u1, u2)
nash (MkPLens play1 coplay1) (MkPLens play2 coplay2) =
  MkDLens
    (\(p1, p2) => (play1 ((), p1), play2 ((), p2)))
    (\(p1, p2), payoff => let f = fst $ coplay1 ((), p1) (\x => fst (payoff (x, play2 ((), p2))))
                              g = fst $ coplay2 ((), p2) (\y => snd (payoff (play1 ((), p1), y)))
                         in (\(a1, a2) => f a1 && g a2))

