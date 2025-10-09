module Games.Equilibria

import Interfaces.Listable
import Optics.Lens
import Games.Definition
import Games.Arena
import Games.CoState
import Games.State
import Games.Context
import Players.Definition

public export
packup : {p : Type} -> {q : p -> Type} -> Arena (MkCo p q) xs yr -> Context xs yr -> ParaDepLens (MkCo p q) (MkCo Unit (\_ => Unit)) (MkCo Unit (\_ => Unit))
packup arena (MkContext st ct) =  let game = st >>> arena >>> ct in pararunitor (paralunitor game)

paraRdiff : {p : Type} -> {q : p -> Type} ->
            {x : Type} -> {s : x -> Type} ->
ParaDepLens (MkCo p q) (MkCo x s) (MkCo y r) -> ParaDepLens (MkCo p (\p0 => (p1 : p) -> q p1)) (MkCo x (\x0 => (x1 : x) -> s x1)) (MkCo y (\y0 => (y1 : y) -> r y1))
paraRdiff (MkPLens play coplay) =
  MkPLens
    play
    (\(p, x), payoff => let f = \x' => fst $ coplay (p, x') (payoff (play (p, x')))
                            g = \p' => snd $ coplay (p', x) (payoff (play (p', x)))
                        in (f, g))
        

reparam : DLens pq' pq -> ParaDepLens pq xs yr -> ParaDepLens pq' xs yr
reparam (MkPLens play1 coplay1) (MkPLens play2 coplay2) =
  MkPLens
    (\(p, x) => play2 (play1 ((), p), x))
    (\(p, x), ry => let (s, q) = coplay2 ((play1 ((), p)), x) ry in (s, fst (coplay1 ((), p) q)))

public export
equilibrium
  :  (Listable profiles)
  => {p : Type} -> {q : Type} 
  -> Game profiles p q x s y r
  -> Context (MkCo x s) (MkCo y r)
  -> List profiles
equilibrium (MkGame player arena) ctx =
  let diff = pararunitor $ paralunitor $ lunitor >>> paraRdiff (packup arena ctx) >>> runitor 
      rep = reparam player diff
  in fixpoints (paraStateToFun (rep))
