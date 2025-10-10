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
packup :  Arena (MkCo p q) (MkParaCont (\p => x) (\x => s)) (MkCo y r) 
          -> Context (MkCo x s) (MkCo y r) 
          -> ParaDepLens (MkCo p q) (MkParaCont (const Unit) (\_ => const Unit)) (MkCo Unit (\_ => Unit))
packup arena (MkContext st ct) =  let game = st >>> arena >>> ct in pararunitor (paralunitor game)

paraRdiff : 
  ParaDepLens (MkCo p q) (MkParaCont (\p => x) (\x => s)) (MkCo y r) 
  -> ParaDepLens (MkCo p (\p0 => (p1 : p) -> q p1)) (MkParaCont (\p => x) (\p => \x0 => (x1 : x) -> s x1)) (MkCo y (\y0 => (y1 : y) -> r y1))
paraRdiff (MkPLens play coplay) =
  MkPLens
    play
    (\p, x, payoff => let f = \x' => fst $ coplay p  x' (payoff (play p x'))
                          g = \p' => snd $ coplay p' x (payoff (play p' x))
                      in (f, g))
        

reparam : (l : DLens pq' pq) -> ParaDepLens pq xs yr -> ParaDepLens pq' (MkParaCont (\p => xs.shape (l.play () p)) (\p => xs.position (l.play () p))) yr
reparam (MkPLens play1 coplay1) (MkPLens play2 coplay2) =
  MkPLens
    (\p, x => play2 (play1 () p) x)
    (\p, x, ry => let (s, q) = coplay2 (play1 () p) x ry in (s, fst (coplay1 () p q)))

public export
equilibrium
  :  (Listable profiles)
  => Game profiles p q (MkParaCont (\p => x) (\p => s)) (MkCo y r)
  -> Context (MkCo x s) (MkCo y r)
  -> List profiles
equilibrium (MkGame player arena) ctx =
  let diff = pararunitor $ paralunitor $ lunitor >>> paraRdiff (packup arena ctx) >>> runitor 
      rep : ParaDepLens (MkCo profiles (\p => profiles -> Bool))
                  (MkParaCont (const ()) (\_ => const ()))
                  (MkCo () (const ()))
      rep = reparam player diff
  in fixpoints (paraStateToFun (rep))
