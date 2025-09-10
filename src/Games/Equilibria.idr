module Games.Equilibria

import Interfaces.Listable
import Container.Definition
import Container.Product
import Container.RDiff
import Lens.Definition
import Lens.Composition
import Games.Definition
import Players.Definition
import Games.Arena
import Games.Context
import Games.State
import Games.CoState

public export
paraRdiff
  :  {pq, xs, yr : Container}
  -> ParaLens pq xs yr
  -> ParaLens (rDiff pq) (rDiff xs) (rDiff yr)
paraRdiff (MkPLens play coplay) =
  MkPLens play
    (\p, x, payoff => 
      ( \x' => fst $ coplay p x' (payoff (play p x'))
      , \p' => snd $ coplay p' x (payoff (play p' x))
      ))

norm : ParaLens pq (rDiff CUnit) (rDiff CUnit) -> ParaLens pq CUnit CUnit
norm (MkPLens play coplay) =
  MkPLens 
    (\p, _ => play p ())
    (\p, _, _ => let (_, q) = coplay p () (const ()) in ((), q))

public export %inline
packup : {pq, xs, yr : Container}
        -> Arena pq xs yr
        -> Context xs yr
        -> ParaLens (rDiff pq) CUnit CUnit
packup arena (MkContext state coState) =
  let comp = replace {p = (\d => ParaLens d CUnit CUnit)} (rightUnitProd pq) 
             (state >>>> arena >>>> coState)
  in  norm $ paraRdiff comp

public export
reparam : NonParaLens pq' pq -> ParaLens pq xs yr -> ParaLens pq' xs yr
reparam (MkPLens playP coplayP) (MkPLens play coplay) =
  MkPLens
    (\p', x => play (playP () p') x)
    (\p', x, r =>
        let (s, q)  = coplay (playP () p') x r
            (q', _) = coplayP () p' q
        in (s, q'))

public export
equilibrium
  :  (Listable profiles)
  => {pq, xs, yr : Container}
  -> Game profiles pq xs yr
  -> Context xs yr
  -> List profiles
equilibrium (MkGame player arena) ctx =
  fixpoints (paraStateToFun (reparam player (packup arena ctx)))
