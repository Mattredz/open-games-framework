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
import Context
import State.Definition
import CoState.Definition



public export
paraRdiff
  :  {pq, xs, yr : Container}
  -> ParaLens pq xs yr
  -> ParaLens (rDiff pq) (rDiff xs) (rDiff yr)
paraRdiff (MkPLens play coplay) =
  MkPLens
    play
    (\p, x, payoff => let
        s = \x' => fst $ coplay p x' (payoff (play p x'))
        g = \p' => snd $ coplay p' x (payoff (play p' x))
        in (s, g))


norm : ParaLens pq (rDiff CUnit) (rDiff CUnit)
       -> ParaLens pq CUnit CUnit
norm (MkPLens play coplay) =
  MkPLens
    (\p, _ => play p ())
    (\p, _, _ => let (_, q) = coplay p () (const ()) in ((), q))

-- packup: normalizzo via rightUnitProd PRIMA di applicare paraRdiff
public export %inline
packup : {pq, xs, yr : Container}
        -> Arena pq xs yr
        -> Context xs yr
        -> ParaLens (rDiff pq) CUnit CUnit
packup arena (MkContext state coState) =
  let comp = replace {p = (\d => ParaLens d CUnit CUnit)} (rightUnitProd pq) 
             (state >>>> arena >>>> coState)
  in  norm $ paraRdiff comp

-- Reparametrization (operatore *** in Optics.hs)
public export
reparam : NonParaLens pq' pq -> ParaLens pq xs yr -> ParaLens pq' xs yr
reparam (MkPLens playP coplayP) (MkPLens play coplay) =
  MkPLens
    (\p', x => play (playP () p') x)
    (\p', x, r =>
        let (s, q)  = coplay (playP () p') x r
            (q', _) = coplayP () p' q
        in (s, q')
    )


-- Equilibria: chiude il gioco nel contesto e cerca i punti fissi del best response
-- Se la tua 'fixpoints' richiede uguaglianza decidibile, aggiungi anche 'DecEq profiles'.
public export
equilibrium
  :  (Listable profiles)
  => 
  {pq, xs, yr : Container} ->
  Game profiles pq xs yr
  -> Context xs yr
  -> List profiles
equilibrium (MkGame player arena) ctx =
  let packed = packup arena ctx                         -- ParaLens (rDiff pq) () ()
      game   = reparam player packed                   -- ParaLens pq () ()
  in  fixpoints (paraStateToFun game)                   -- profiles -> profiles
