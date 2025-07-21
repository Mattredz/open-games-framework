module Games.Equilibria

import Interfaces.Listable
import Container.Definition
import Container.Product
import Lens.Definition
import Lens.Composition
import Games.Definition
import Players.Definition
import Arena
import Context
import State.Definition
import CoState.Definition


rDiff : Container -> Container
rDiff MkCUnit = MkCUnit
rDiff (MkCont shp pos) = MkCont shp (\s' => (s : shp) -> pos s)

paraRdiff : {pq, xs, yr : Container} -> ParaLens pq xs yr -> ParaLens (rDiff pq) (rDiff xs) (rDiff yr)
paraRdiff {pq = MkCont _ _} {xs = MkCont _ _} {yr = MkCont _ _} (MkParaLens play coplay) = MkParaLens
  play
  (\p, x, payoff =>
    let
      f = \x' => fst $ coplay p x' (payoff (play p x'))
      g = \p' => snd $ coplay p' x (payoff (play p' x))
    in (f, g)
  )
paraRdiff {pq = MkCUnit} {xs = MkCUnit} {yr = MkCUnit} (MkParaLens play coplay) = MkParaLens play coplay
paraRdiff {pq = MkCont _ _} {xs = MkCont _ _} {yr = MkCUnit} (MkParaLens play coplay) = MkParaLens
  play
  (\p, x, payoff =>
    let
      f = \x' => fst $ coplay p x' ()
      g = \p' => snd $ coplay p' x ()
    in (f, g)
  )
paraRdiff {pq = MkCont _ _} {xs = MkCUnit} {yr = MkCUnit} (MkParaLens play coplay) = MkParaLens
  play
  (\p, x, payoff =>
    let
      g = \p' => snd $ coplay p' x ()
    in ((), g)
  )
paraRdiff _ = ?boh

packup : Arena pq xs yr -> Context xs yr -> ParaLens pq MkCUnit MkCUnit
packup arena (MkContext state coState) = paraRdiff (state >>> arena >>> coState)

reparam : DepLens pq' pq -> ParaLens pq xs yr -> ParaLens pq' xs yr
reparam (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens
  (fwd' . fwd ())
  (\p, x, r => 
    let (s, q) = bwd' (fwd () p) x r
        (q', _) = bwd () p q
    in (s, q')
  )

public export
equilibrium : (Listable profiles) => Game profiles pq xs yr -> Context xs yr -> List profiles
equilibrium (MkGame player arena) context =
  let 
    packed = packup arena context
    game = reparam player (?transform)
  in fixpoints (?ad paraStateToFun game)
  
