module Lens.Coproduct

import Container.Definition
import Container.Coproduct
import Lens.Definition
%default total

infixr 4 ++++

public export
(++++) :
  {q   : Type} ->
  {p,p' : Type} ->
  {xs, xs', yr, yr' : Container} ->
  ParaLens (CMk (p  ** const q)) xs  yr  ->
  ParaLens (CMk (p' ** const q)) xs' yr' ->
  ParaLens (CMk ((p, p') ** const q)) (SumCont xs xs') (SumCont yr yr')
(++++) (MkPLens fwd bwd) (MkPLens fwd' bwd') =
  MkPLens 
    (\(pVal, pVal'), xx => case xx of
        Left  x  => Left  (fwd  pVal  x)
        Right x' => Right (fwd' pVal' x'))
    (\(pVal, pVal'), xx, t => case xx of
      Left  x  => let (posXS , qpos) = bwd  pVal  x  t in (posXS , qpos)
      Right x' => let (posXS', qpos) = bwd' pVal' x' t in (posXS', qpos))
