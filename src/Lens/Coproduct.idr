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
  MkPLens fwdSum bwdSum
  where
    -- FORWARD: instrada per ramo
    fwdSum : (pp : (p, p')) -> shape (SumCont xs xs') -> shape (SumCont yr yr')
    fwdSum (pVal, pVal') xx = case xx of
        Left  x  => Left  (fwd  pVal  x)
        Right x' => Right (fwd' pVal' x')

    -- BACKWARD: chiama il bwd del ramo selezionato
    -- Nota: position sul parametro risultante è 'q' (costante), quindi
    --       possiamo ritornare direttamente la 'q' dal ramo corrispondente.
    bwdSum
      : (pp : (p, p'))
     -> (xx : shape (SumCont xs xs'))
     -> position (SumCont yr yr') (fwdSum pp xx)
     -> ( position (SumCont xs xs') xx
        , position (CMk ((p,p') ** const q)) pp )  -- ≡ q
    bwdSum (pVal, pVal') xx t = case xx of
      Left  x  =>
        let (posXS , qpos) = bwd  pVal  x  t in (posXS , qpos)
      Right x' =>
        let (posXS', qpos) = bwd' pVal' x' t in (posXS', qpos)
