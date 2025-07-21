module Lens.Tensor

import Lens.Definition
import Container.Definition
import Container.Product
%hide Prelude.Ops.infixl.(*)

infixr 5 ***

public export
(***) : {pq, pq', xs, xs', yr, yr' : Container } -> ParaLens pq xs yr -> ParaLens pq' xs' yr' -> ParaLens (pq * pq') (xs * xs') (yr * yr')
(***) {pq = MkCUnit} {pq' = MkCont _ _}
      {xs = MkCont _ _} {xs' = MkCont _ _}
      {yr = MkCont _ _} {yr' = MkCont _ _}
    (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens
    (\p, (x, x') => (fwd () x, fwd' p x'))
    (\p, (x, x'), (r, r') =>
        let (s, _) = bwd () x r in
        let (s', q') = bwd' p x' r' in
        ((s, s'), q')
    )
(***) {pq = MkCont _ _} {pq' = MkCUnit}
      {xs = MkCont _ _} {xs' = MkCont _ _}
      {yr = MkCont _ _} {yr' = MkCont _ _}
    (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens
    (\p, (x, x') => (fwd p x, fwd' () x'))
    (\p, (x, x'), (r, r') =>
        let (s, q) = bwd p x r in
        let (s', _) = bwd' () x' r' in
        ((s, s'), q)
    )
(***) {pq = MkCont _ _} {pq' = MkCont _ _}
      {xs = MkCont _ _} {xs' = MkCont _ _}
      {yr = MkCont _ _} {yr' = MkCont _ _}
    (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens
    (\(p, p'), (x, x') => (fwd p x, fwd' p' x'))
    (\(p, p'), (x, x'), (r, r') =>
        let (s, q) = bwd p x r in
        let (s', q') = bwd' p' x' r' in
        ((s, s'), (q, q'))
    )

(***) _ _ = ?notCovered