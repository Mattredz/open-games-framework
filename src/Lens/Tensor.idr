module Lens.Tensor

import Lens.Definition
import Container.Definition
import Container.Product

infixr 5 ***

public export
(***) : ParaLens pq xs yr -> ParaLens pq' xs' yr' -> ParaLens (pq * pq') (xs * xs') (yr * yr')
(***) (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens
    (\(p, p'), (x, x') => (fwd p x, fwd' p' x'))
    (\(p, p'), (x, x'), (r, r') =>
        let (s, q) = bwd p x r in
        let (s', q') = bwd' p' x' r' in
        ((s, s'), (q, q'))
    )