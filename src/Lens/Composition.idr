module Lens.Composition

import Lens.Para
import Lens.Definition
import Container.Definition
import Container.Product

infixr 5 >>>

public export
(>>>) : (ParaLens pq xs yr) -> ParaLens pq' yr zt -> ParaLens (pq * pq') xs zt
(>>>) (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens 
    (\(p, p'), x => fwd' p' (fwd p x)) 
    (\(p, p'), x, t => 
        let (r, q') = bwd' p' (fwd p x) t in
        let (s, q) = bwd p x r in
        (s, (q, q'))
    )

