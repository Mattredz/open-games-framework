module Lens.Composition

import Lens.Definition
import Container.Definition
import Container.Product
%hide Prelude.Ops.infixl.(*)

infixr 5 >>>

public export
(>>>) : {pq, pq' : Container} -> (ParaLens pq xs yr) -> ParaLens pq' yr zt -> ParaLens (pq * pq') xs zt
(>>>) {pq = MkCUnit} {pq' = MkCont _ _} (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens 
    (\p, x => fwd' p (fwd () x))
    (\p, x, t => 
        let (r, q') = bwd' p (fwd () x) t in
        let (s, _) = bwd () x r in
        (s, q')
    )
(>>>) {pq' = MkCUnit} {pq = MkCont _ _} (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens 
    (\p, x => fwd' () (fwd p x))
    (\p, x, t => 
        let (r, _) = bwd' () (fwd p x) t in
        let (s, q) = bwd p x r in
        (s, q)
    )
(>>>) {pq = MkCont _ _} {pq' = MkCont _ _} (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens 
    (\(p, p'), x => fwd' p' (fwd p x)) 
    (\(p, p'), x, t => 
        let (r, q') = bwd' p' (fwd p x) t in
        let (s, q) = bwd p x r in
        (s, (q, q'))
    )
(>>>) {pq = MkCUnit} {pq' = MkCUnit} (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens 
    (const (\x => fwd' () (fwd () x)))
    (const (\x, t => 
        let (r, _) = bwd' () (fwd () x) t in
        let (s, _) = bwd () x r in
        (s, ())
    ))
