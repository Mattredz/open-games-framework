module Lens.Definition

import Container.Definition
import Container.Morphism

public export
record ParaLens (pq, xs, yr : Container) where
    constructor MkParaLens
    fwd : pq.shape -> xs.shape -> yr.shape
    bwd : (p : pq.shape) -> (x : xs.shape) -> yr.position (fwd p x) ->  (xs.position x, pq.position p)


public export
record DepLens (xs, yr : Container) where
    constructor (!>)