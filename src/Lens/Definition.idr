module Lens.Definition

import Container.Definition
import Container.Morphism
import Container.Product
%hide Prelude.Ops.infixl.(*)

public export
record ParaLens (pq, xs, yr : Container) where
    constructor MkParaLens
    fwd : shape pq -> shape xs -> shape yr
    bwd : (p : shape pq) -> (x : shape xs) -> position yr (fwd p x) ->  (position xs x, position pq p)

public export
DepLens : (xs, yr : Container) -> Type
DepLens = ParaLens MkCUnit 

public export
MkDepLens : CMorph xs yr -> DepLens xs yr
MkDepLens (play !> coplay) = MkParaLens
    (const (\x => play x))
    (const (\x, t => (coplay x t, ())))


public export
NormilizeLens : ParaLens pq xs yr -> ParaLens pq' xs' yr'
NormilizeLens (MkParaLens fwd bwd) = ?para