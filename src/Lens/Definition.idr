module Lens.Definition

import Container.Definition
import Container.Product

%default total

public export 
record ParaLens (PQ : Container) (XS : Container) (YR : Container) where
  constructor MkPLens
  fwd : shape PQ -> shape XS -> shape YR
  bwd : (p : shape PQ) -> (x : shape XS)
      -> position YR (fwd p x)
      -> ( position XS x , position PQ p )

public export
NonParaLens : (XS : Container) -> (YR : Container) -> Type
NonParaLens = ParaLens CUnit

public export
MkNonParaLens
  : {xs, yr : Container}
  -> (f : shape xs -> shape yr)
  -> (g : (x : shape xs) -> position yr (f x) -> position xs x)
  -> NonParaLens xs yr
MkNonParaLens f g =
  MkPLens
    (\_, x => f x)
    (\_, x, pos => (g x pos, ()))
