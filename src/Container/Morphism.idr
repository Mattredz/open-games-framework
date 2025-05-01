module Container.Morphism

import Container.Definition


public export
record (=%>) (c1, c2 : Container) where
  constructor (!>)
  fwd : c1.shape -> c2.shape
  bwd : (x : c1.shape) -> c2.position (fwd x) -> c1.position x

