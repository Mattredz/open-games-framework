module Container.Morphism

import Container.Definition

infixr 5 =%>
infixr 5 !>

public export
record CMorph (xs, yr : Container) where
  constructor (!>)
  fwd : shape xs -> shape yr
  bwd : (x : shape xs) -> position yr (fwd x) -> position xs x

