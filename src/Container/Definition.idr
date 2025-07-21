module Container.Definition

public export
data Container : Type where
  MkCUnit : Container
  MkCont : (s : Type) -> (pos : s -> Type) -> Container

public export
shape : Container -> Type
shape MkCUnit         = Unit
shape (MkCont s _)   = s

public export
position : (c : Container) -> shape c -> Type
position MkCUnit       = const Unit
position (MkCont _ p) = p




