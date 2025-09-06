module Container.Definition

public export
data Container : Type where
  CUnit : Container
  CMk   : (S : Type ** S -> Type) -> Container

public export %inline
shape : Container -> Type
shape CUnit            = Unit
shape (CMk (s ** _))   = s

public export %inline
position : (c : Container) -> shape c -> Type
position CUnit          = const Unit
position (CMk (_ ** p)) = p


