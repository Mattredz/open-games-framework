module Games.CoState

import Container.Definition  -- definizione di Container
import Lens.Definition       -- definizione di ParaLens e DepLens


public export
CoState : (xs : Container) -> Type
CoState xs = NonParaLens xs CUnit

public export
funToCostate : {xs : Container} -> ((x : shape xs) -> position xs x) -> CoState xs
funToCostate f = MkNonParaLens (const ()) (\x => const (f x))

public export
costateToFun : {xs : Container} -> CoState xs -> ((x : shape xs) -> position xs x)
costateToFun (MkPLens _ bwd) key = fst (bwd () key ())