module CoState.Definition

import Container.Definition  -- definizione di Container
import Container.Morphism   -- definizione di Morphism
import Lens.Definition       -- definizione di ParaLens e DepLens


public export
CoState : (xs : Container) -> Type
CoState xs = DepLens xs MkCUnit

public export
funToCostate : {xs : Container} -> ((x : shape xs) -> position xs x) -> CoState xs
funToCostate f = MkDepLens (const () !> (\x => const (f x)))

public export
costateToFun : {xs : Container} -> CoState xs -> ((x : shape xs) -> position xs x)
costateToFun (MkParaLens _ bwd) key = fst (bwd () key ())