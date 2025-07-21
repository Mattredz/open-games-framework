module State.Definition

import Container.Definition
import Container.Morphism
import Lens.Definition

-- | A State is a DepLens from the unit container to a container over x
public export
State : Container -> Type
State yr = DepLens MkCUnit yr

public export
scalarToState : shape xs -> State xs
scalarToState x = MkDepLens (const x !> const)

public export
stateToScalar : State yr -> shape yr
stateToScalar (MkParaLens fwd _) = fwd () ()


public export
paraStateToFun : ParaLens pq MkCUnit MkCUnit -> (s : shape pq) -> position pq s
paraStateToFun (MkParaLens _ bwd) p = snd $ bwd p () ()
