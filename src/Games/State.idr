module Games.State

import Container.Definition
import Container.Morphism
import Lens.Definition

-- | A State is a DepLens from the unit container to a container over x
public export
State : Container -> Type
State yr = NonParaLens CUnit yr

public export
scalarToState : {xs : Container} -> shape xs -> State xs
scalarToState x = MkNonParaLens (const x) const

public export
stateToScalar : State yr -> shape yr
stateToScalar (MkPLens fwd _) = fwd () ()


public export
paraStateToFun : ParaLens pq CUnit CUnit -> ((s : shape pq) -> position pq s)
paraStateToFun (MkPLens _ bwd) p = snd $ bwd p () ()
