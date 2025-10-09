module Games.State

import Optics.Lens

-- | A State is a DepLens from the unit container to a container over x
public export
State : (yr : Cont) -> Type
State yr = DLens (MkCo () (\_ => ())) yr

public export
scalarToState : {y : Type} -> {r : y -> Type} -> y -> State (MkCo y r)
scalarToState x = MkDLens (const x) (\_ => const ())

public export
paraStateToFun : ParaDepLens (MkCo p q) (MkCo () (const ())) (MkCo () (const ())) -> ((s : p) -> q s)
paraStateToFun (MkPLens _ bwd) p0 = snd (bwd (p0, ()) ())

