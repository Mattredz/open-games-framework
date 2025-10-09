module Games.CoState

import Optics.Lens   


public export
CoState : (xs : Cont) -> Type
CoState xs = DLens xs (MkCo () (\_ => ()))

public export
funToCostate : {x : Type} -> {s : x -> Type} -> ((x' : x) -> s x') -> CoState (MkCo x s)
funToCostate f = MkDLens (const ()) (\x => const (f x))

public export
costateToFun : {x : Type} -> {s : x -> Type} -> CoState (MkCo x s) -> ((x' : x) -> s x')
costateToFun (MkPLens _ bwd) x0 = fst (bwd ((), x0) ())