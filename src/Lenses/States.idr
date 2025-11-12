||| States and costates for dependent lenses
|||
||| This module provides abstractions for viewing dependent lenses
||| as stateful computations or observations.
module Lenses.States

import public Lenses.DTypes
import public Lenses.ParaDLens

%default total

||| State: a lens from unit to a dependent type
|||
||| Represents a value in a context without external input.
|||
||| @ xs The state space with its fibration
public export
State : (xs : (X : Type ** X -> Type)) -> Type
State xs = DLens DUnit xs

||| Lift a scalar value to a state
|||
||| Creates a constant state that always returns the given value.
|||
||| @ x0 The constant value to lift
public export
scalarToState : {x : Type} -> {s : x -> Type} -> x -> State (x ** s)
scalarToState x0 = MkDLens (const x0) (\_, _ => ())

||| CoState: a lens from a dependent type to unit
|||
||| Represents an observation or measurement of a dependent type.
|||
||| @ yr The observed type with its fibration
public export
CoState : (yr : (Y : Type ** Y -> Type)) -> Type
CoState yr = DLens yr DUnit

||| Convert a function to a costate
|||
||| Lifts a dependent function to a costate observation.
|||
||| @ f The function to lift
public export
FunToCoState : {x : Type} -> {s : x -> Type} -> 
               ((x' : x) -> s x') -> CoState (x ** s)
FunToCoState f = MkDLens (const ()) (\x, _ => f x)

||| Extract function from costate
|||
||| Recovers the underlying function from a costate.
public export
CoStateToFun : CoState (y ** r) -> ((a : y) -> r a)
CoStateToFun (MkParaLens _ bwd) y0 = fst (bwd () y0 ())

||| Extract parameterized function from parameterized state
|||
||| Recovers the parameterized function encoded in a parameterized lens.
public export
ParaStateToFun : ParaDLens pq DUnit DUnit -> ((p : pq.fst) -> pq.snd p)
ParaStateToFun (MkParaLens _ bwd) p0 = snd (bwd p0 () ())
