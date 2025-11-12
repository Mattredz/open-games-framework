||| Parameterized dependent lenses
|||
||| This module defines the central concept of parameterized dependent lenses,
||| which generalize traditional lenses to the dependent type setting with
||| internal fibration structure.
module Lenses.ParaDLens

import public Lenses.DTypes

%default total

||| Parameterized dependent lens with internal fibration
|||
||| A ParaDLens represents a bidirectional transformation between dependent types
||| with an internal parameter space. The fibration is encoded inside the dependent pair.
|||
||| @ pq The parameter space with its fibration
||| @ xs The source dependent type
||| @ yr The target dependent type
public export
record ParaDLens (pq : (P : Type ** P -> Type))
                 (xs : (X : Type ** X -> Type)) 
                 (yr : (Y : Type ** Y -> Type)) where
    constructor MkParaLens
    ||| Forward direction: transforms source to target given a parameter
    play : pq.fst -> xs.fst -> yr.fst
    ||| Backward direction: updates source and parameter given target observation
    coplay : (p1 : pq.fst) -> (x : xs.fst) -> 
             yr.snd (play p1 x) -> (xs.snd x, pq.snd p1)

||| Non-parameterized dependent lens
|||
||| A DLens is a ParaDLens with trivial parameter space.
|||
||| @ xs The source dependent type
||| @ yr The target dependent type
public export
DLens : (xs : (X : Type ** X -> Type)) ->
        (yr : (Y : Type ** Y -> Type)) ->
        Type
DLens xs yr = ParaDLens DUnit xs yr

||| Smart constructor for non-parameterized dependent lenses
|||
||| Constructs a DLens from forward and backward functions.
|||
||| @ play The forward transformation
||| @ coplay The backward transformation
public export
MkDLens : (play : xs.fst -> yr.fst) ->
          (coplay : (x : xs.fst) -> yr.snd (play x) -> xs.snd x) ->
          DLens xs yr
MkDLens play coplay =
    MkParaLens
    (const play)
    (\_, x, ry => (coplay x ry, ()))
