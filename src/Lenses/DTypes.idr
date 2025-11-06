||| Core dependent types for categorical constructions
|||
||| This module defines fundamental dependent type constructions
||| used throughout the optics and game theory framework.
module Lenses.DTypes

%default total


||| The terminal dependent type, representing the unit type with trivial fibration
public export
DUnit : (X : Type ** X -> Type)
DUnit = (() ** const ())

||| Dependent product of two dependent types
|||
||| Constructs a dependent product by pairing the base types
||| and defining the fiber over pairs component-wise.
|||
||| @ xs The first dependent type
||| @ ys The second dependent type
public export
DProd : (xs : (X : Type ** X -> Type)) ->
        (ys : (Y : Type ** Y -> Type)) ->
        (XY : Type ** XY -> Type)
DProd xs ys =
    ((xs.fst, ys.fst) ** (\xy => (xs.snd (fst xy), ys.snd (snd xy))))

||| Dependent sum type over Either
|||
||| Applies a dependent type to each branch of an Either value.
|||
||| @ fa The fiber for Left values
||| @ fb The fiber for Right values
||| @ e The Either value
public export
SEither : (a -> Type) -> (b -> Type) -> Either a b -> Type
SEither fa fb e = case e of
    Left  x => fa x
    Right y => fb y

||| Dependent coproduct (Either) of two dependent types
|||
||| @ xs The first dependent type
||| @ ys The second dependent type
public export
DEither : (xs : (X : Type ** X -> Type)) ->
          (ys : (Y : Type ** Y -> Type)) ->
          (E : Type ** E -> Type)
DEither xs ys =
    (Either xs.fst ys.fst ** SEither xs.snd ys.snd)

||| Dependent sum for parameterized fibers over coproducts
|||
||| @ q The fiber family for the left component
||| @ q' The fiber family for the right component
public export
QEither : {X, Y : Type} ->
          {P : X -> Type} ->
          {P' : Y -> Type} ->
          (q : (x : X) -> P x -> Type) ->
          (q' : (y : Y) -> P' y -> Type) ->
          ((e : Either X Y) -> SEither P P' e -> Type)
QEither q q' = \case 
    Left  x => q x
    Right y => q' y