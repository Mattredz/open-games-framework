||| Combinators for constructing and manipulating games
|||
||| This module provides advanced combinators for building complex
||| game structures from simpler components.
module GameTheory.Combinators

import public Lenses.DTypes
import public Lenses.ParaDLens
import public Lenses.Operators

%default total

||| lift of a parameterized lens
|||
||| Constructs a lens that exposes the dependency structure
||| and removes the depency from the DPair.
public export
lift : ParaDLens pq xs yr ->
            ParaDLens (pq.fst ** const ((p : pq.fst) -> pq.snd p))
                      (xs.fst ** const ((x : xs.fst) -> xs.snd x)) 
                      (yr.fst ** const ((y : yr.fst) -> yr.snd y))
lift (MkParaLens play1 coplay1) =
  MkParaLens
    play1
    (\p, x, ry =>
      let s = \x => fst $ coplay1 p x (ry $ play1 p x)
          g = \p => snd $ coplay1 p x (ry $ play1 p x)
      in (s, g))

||| Reparameterization combinator
|||
||| Changes the parameter space of a parameterized lens by
||| composing with a lens that transforms parameters.
|||
||| @ l The original parameterized lens
||| @ param The parameter transformation lens
public export
reparam : ParaDLens au xs yr ->
          DLens pq au ->
          ParaDLens pq xs yr
reparam (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
  MkParaLens
    (\p, x => play1 (play2 () p) x)
    (\p, x, ry =>
        let (s, u)  = coplay1 (play2 () p) x ry
            (q, _) = coplay2 () p u
        in (s, q))

||| Corner lens: identity with internal fibration
|||
||| Creates a lens that exposes the parameter space as both
||| source and target, useful for embedding games in larger contexts.
public export
corner : ParaDLens pq DUnit pq
corner = MkParaLens
    (\p, _ => p)
    (\p, _, ry => ((), ry))

infixl 10 ***
||| Product of dependent lenses
|||
||| Combines two non-parameterized lenses into a product lens.
public export
(***) : DLens xs yr ->
            DLens xs' yr' ->
            DLens (DProd xs xs') (DProd yr yr')
(***) l1 l2 = reparam (l1 **** l2) Lunitor

infixl 9 |>>
public export
(|>>) : DLens xs yr -> ParaDLens pq yr zt -> ParaDLens pq xs zt
(|>>) l1 l2 = reparam (l1 >>> l2) Lunitor


infixl 9 <<|
public export
(<<|) : ParaDLens pq xs yr -> DLens yr zt -> ParaDLens pq xs zt
(<<|) l1 l2 =  reparam (l1 >>> l2) Runitor

||| Identity lens
|||
||| The identity morphism in the category of dependent lenses.
public export
idLens : DLens xs xs
idLens = MkDLens id (\x, ry => ry)

