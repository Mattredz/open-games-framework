||| Combinators for constructing and manipulating games
|||
||| This module provides advanced combinators for building complex
||| game structures from simpler components.
module GameTheory.Combinators

import public Lenses.DTypes
import public Lenses.ParaDLens
import public Lenses.Operators

%default total

||| Reverse differentiation of a parameterized lens
|||
||| Constructs a lens that exposes the dependency structure
||| for computing derivatives with respect to parameters.
public export
ParaRDiff : ParaDLens p q xs yr ->
            ParaDLens p (p -> q)
                      (xs.fst ** const ((x : xs.fst) -> xs.snd x)) 
                      (yr.fst ** const ((y : yr.fst) -> yr.snd y))
ParaRDiff (MkParaLens play1 coplay1) =
  MkParaLens
    play1
    (\p, x, ry =>
      let s = \x => fst $ coplay1 p x (ry $ play1 p x)
          g = \p => snd $ coplay1 p x (ry $ play1 p x)
      in (s, g))

||| Right unitor for dependent lenses
public export
Drunitor : DLens (() ** const (() -> ())) DUnit
Drunitor = MkDLens (\_ => ()) (\_, _ => const ())

||| Left unitor for dependent lenses
public export
Dlunitor : DLens DUnit (() ** const (() -> ()))
Dlunitor = MkDLens (\_ => ()) (\_, _ => ())

||| Reparameterization combinator
|||
||| Changes the parameter space of a parameterized lens by
||| composing with a lens that transforms parameters.
|||
||| @ l The original parameterized lens
||| @ param The parameter transformation lens
public export
reparam : ParaDLens a u xs yr ->
          DLens (p ** const q) (a ** const u) ->
          ParaDLens p q xs yr
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
corner : ParaDLens p q DUnit (p ** const q)
corner = MkParaLens
    (\p, _ => p)
    (\p, _, ry => ((), ry))

||| Product of dependent lenses
|||
||| Combines two non-parameterized lenses into a product lens.
public export
DLensProd : DLens xs yr ->
            DLens xs' yr' ->
            DLens (DProd xs xs') (DProd yr yr')
DLensProd (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
  MkDLens
  (\(x, x') => (play1 () x, play2 () x'))
  (\(x, x'), (ry, ry') =>
      let (s1, _) = coplay1 () x ry
          (s2, _) = coplay2 () x' ry'
      in (s1, s2))

||| Identity lens
|||
||| The identity morphism in the category of dependent lenses.
public export
idLens : DLens xs xs
idLens = MkDLens id (\x, ry => ry)

