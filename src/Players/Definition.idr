module Players.Definition

import Lens.Definition
import Lens.Product
import Lens.Composition
import Container.Definition
import Container.Morphism
import Container.RDiff
import Container.Product

public export
Player : (profiles, actions : Type) -> (actions -> Type) -> Type
Player profiles actions utility = NonParaLens (rDiff $ CMk (profiles ** (\p => Bool))) (rDiff $ CMk (actions ** utility))

public export
nashator
  : {a1 : Type} -> {a2 : Type} -> {u1 : a1 -> Type} -> {u2 : a2 -> Type} ->
    NonParaLens
       (ProdCont (rDiff (CMk (a1 ** u1)))
                 (rDiff (CMk (a2 ** u2))))
       (rDiff (CMk ((a1,a2) ** (\xx => (u1 $ fst xx, u2 $ snd xx)))))
nashator {a1} {a2} {u1} {u2} = MkNonParaLens
  (\(a1v, a2v) => (a1v, a2v))                                -- fwd (shape invariata)
  (\(a1v, a2v), k =>                                          -- bwd: k : (a1,a2) -> (u1 a1, u2 a2)
      ( (\x1 => fst (k (x1, a2v)))                   --  k1 : a1 -> u1 a1
      , (\x2 => snd (k (a1v, x2)))                   --  k2 : a2 -> u2 a2
      )
  )


public export
oplaxator
  : {s1,s2 : Type}
  -> NonParaLens
       (CMk ((s1,s2) ** \_ => (s1,s2) -> Bool))
       (ProdCont (CMk (s1 ** \_ => s1 -> Bool))
                 (CMk (s2 ** \_ => s2 -> Bool)))
oplaxator = MkPLens
  (\(), (x1, x2) => (x1, x2))                 -- forward: identità su shape
  (\(), (x1, x2), (phi, psi) =>                -- backward: (x1,x2) ↦ phi x1 ∧ psi x2
      (\(y1, y2) => phi y1 && psi y2, ())
  )


infixl 6 ####
public export
(####) : {s1,s2 : Type} -> {u1 : s1 -> Type} -> {u2 : s2 -> Type}
    -> Player s1 s1 u1 -> Player s2 s2 u2 -> Player (s1,s2) (s1,s2) (\xx => (u1 $ fst xx, u2 $ snd xx))
p1 #### p2 = oplaxator >>>> (p1 **** p2) >>>> nashator

