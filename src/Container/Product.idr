module Container.Product

import Container.Definition


%default total

infixr 4 ***

-- Prodotto monoidale ----------------------------------------

public export %inline
ProdCont : Container -> Container -> Container
ProdCont CUnit c2 = c2
ProdCont c1 CUnit = c1
ProdCont (CMk (s ** p)) (CMk (s' ** p')) =
  CMk ((s, s') ** \xy => (p (fst xy), p' (snd xy)))


public export
(***) : Container -> Container -> Container
(***) = ProdCont

-- HINT: leggi d’unità per aiutare l’unificazione nei tipi
public export %hint
leftUnitProd  : (c : Container) -> ProdCont CUnit c = c
leftUnitProd _ = Refl

public export %inline
rightUnitProd : (c : Container) -> ProdCont c CUnit = c
rightUnitProd CUnit    = Refl
rightUnitProd (CMk _)  = Refl





-- Pack / Unpack su shape ------------------------------------

public export
unpackProdShape :
  {c1, c2 : Container} ->
  shape (ProdCont c1 c2) -> (shape c1, shape c2)
unpackProdShape {c1 = CUnit} x = ((), x)
unpackProdShape {c1 = CMk _} {c2 = CUnit} x = (x, ())
unpackProdShape {c1 = CMk (s ** _)} {c2 = CMk (s' ** _)} (x, y) = (x, y)

public export
packProdShape :
  {c1, c2 : Container} ->
  shape c1 -> shape c2 -> shape (ProdCont c1 c2)
packProdShape {c1 = CUnit} _ y = y
packProdShape {c1 = CMk _} {c2 = CUnit} x _ = x
packProdShape {c1 = CMk (s ** _)} {c2 = CMk (s' ** _)} x y = (x, y)

-- Pack / Unpack su position alla shape data -----------------

public export
unpackProdPositionAt :
  {c1, c2 : Container} ->
  (s1 : shape c1) -> (s2 : shape c2) ->
  position (ProdCont c1 c2) (packProdShape {c1} {c2} s1 s2) ->
  ( position c1 s1 , position c2 s2 )
unpackProdPositionAt {c1 = CUnit}              _  s2 pos = ((), pos)
unpackProdPositionAt {c1 = CMk _} {c2 = CUnit} s1 _  pos = (pos, ())
unpackProdPositionAt {c1 = CMk (s ** _)} {c2 = CMk (s' ** _)} _ _ (px, py) = (px, py)

public export
packProdPositionAt :
  {c1, c2 : Container} ->
  (sh : shape (ProdCont c1 c2)) ->
  position c1 (fst (unpackProdShape {c1} {c2} sh)) ->
  position c2 (snd (unpackProdShape {c1} {c2} sh)) ->
  position (ProdCont c1 c2) sh
packProdPositionAt {c1 = CUnit}                      _  () py = py
packProdPositionAt {c1 = CMk _} {c2 = CUnit}         _  px () = px
packProdPositionAt {c1 = CMk (s ** _)} {c2 = CMk (s' ** _)} (x', y') px py = (px, py)
