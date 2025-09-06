module Lens.Product

import Lens.Definition
import Container.Definition
import Container.Product

infixr 4 ****

%default total

public export %inline
(****)
  : {pq, xs, yr, pq', xs', yr' : Container}
  -> ParaLens pq  xs  yr
  -> ParaLens pq' xs' yr'
  -> ParaLens (ProdCont pq pq') (ProdCont xs xs') (ProdCont yr yr')
(****) (MkPLens play  coplay)
         (MkPLens play' coplay') =
  MkPLens playP coplayP
  where
    pL pP = fst (unpackProdShape {c1=pq} {c2=pq'} pP)
    pR pP = snd (unpackProdShape {c1=pq} {c2=pq'} pP)
    xL xX = fst (unpackProdShape {c1=xs} {c2=xs'} xX)
    xR xX = snd (unpackProdShape {c1=xs} {c2=xs'} xX)

    yL pP xX = play  (pL pP) (xL xX)
    yR pP xX = play' (pR pP) (xR xX)

    playP pP xX = packProdShape {c1=yr} {c2=yr'} (yL pP xX) (yR pP xX)

    -- Prova definizionale: utile per rewrite negli helper delle posizioni
    public export %inline
    reflPlay :
         (pP : shape (ProdCont pq pq'))
      -> (xX : shape (ProdCont xs xs'))
      -> playP pP xX
       = packProdShape {c1=yr} {c2=yr'} (yL pP xX) (yR pP xX)
    reflPlay _ _ = Refl

    posL pP xX posYY =
      fst (unpackProdPositionAt {c1=yr} {c2=yr'}
             (yL pP xX) (yR pP xX)
             (rewrite (reflPlay pP xX) in posYY))


    posR pP xX posYY =
      snd (unpackProdPositionAt {c1=yr} {c2=yr'}
             (yL pP xX) (yR pP xX)
             (rewrite (reflPlay pP xX) in posYY))

    xsOut pP xX posYY =
      let a = coplay  (pL pP) (xL xX) (posL pP xX posYY)
          b = coplay' (pR pP) (xR xX) (posR pP xX posYY)
      in  packProdPositionAt {c1=xs} {c2=xs'} xX (fst a) (fst b)

    pqOut pP xX posYY =
      let a = coplay  (pL pP) (xL xX) (posL pP xX posYY)
          b = coplay' (pR pP) (xR xX) (posR pP xX posYY)
      in  packProdPositionAt {c1=pq} {c2=pq'} pP (snd a) (snd b)

    -- Backward finale: nessun case; può essere una one-liner
    coplayP pP xX posYY = ( xsOut pP xX posYY , pqOut pP xX posYY )
