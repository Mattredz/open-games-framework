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

    playP pP xX = packProdShape {c1=yr} {c2=yr'} 
                    (play (pL pP) (xL xX)) 
                    (play' (pR pP) (xR xX))

    coplayP pP xX posYY = 
      let posL = fst (unpackProdPositionAt {c1=yr} {c2=yr'} 
                   (play (pL pP) (xL xX)) 
                   (play' (pR pP) (xR xX)) 
                   posYY)
          posR = snd (unpackProdPositionAt {c1=yr} {c2=yr'} 
                   (play (pL pP) (xL xX)) 
                   (play' (pR pP) (xR xX)) 
                   posYY)
          (xsL, pqL) = coplay (pL pP) (xL xX) posL
          (xsR, pqR) = coplay' (pR pP) (xR xX) posR
      in  (packProdPositionAt {c1=xs} {c2=xs'} xX xsL xsR,
           packProdPositionAt {c1=pq} {c2=pq'} pP pqL pqR)
