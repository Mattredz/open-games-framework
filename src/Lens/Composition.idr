module Lens.Composition

import Container.Definition
import Container.Product
import Lens.Definition

%default total

infixr 5 >>>>

public export
(>>>>)
  : {pq, xs, yr, pq', zt : Container}
 -> ParaLens pq  xs yr
 -> ParaLens pq' yr zt
 -> ParaLens (ProdCont pq pq') xs zt
(>>>>) (MkPLens fwd bwd) (MkPLens fwd' bwd') =
  MkPLens compF compB
  where

    pL pP = fst (unpackProdShape {c1=pq} {c2=pq'} pP)

    pR pP = snd (unpackProdShape {c1=pq} {c2=pq'} pP)

    compF pP x = fwd' (pR pP) (fwd (pL pP) x)

    compB pP x posZ =
      let (posY , posPQ') = bwd' (pR pP) (fwd (pL pP) x) posZ
          (posX , posPQ ) = bwd  (pL pP) x                posY
      in  ( posX, packProdPositionAt {c1=pq} {c2=pq'} pP posPQ posPQ' )
