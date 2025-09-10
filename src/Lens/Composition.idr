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
  MkPLens 
    (\pP, x => fwd' (snd $ unpackProdShape pP) (fwd (fst $ unpackProdShape pP) x))
    (\pP, x, posZ =>
      let (posY, posPQ') = bwd' (snd $ unpackProdShape pP) (fwd (fst $ unpackProdShape pP) x) posZ
          (posX, posPQ)  = bwd  (fst $ unpackProdShape pP) x posY
      in  (posX, packProdPositionAt pP posPQ posPQ'))
