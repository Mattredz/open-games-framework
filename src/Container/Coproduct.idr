module Container.Coproduct

import Container.Definition


public export
SumCont : Container -> Container -> Container
SumCont c1 c2 = CMk (Either (shape c1) (shape c2) ** \e => case e of
  Left x => position c1 x
  Right y => position c2 y)

