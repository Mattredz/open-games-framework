module Container.Coproduct

import Container.Definition

public export
(+) : (c1, c2 : Container) -> Container
(+) c1 c2 = MkCont (Either (shape c1)  (shape c2) ) (\(xx) => case xx of
    Left x => position c1 x
    Right x' => position c2  x'
    )

