module Container.Coproduct

import Container.Definition

public export
(+) : (c1, c2 : Container) -> Container
(+) c1 c2 = (Either c1.shape c2.shape) <! (\(xx) => case xx of
    Left x => c1.position x
    Right x' => c2.position x'
    )

