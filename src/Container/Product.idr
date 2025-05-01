module Container.Product

import Container.Definition

public export
(*) : (c1, c2 : Container) -> Container
(*) c1 c2 = (c1.shape, c2.shape) <! (\(x, x') => (c1.position x, c2.position x'))
