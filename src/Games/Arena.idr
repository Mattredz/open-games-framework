module Games.Arena

import Lens.Definition
import Container.Definition

public export
Arena : (pq, xs, yr : Container) -> Type
Arena = ParaLens

