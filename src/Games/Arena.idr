module Games.Arena

import Lens.Definition
import Container.Definition

public export
Arena : (pq, xs, yr : Container) -> Type
Arena = ParaLens

public export
corner : ParaLens c CUnit c
corner = MkPLens const (\_, _, r => ((), r))
