module Games.Arena

import Optics.Lens

public export
Arena : Cont -> Cont -> Cont -> Type
Arena pq xs yr = ParaDepLens pq xs yr

public export
corner : ParaDepLens (MkCo p q) (MkCo Unit (\_ => Unit)) (MkCo p q)
corner = MkPLens (\(p, _) => p) (\(p, _), r => ((), r))
