module Games.Arena

import Optics.Lens

public export
Arena : (pq : Cont) -> ParaCont pq -> Cont -> Type
Arena pq xs yr = ParaDepLens pq xs yr

public export
corner : ParaDepLens (MkCo p q) (MkParaCont (const ()) (\_ => const ())) (MkCo p q)
corner = MkPLens (\p, _ => p) (\p, _, r => ((), r))
