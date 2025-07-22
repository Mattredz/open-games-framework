module Container.Product

import Container.Definition
%hide Prelude.Ops.infixl.(*)

infixr 5 *
public export
(*) : (c1 : Container) -> (c2 : Container) -> Container
(*) MkCUnit c2 = c2
(*) c1 MkCUnit = c1
(*) (MkCont sh pos) (MkCont sh' pos') = MkCont (sh, sh') (\(x, y) => (pos x, pos' y))


