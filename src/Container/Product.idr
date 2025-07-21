module Container.Product

import Container.Definition
%hide Prelude.Ops.infixl.(*)

infixr 5 *
public export
(*) : (c1 : Container) -> (c2 : Container) -> Container
(*) c1 MkCUnit = c1
(*) MkCUnit c2 = c2
(*) (MkCont sh pos) (MkCont sh' pos') = MkCont (sh, sh') (\(x, y) => (pos x, pos' y))


