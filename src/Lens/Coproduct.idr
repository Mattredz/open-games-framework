module Lens.Coproduct

import Lens.Definition
import Container.Definition
import Container.Product
import Container.Coproduct

infixr 5 +++

public export
(+++) : ParaLens (MkCont p (\x => q)) xs yr -> ParaLens (MkCont p' (\x => q)) xs' yr' -> ParaLens (MkCont (p, p') (\x => q)) (xs + xs') (yr + yr')
(+++) (MkParaLens fwd bwd) (MkParaLens fwd' bwd') = MkParaLens
    (\(p, p'), xx => case xx of
        Left x => Left (fwd p x)
        Right x' => Right (fwd' p' x')
    )
    (\(p, p'), xx, t => case xx of
        Left x => bwd p x t
        Right x' => bwd' p' x' t
    )
