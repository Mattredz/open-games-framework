module Container.Normalization

import Container.Definition


normType : Type -> Type
normType Unit = Unit
normType (Unit, t) = normType t
normType (t, Unit) = normType t
normType t = t

normDepType : {s : Type} -> (p : s -> Type) -> (normType s -> Type)
normDepType {s = Unit} p = p
normDepType {s = (Unit, t)} p = normDepType {s = t} (\x => p ((), x))
normDepType {s = (t, Unit)} p = normDepType {s = t} (\x => p (x, ()))
normDepType {s} p = p

public export
normalizeCont : (c : Container) -> Container
normalizeCont MkCUnit = MkCUnit
normalizeCont (MkCont Unit pos) = MkCont Unit (const $ normType $ pos ())
normalizeCont (MkCont (Unit, t) pos) = MkCont (normType t) (normType pos)
normalizeCont (MkCont (t, Unit) pos) = MkCont (normType t) (\t => normType $ pos ?somees)
normalizeCont c = c
