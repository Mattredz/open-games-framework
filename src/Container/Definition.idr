module Container.Definition


infixr 5 <!  -- container 

public export
record Container where
    constructor (<!)
    shape    : Type
    position : shape -> Type

