module Players.Definition

import Lens.Definition
import Container.Definition
import Container.Morphism


public export
Player : (profiles, actions : Type) -> (actions -> Type) -> Type
Player profiles actions utility = DepLens (MkCont profiles (\p => Bool)) (MkCont actions utility)
    
public export
MkPlayer : CMorph (MkCont profiles (\p => Bool)) (MkCont actions utility)-> Player profiles actions utility
MkPlayer = MkDepLens
