module Container.RDiff

import Container.Definition

%default total

public export %inline
rDiff : Container -> Container
rDiff c = CMk (shape c ** (\_ => (x' :shape c) -> position c x'))

public export %inline
rDiffShapeEq : (c : Container) -> shape (rDiff c) = shape c
rDiffShapeEq CUnit      = Refl
rDiffShapeEq (CMk (s ** p))    = Refl

public export %inline
toOrig  : {c : Container} -> shape (rDiff c) -> shape c
toOrig  {c} s = rewrite sym (rDiffShapeEq c) in s

public export %inline
toRDiff : {c : Container} -> shape c -> shape (rDiff c)
toRDiff {c} s = rewrite (rDiffShapeEq c) in s

