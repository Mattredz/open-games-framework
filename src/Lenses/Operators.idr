||| Categorical operators for composing dependent lenses
||| This module provides composition operators that respect the categorical
||| structure of parameterized dependent lenses.
module Lenses.Operators

import public Lenses.ParaDLens
import public Lenses.DTypes

%default total



infixr 9 >>>
public export
(>>>) : ParaDLens p q xs yr ->
        ParaDLens p' q' yr zt ->
        ParaDLens (p, p') (q, q') xs zt
(>>>) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) = 
  MkParaLens
  (\(p, p'), x => play2 p' (play1 p x))
  (\(p, p'), x, zt => 
      let (r, q2) = coplay2 p' (play1 p x) zt
          (s, q1) = coplay1 p x r
      in (s, (q1, q2)))


infixl 9 |>>
public export
(|>>) : DLens xs yr -> ParaDLens p q yr zt -> ParaDLens p q xs zt
(|>>) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens
    (\p, x => play2 p (play1 () x))
    (\p, x, tz =>
        let (r, q2) = coplay2 p (play1 () x) tz
            (s, _)  = coplay1 () x r
        in (s, q2))


infixl 9 <<|
public export
(<<|) : ParaDLens p q xs yr -> DLens yr zt -> ParaDLens p q xs zt
(<<|) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens
    (\p, x => play2 () (play1 p x))
    (\p, x, tz =>
        let (r, _)  = coplay2 () (play1 p x) tz
            (s, q1) = coplay1 p x r
        in (s, q1))

infixr 10 ***
public export
(***) : ParaDLens p q xs yr ->
        ParaDLens p' q' xs' yr' ->
        ParaDLens (p, p') (q, q') (DProd xs xs') (DProd yr yr')
(***) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens 
    (\(p, p'), (x, x') => (play1 p x, play2 p' x'))
    (\(p, p'), (x, x'), (ry, ry') =>
        let (s1, q1) = coplay1 p x ry
            (s2, q2) = coplay2 p' x' ry'
        in ((s1, s2), (q1, q2)))

infixr 10 +++
public export
(+++) : ParaDLens p q xs yr ->
        ParaDLens p' q' xs' yr' ->
        ParaDLens (p, p') (Either q q') (DEither xs xs') (DEither yr yr')
(+++) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens
    (\(p, p'), e => case e of
                 Left  x  => Left  (play1 p x)
                 Right x' => Right (play2 p' x'))
    (\(p, p'), e, zt => case e of
                     Left x  => let (s, q) = coplay1 p x zt in (s, Left q)
                     Right x' => let (s, q') = coplay2 p' x' zt in (s, Right q'))

||| Dependent coproduct for non-parameterized lenses
public export
DCoProd : DLens xs yr ->
          DLens xs' yr' ->
          DLens (DEither xs xs') (DEither yr yr')
DCoProd (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkDLens
    (\e => case e of
            Left  x  => Left  (play1 () x)
            Right x' => Right (play2 () x'))
    (\e, zt => case e of
                Left x  => let (s, _) = coplay1 () x zt in s
                Right x' => let (s, _) = coplay2 () x' zt in s)

||| Counitor: collapses Either unit to unit
public export
CoUnitor : DLens (Either x x ** SEither (const s) (const s)) (x ** const s)
CoUnitor = MkDLens
    (\case Left  x => x
           Right x => x)
    (\case 
            Left _ => id
            Right _ => id)

||| Parameterized counitor
public export
ParaCoUnitor : DLens DUnit (((), ()) ** const (Either () ()))
ParaCoUnitor = MkDLens
    (\_ => ((), ()))
    (\_, _ => ())

||| Product unitor: unit product isomorphism
public export
ProdUnitor : DLens (DProd DUnit DUnit) DUnit
ProdUnitor = MkDLens
    (\_ => ())
    (\_, _ => ((), ()))
