||| Categorical operators for composing dependent lenses
||| This module provides composition operators that respect the categorical
||| structure of parameterized dependent lenses.
module Lenses.Operators

import public Lenses.ParaDLens
import public Lenses.DTypes

%default total

infixr 9 >>>
public export
(>>>) : ParaDLens pq xs yr ->
        ParaDLens pq' yr zt ->
        ParaDLens (DProd pq pq') xs zt
(>>>) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) = 
  MkParaLens
  (\(p, p'), x => play2 p' (play1 p x))
  (\(p, p'), x, zt => 
      let (r, q2) = coplay2 p' (play1 p x) zt
          (s, q1) = coplay1 p x r
      in (s, (q1, q2)))


infixr 10 ****
public export
(****) : ParaDLens pq xs yr ->
        ParaDLens pq' xs' yr' ->
        ParaDLens (DProd pq pq') (DProd xs xs') (DProd yr yr')
(****) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens 
    (\(p, p'), (x, x') => (play1 p x, play2 p' x'))
    (\(p, p'), (x, x'), (ry, ry') =>
        let (s1, q1) = coplay1 p x ry
            (s2, q2) = coplay2 p' x' ry'
        in ((s1, s2), (q1, q2)))

infixr 10 ++++
public export
(++++) : ParaDLens pq xs yr ->
        ParaDLens pq' xs' yr' ->
        ParaDLens ((pq.fst, pq'.fst) ** \pp => Either (pq.snd (fst pp)) (pq'.snd (snd pp)))
                  (DEither xs xs') 
                  (DEither yr yr')
(++++) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
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
public export
Lunitor : DLens xs (((), xs.fst) ** \xx => ((), xs.snd (snd xx)))
Lunitor = MkDLens
    (\x => ((), x))
    (\_, ((), s) => s)

public export
Runitor : DLens xs ((xs.fst, ()) ** \xx => (xs.snd (fst xx), ()))
Runitor = MkDLens
    (\x => (x, ()))
    (\_, (s, ()) => s)

public export
diffLunitor : DLens DUnit (() ** const (() -> ()))
diffLunitor = MkDLens
    (\_ => ())
    (\_, _ => ())

public export
diffRunitor : DLens (() ** const (() -> ())) DUnit
diffRunitor = MkDLens
    (\_ => ())
    (\_, _ => const ())