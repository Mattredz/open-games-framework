module Optics.Lens 

SEither : (a -> Type) -> (b -> Type) ->
          Either a b -> Type
SEither fa fb e = case e of
    Left  x => fa x
    Right y => fb y

public export
record Cont where
  constructor MkCo
  sh : Type
  pos : sh -> Type

public export
record ParaDepLens (pq : Cont) (xs : Cont) (yr : Cont) 
  {default (MkCo (pq.sh, xs.sh) (\(p, x) => (xs.pos x, pq.pos p))) cc : Cont} where
  constructor MkPLens
  play : cc.sh -> yr.sh
  coplay : (px : cc.sh) -> yr.pos (play px) -> cc.pos px

public export
DLens : (xs : Cont) -> (yr : Cont) -> Type
DLens xs yr = ParaDepLens (MkCo () (const ())) xs yr

public export
MkDLens : (play : x -> y) ->
          (coplay : (x' : x) -> r (play x') -> s x') ->
          ParaDepLens (MkCo () (const ())) (MkCo x s) (MkCo y r)
MkDLens play coplay =
  MkPLens
    (\((), x) => play x)
    (\((), x), ry => (coplay x ry, ()))


infixr 6 >>>
infixr 7 ### 
infixr 5 +++

public export
(>>>) : ParaDepLens pq xs yr -> ParaDepLens pq' yr zr 
      -> ParaDepLens (MkCo (pq.sh, pq'.sh) (\pp => (pq.pos (fst pp), pq'.pos (snd pp)))) xs zr
(>>>) (MkPLens p1 cp1) (MkPLens p2 cp2) = 
  MkPLens
    (\((p, p'), x) => p2 (p', (p1 (p, x))))
    (\((p, p'), x), z => let (r, q') = cp2 (p', (p1 (p, x))) z
                             (s, q ) = cp1 (p, x) r
                         in (s, (q, q')))

public export
(###)  : ParaDepLens {cc = cc1} pq xs yr -> ParaDepLens {cc = cc2} pq' xs' yr' 
      -> ParaDepLens (MkCo (pq.sh, pq'.sh) (\pp => (pq.pos (fst pp), pq'.pos (snd pp))))
                     (MkCo (xs.sh, xs'.sh) (\xx => (xs.pos (fst xx), xs'.pos (snd xx))))
                     (MkCo (yr.sh, yr'.sh) (\yy => (yr.pos (fst yy), yr'.pos (snd yy))))
                     {cc = MkCo (cc1.sh, cc2.sh) (\cc => (cc1.pos (fst cc), cc2.pos (snd cc)))}
(###) (MkPLens p1 cp1) (MkPLens p2 cp2) = 
  MkPLens
    (\(px, px') => (p1 (px), p2 (px')))
    (\(px, px'), (y, y') => (cp1 px y, cp2 px' y'))
    

public export
(+++)  : ParaDepLens pq xs yr -> ParaDepLens pq' xs' yr' 
      -> ParaDepLens (MkCo (Either pq.sh pq'.sh) (SEither pq.pos pq'.pos)) 
                     (MkCo (Either xs.sh xs'.sh) (SEither xs.pos xs'.pos)) 
                     (MkCo (Either yr.sh yr'.sh) (SEither yr.pos yr'.pos))
                     {cc = MkCo (Either (pq.sh, xs.sh) (pq'.sh, xs'.sh)) 
                                  (SEither (\(p, x) => (xs.pos x, pq.pos p)) 
                                           (\(p', x') => (xs'.pos x', pq'.pos p')))}
(+++)  (MkPLens p1 cp1) (MkPLens p2 cp2) = 
  MkPLens
    (\case Left (p, x) => Left (p1 (p, x)); Right (p', x') => Right (p2 (p', x')))
    (\case Left (p, x) => cp1 (p, x); Right (p', x') => cp2 (p', x'))

public export
lunitor : DLens (MkCo () (const ())) (MkCo () (\x => () -> ()))
lunitor = MkDLens (\() => ()) (\_, _ => ()) 

public export
paralunitor : {p : Type} -> {q : p -> Type} ->
          ParaDepLens (MkCo ((), p) (\pp => (const () (fst pp), q (snd pp)))) xs yr
          -> ParaDepLens (MkCo p q) xs yr
paralunitor (MkPLens f b) =
  MkPLens
    (\(p, x) => f (((), p), x))
    (\(p, x), ry => let (s, (_, q)) = b (((), p), x) ry in (s, q))


public export
runitor : DLens (MkCo () (\x => () -> ())) (MkCo () (const ()))
runitor = MkDLens (\_ => ()) (\_, _ => const ())

public export
pararunitor : {p : Type} -> {q : p -> Type} ->
          ParaDepLens (MkCo (p, ()) (\pp => (q (fst pp), const () (snd pp)))) xs yr
          -> ParaDepLens (MkCo p q) xs yr
pararunitor (MkPLens f b) =
  MkPLens
    (\(p0, x0) => f ((p0, ()), x0))
    (\(p, x), ry => let (s, (q, _)) = b ((p, ()), x) ry in (s, q))

