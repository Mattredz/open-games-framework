module Optics.Lens 

infixr 6 >>>
infixr 7 ### 
infixr 5 +++


public export
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
record ParaCont (pq : Cont) where
  constructor MkParaCont
  shape : pq.sh -> Type
  position : (p' : pq.sh) -> shape p' -> Type


public export
record ParaDepLens (pq : Cont) (xs : ParaCont pq) (yr : Cont) where
  constructor MkPLens
  play : (p' : pq.sh) -> xs.shape p' -> yr.sh
  coplay : (p' : pq.sh) -> (x : xs.shape p') -> yr.pos (play p' x) -> (xs.position p' x, pq.pos p')



public export
DLens : (xs : Cont) -> (yr : Cont) -> Type
DLens xs yr = ParaDepLens (MkCo () (const ())) (MkParaCont (const xs.sh) (const xs.pos)) yr

public export
MkDLens : (play : x -> y) ->
          (coplay : (x' : x) -> r (play x') -> s x') ->
          ParaDepLens (MkCo () (const ())) (MkParaCont (\p => x) (const s)) (MkCo y r)
MkDLens play coplay =
  MkPLens
    (\_, x => play x)
    (\_, x, ry => (coplay x ry, ()))


public export
(>>>) : ParaDepLens pq ((MkParaCont (\p => x) (\p => s))) (MkCo y r) -> ParaDepLens pq' (MkParaCont (\p => y) (\p => r)) zt 
           -> ParaDepLens (MkCo (pq.sh, pq'.sh) (\pp => (pq.pos (fst pp), pq'.pos (snd pp)))) ((MkParaCont (\p => x) (\p => s))) zt
(>>>) (MkPLens play1 coplay1) (MkPLens play2 coplay2) = 
  MkPLens 
  --play
  (\(p, p'), x => play2 p' (play1 p x))
  --coplay
  (\(p, p'), x, zt => let (r, q') = coplay2 p' (play1 p x) zt
                          (s, q) = coplay1 p x r
                       in (s, (q, q')))


public export
(###) : ParaDepLens pq xs yr -> ParaDepLens pq' xs' yr' 
           -> ParaDepLens (MkCo (pq.sh, pq'.sh) (\pp => (pq.pos (fst pp), pq'.pos (snd pp)))) 
                  (MkParaCont (\pp => (xs.shape (fst pp), xs'.shape (snd pp))) 
                              (\pp, xx => (xs.position (fst pp) (fst xx), xs'.position (snd pp) (snd xx))))
                  (MkCo (yr.sh, yr'.sh) (\yy => (yr.pos (fst yy), yr'.pos (snd yy))))
(###) (MkPLens play1 coplay1) (MkPLens play2 coplay2) = 
  MkPLens
    (\(px, px'), (x, x') => (play1 px x, play2 px' x'))
    (\(px, px'), (x, x'), (y, y') => let (s, q) = coplay1 px x y
                                         (s', q') = coplay2 px' x' y'
                                      in ((s, s'), (q, q')))

public export
(+++) : ParaDepLens pq xs yr -> ParaDepLens pq' xs' yr' 
           -> ParaDepLens (MkCo (Either pq.sh pq'.sh) (SEither pq.pos pq'.pos)) 
                  (MkParaCont (SEither xs.shape xs'.shape) 
                              (\case Left p => xs.position p; Right p' => xs'.position p'))
                  (MkCo (Either yr.sh yr'.sh) (SEither yr.pos yr'.pos))
(+++) (MkPLens play1 coplay1) (MkPLens play2 coplay2) = 
  MkPLens
    (\case Left p => \x => Left (play1 p x) ; Right p' => \x' => Right (play2 p' x'))
    (\case Left p => coplay1 p; Right p' => coplay2 p')


public export
lunitor : DLens (MkCo () (const ())) (MkCo () (\x => () -> ()))
lunitor = MkDLens (\() => ()) (\_, _ => ()) 

public export
paralunitor : ParaDepLens (MkCo ((), p) (\pp => (const () (fst pp), q (snd pp)))) xs yr
              -> ParaDepLens (MkCo p q) (MkParaCont (\p => xs.shape ((), p)) (\p => xs.position ((), p))) yr
paralunitor (MkPLens f b) =
  MkPLens
    (\p, x => f ((), p) x)
    (\p, x, ry => let (s, (_, q)) = b ((), p) x ry in (s, q))


public export
runitor : DLens (MkCo () (\x => () -> ())) (MkCo () (const ()))
runitor = MkDLens (\_ => ()) (\_, _ => const ())

public export
pararunitor : ParaDepLens (MkCo (p, ()) (\pp => (q (fst pp), const () (snd pp)))) xs yr
              -> ParaDepLens (MkCo p q) (MkParaCont (\p => xs.shape (p, ())) (\p => xs.position (p, ()))) yr
pararunitor (MkPLens f b) =
  MkPLens
    (\p0, x0 => f (p0, ()) x0)
    (\p, x, ry => let (s, (q, _)) = b (p, ()) x ry in (s, q))

