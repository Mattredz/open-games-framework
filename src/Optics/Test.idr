module Optics.Test

import Interfaces.Listable
import Players.Argmax
%hide Optics.Lens.infixr.(>>>)

record DParaLens (x : Type) (s : x -> Type)
                 (p : x -> Type) (q : (x' : x) -> p x' -> Type) 
                 (y : Type) (r : y -> Type)
    where
    constructor MkDPLens
    play : (x' : x) -> p x' -> y
    coplay : (x' : x) -> (p1 : p x') -> r (play x' p1) -> (s x', q x' p1)

DepLens : (x : Type) -> (s : x -> Type) ->
          (y : Type) -> (r : y -> Type) ->
          Type
DepLens x s y r = DParaLens x s (\_ => Unit) (\_ => const Unit) y r

MkDepLens : (play : (x' : x) -> y) ->
            (coplay : (x' : x) -> r (play x') -> s x') ->
            DepLens x s y r
MkDepLens play coplay =
    MkDPLens
        (\x, _ => play x)
        (\x, _, ry => (coplay x ry, ()))
        
comp : (l1 : DParaLens x s p q y r) ->
       DParaLens y r p' q' z t ->
       DParaLens x s 
       (\x => (p1 : p x ** p' (l1.play x p1))) -- p
       (\x, pp => (q x (fst pp), q' (l1.play x (fst pp)) (snd pp))) -- q
       z t
comp (MkDPLens play1 coplay1) (MkDPLens play2 coplay2) = 
  MkDPLens
  --play
  (\x, pp => play2 (play1 x (fst pp)) (snd pp))
  --coplay
  (\x, pp, zt =>    let (r, q2) = coplay2 (play1 x (fst pp)) (snd pp) zt
                        (s, q1) = coplay1 x (fst pp) r
                            in  (s, (q1, q2)))

LunitComp : 
            DParaLens x s (\x => (p1 : () ** p (play1 x p1))) (\x, pp => ((), q' (play1 x (fst pp)) (snd pp))) z t ->
            DParaLens x s p q z t
LunitComp (MkDPLens play coplay) = 
    MkDPLens
    --play
    (\x, pp => play x (() ** pp))
    --coplay
    (\x, pp, ry => let (s, ((), q)) = coplay x (() ** pp) ry in (s, q))

RunitComp : 
            DParaLens x s (\x1 => (p1 : p x1 ** ())) (\x1, p1 => (q x1 (p1.fst), ())) z t ->
            DParaLens x s p q z t
RunitComp (MkDPLens play coplay) =
    MkDPLens
    --play
    (\x, pp => play x (pp ** ()))
    --coplay
    (\x, pp, ry => let (s, (q, ())) = coplay x (pp ** ()) ry in (s, q))

    
prod : 
    DParaLens  x s p q y r ->
    DParaLens x' s' p' q' y' r' ->
    DParaLens (x, x') (\xx => (s (fst xx), s' (snd xx)))
              (\xx => (p (fst xx), p' (snd xx))) (\xx, pp => (q (fst xx) (fst pp), q' (snd xx) (snd pp)))
              (y, y') (\yy => (r (fst yy), r' (snd yy)))
prod (MkDPLens play1 coplay1) (MkDPLens play2 coplay2) =
    MkDPLens 
    --play
    (\(x, x'), (p1, p2) => (play1 x p1, play2 x' p2) )
    --coplay
    (\(x, x'), (p1, p2), (y, y') => let (s1, q1) = coplay1 x p1 y
                                        (s2, q2) = coplay2 x' p2 y'
                                    in ((s1, s2), (q1, q2)) )


public export
SEither : (a -> Type) -> (b -> Type) ->
                Either a b -> Type
SEither fa fb e = case e of
        Left  x => fa x
        Right y => fb y

coprod : 
        DParaLens   x s p q y r ->
        DParaLens   x' s' p' q' y' r' ->
        DParaLens   (Either x x') (SEither s s') 
                    (SEither p p') (\e, ep => case e of
                                            Left x  => q x ep
                                            Right x' => q' x' ep)
                    (Either y y') (SEither r r')
coprod (MkDPLens play1 coplay1) (MkDPLens play2 coplay2) = 
        MkDPLens
        --play
        (\e, p => case e of
                        Left x  => Left  (play1 x p)
                        Right x' => Right (play2 x' p) )
        --coplay
        (\e, p, zt => case e of
                                Left x  => coplay1 x p zt
                                Right x' => coplay2 x' p zt)


public export
paraStateToFun : DParaLens () (const ()) p q () (const ()) -> ((a : p ()) -> q () a)
paraStateToFun (MkDPLens _ bwd) p0 = snd (bwd () p0 ())


-- | A State is a DepLens from the unit container to a container over x
public export
State : (y : Type) -> (r : y -> Type) -> Type
State  y r = DepLens () (\_ => ()) y r

scalarToState : {y : Type} -> {r : y -> Type} -> y -> State y r
scalarToState x = MkDepLens (const x) (\_ => const ())


public export
CoState : (x : Type) -> (s : x -> Type) -> Type
CoState x s = DepLens x s () (\_ => ())

public export
funToCostate : {x : Type} -> {s : x -> Type} -> ((x' : x) -> s x') -> CoState x s
funToCostate f = MkDepLens (const ()) (\x => const (f x))


record Context (x : Type) (s : x -> Type) 
               (y : Type) (r : y -> Type)
    where
    constructor MkContext
    state : State x s
    costate : CoState y r



public export
Arena : ?
Arena = DParaLens

Player : {states : Type} -> {copayoffs : states -> Type} -> (profiles : Type)  -> (actions : states -> Type) -> (utility : (s : states) -> actions s -> Type) -> Type
Player {states} {copayoffs} profiles actions utility = DParaLens states copayoffs (const profiles) (\pr, x => profiles -> Bool) (s : states ** actions s) (\sa => utility sa.fst sa.snd)

ArgmaxPlayer : (Listable actions) => (Ord utility) => Player {states} {copayoffs} actions (\_ => actions) (\_, _ =>  utility)
ArgmaxPlayer {states} {copayoffs = c1} = MkDPLens
                (\x, p => (x **p))
                (\x, p, ry => (?some, ?argmax))

infixl 5 >>>
(>>>) : (l1 : DParaLens x s p q y r) -> DParaLens y r p' q' z t -> DParaLens x s (\x => (p1 : p x ** p' (l1 .play x p1))) (\x, pp => (q x (fst pp), q' (l1 .play x (fst pp)) (snd pp))) z t
(>>>) = comp

ParaMorfism : {x : Type} ->
              (p  : x -> Type) -> (q  : (x' : x) -> p  x' -> Type) ->
              (p' : x -> Type) -> (q' : (x' : x) -> p' x' -> Type) ->
              Type
ParaMorfism p' q' p q = (x0 : x) -> DepLens (p' x0) (\v => q' x0 v) (p x0) (\v => q x0 v)

rep2 : ParaMorfism p' q' p q ->
       DParaLens x s p q y r ->
       DParaLens x s p' q' y r
rep2 pm (MkDPLens play coplay) =
  MkDPLens
    (\x, px' => play x ((pm x).play px' () ))        
    (\x, px', rv =>
        let (s, q) = coplay x ((pm x).play px' ()) rv 
            (q', _) = (pm x).coplay px' () q
            in (s, q')
    )

Player2 : {x : Type} -> (profiles : Type) -> (actions : x -> Type) -> (utility : (s : x) -> (actions s) -> Type) -> Type
Player2 profiles actions utility = ParaMorfism (const profiles) (\x, p => profiles -> Bool) actions (\x, p => actions x -> utility x p)

ArgmaxPlayer2 : (Listable actions) => (Ord utility) => Player2 actions (\_ => actions) (\_, _=> utility)
ArgmaxPlayer2 _ = MkDepLens
                id
                (\_, ry => argmax ry)

pararunitor : ParaMorfism p' q' (\x1 => (p1 : p' x1 ** ())) (\x1, p1 => (q' x1 (p1.fst), ()))
pararunitor x = MkDepLens
                (\p => (p ** ()))
                (\_ => fst)


paralunitor : ParaMorfism p' q' (\x' => ((p1 : () ** p' x'))) (\x', p' => ((), q' x' (snd p')))
paralunitor x = MkDepLens
                (\p => (() ** p))
                (\_ => snd)

paraRDiff : DParaLens () (const ()) p q () (const ()) ->
            DParaLens () (const ()) p (\x1, p1 => (p2 : p x1) -> q x1 p2) () (const ())
paraRDiff (MkDPLens play coplay) =
  MkDPLens
    play
    (\x1, p1, ry => let (s, q) = coplay x1 p1 ry in (s, \p' => snd (coplay x1 p' ry)))

equilibrium : {profiles : Type} -> (Listable profiles) =>
              Arena x s actions utility y r
           -> Player2 profiles actions utility
           -> Context x s y r
           -> List profiles
equilibrium arena player (MkContext state costate) =
  let
    -- 1 pack2: x → ()
    pack2 = rep2 (pararunitor {p' = actions} {q' = utility})
                 (arena >>> costate)

    -- 2 pack1: () → ()
    pack1 = rep2 (paralunitor
                    {p' = \u => actions (state .play u ?someth)}
                    {q' = \u, act => utility (state .play u ?ppp) act})
                 (state >>> arena)

    -- 3 diff: State profiles (const ()) → modifica payoffs
    diff  = paraRDiff (?fix pack1)

    -- 4 test: State profiles (const Bool)
    test  = rep2 player (?magic diff)
  in
    fixpoints (paraStateToFun (?truetest))


public export
data MovesPD = C | D

Listable MovesPD where
  allValues = [C, D]

Show MovesPD where
  show C = "C"
  show D = "D"

payoffPD : (MovesPD, MovesPD) -> (Int, Int)
payoffPD (C, C) = (1, 1)
payoffPD (C, D) = (5, 0)
payoffPD (D, C) = (0, 5)
payoffPD (D, D) = (3, 3)

contextPD : Context () (const ()) (MovesPD, MovesPD) (const (Int, Int))
contextPD = MkContext (scalarToState ()) (funToCostate payoffPD)


public export
corner : DParaLens () (const ()) p q (p ()) (q ())
corner = MkDPLens (\(), p => p) (\(), p, r => ((), r))


ArenaPD : Arena () (const ()) (\_ => (MovesPD, MovesPD)) (\_, _=> (Int, Int)) (MovesPD, MovesPD) (\_ => (Int, Int))
ArenaPD = corner

equiPD : List (MovesPD, MovesPD)
equiPD = equilibrium ArenaPD ArgmaxPlayer2 contextPD


