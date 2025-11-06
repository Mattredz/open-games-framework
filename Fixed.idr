module Optics.Fixed

import Interfaces.Listable
import Data.Fin

-- Basic dependent types
DUnit : (X : Type ** X -> Type)
DUnit = (() ** const ())

DProd : (x : Type ** (x -> Type)) ->
        (y : Type ** (y -> Type)) ->
        (xy : Type ** (xy -> Type))
DProd xs ys =
    ((xs.fst, ys.fst) ** (\xy => (xs.snd (fst xy), ys.snd (snd xy))))

-- FIXED: Internal fibration ParaDLens
-- The key insight: the fibration is now INSIDE the dependent pair
record ParaDLens (pq : (P : Type ** P -> Type))
                 (xs : (X : Type ** X -> Type)) 
                 (yr : (Y : Type ** Y -> Type)) where
    constructor MkParaLens
    play : pq.fst -> (x : xs.fst) -> yr.fst
    coplay : (p : pq.fst) -> (x : xs.fst) -> yr.snd (play p x) -> (xs.snd x, pq.snd p)

DLens : (X : Type ** X -> Type) ->
        (Y : Type ** Y -> Type) ->
        Type
DLens xs yr = ParaDLens DUnit xs yr

-- Helper for non-parametrized lenses
MkDLens : (play : xs.fst -> yr.fst) ->
          (coplay : (x1 : xs.fst) -> yr.snd (play x1) -> xs.snd x1) ->
          DLens xs yr
MkDLens play coplay =
    MkParaLens
    (const play)
    (\_, x, ry => (coplay x ry, ()))

-- SEither for dependent sums
public export
SEither : (a -> Type) -> (b -> Type) ->
          Either a b -> Type
SEither fa fb e = case e of
    Left  x => fa x
    Right y => fb y

DEither : (xs : (X : Type ** X -> Type)) ->
          (xs' : (Y : Type ** Y -> Type)) ->
          (E : Type ** E -> Type)
DEither xs xs' =
    (Either xs.fst xs'.fst ** SEither xs.snd xs'.snd)


-- QEither for dependent coproduct parameters  
QEither : {X, Y : Type} ->
          {P : X -> Type} ->
          {P' : Y -> Type} ->
          (q : (x : X) -> P x -> Type) ->
          (q' : (x : Y) -> P' x -> Type) ->
          ((e : Either X Y) -> SEither P P' e -> Type)
QEither q q' = \case 
    Left  x => q x
    Right x => q' x


-- Coproduct operator
infixr 10 +++
(+++) : ParaDLens pq xs yr ->
        ParaDLens pq' xs' yr' ->
        ParaDLens ((pq.fst, pq'.fst) ** \pp => (Either (pq.snd (fst pp)) (pq'.snd (snd pp)))) (DEither xs xs') (DEither yr yr')
(+++) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens
    (\(p, p'), e => case e of
                 Left  x  => Left  (play1 p x)
                 Right x' => Right (play2 p' x'))
    (\(p, p'), e, zt => case e of
                     Left x  => let (s, q) = coplay1 p x zt in (s, Left q)
                     Right x' => let (s, q) = coplay2 p' x' zt in (s, Right q))


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

CoUnitor : DLens (Either () () ** SEither (const ()) (const ())) DUnit
CoUnitor = MkDLens
    (const ())
    (\case Left  () => const ()
           Right () => const ())

ParaCoUnitor : DLens DUnit (((), ()) ** const (Either () ()))
ParaCoUnitor = MkDLens
    (\_ => ((), ()))
    (\_, _ => ())

-- Sequential composition
infixr 9 >>>
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



infixl 9 |>>
(|>>) : (l1 : DLens xs yr) -> ParaDLens pq yr zt -> ParaDLens pq xs zt
(|>>) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens
    (\p, x => play2 p (play1 () x))
    (\p, x, tz =>
        let (r, q2) = coplay2 p (play1 () x) tz
            (s, _)  = coplay1 () x r
        in (s, q2))


infixl 9 <<|
(<<|) : ParaDLens xs pq yr -> DLens yr zt -> ParaDLens xs pq zt 
(<<|) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens
    (\p, x => play2 () (play1 p x))
    (\p, x, tz =>
        let (r, _)  = coplay2 () (play1 p x) tz
            (s, q1) = coplay1 p x r
        in (s, q1))
 
infixr 10 ***
(***) : ParaDLens pq xs yr ->
        ParaDLens pq' xs' yr' ->
        ParaDLens (DProd pq pq') (DProd xs xs') (DProd yr yr')
(***) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
    MkParaLens 
    (\(p, p'), (x, x') => (play1 p x, play2 p' x'))
    (\(p, p'), (x, x'), (ry, ry') =>
        let (s1, q1) = coplay1 p x ry
            (s2, q2) = coplay2 p' x' ry'
        in ((s1, s2), (q1, q2)))

ProdUnitor : DLens (DProd DUnit DUnit) DUnit
ProdUnitor = MkDLens
    (\_ => ())
    (\_, _ => ((), ()))

-- States and CoStates
State : (X : Type ** X -> Type) -> Type
State xs = DLens DUnit xs

scalarToState : {x : Type} -> {s : x -> Type} -> x -> State (x ** s)
scalarToState x0 = MkDLens (const x0) (\_, _ => ())

CoState : (Y : Type ** Y -> Type) -> Type
CoState yr = DLens yr DUnit

FunToCoState : {x : Type} -> {s : x -> Type} -> 
               ((x' : x) -> s x') -> CoState (x ** s)
FunToCoState f = MkDLens (const ()) (\x, _ => f x)

CoStateToFun : CoState (y ** r) -> ((a : y) -> r a)
CoStateToFun (MkParaLens _ bwd) y0 = fst (bwd () y0 ())

public export
ParaStateToFun : ParaDLens pq DUnit DUnit -> ((p : pq.fst) -> pq.snd p)
ParaStateToFun (MkParaLens _ bwd) p0 = snd (bwd p0 () ())

-- Utilities
public export
maximum : Ord a => a -> List a -> a
maximum = foldl max

public export
argmax : (Listable x, Ord a, Eq a) => (x -> a) -> (x -> Bool)
argmax f x =
  case allValues of
    []        => True
    (h :: hs) => f x == maximum (f h) (map f hs)

-- Players and Nash
Player : (profiles : Type) ->
         (actions : Type) ->
         (utility : actions -> Type) ->
         Type
Player profiles a u = DLens (profiles ** const (profiles -> Bool)) (a ** const ((a1 : a) -> u a1))

Nash : Player p a u ->
       Player p' a' u' ->
       Player (p, p') (a, a') (\aa => (u (fst aa), u' (snd aa)))
Nash (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
  MkDLens 
    (\pp => (play1 () (fst pp), play2 () (snd pp)))
    (\pp, payoffs => 
        let pay1 = \a1 : a => fst $ payoffs (a1, play2 () (snd pp))
            pay2 = \a2 : a' => snd $ payoffs (play1 () (fst pp), a2)
            (s1, _) = coplay1 () (fst pp) pay1
            (s2, _) = coplay2 () (snd pp) pay2
        in \(p1, p2) => s1 p1 && s2 p2)

ParaRDiff : ParaDLens pq xs yr ->
            ParaDLens (pq.fst ** const ((p : pq.fst) -> pq.snd p)) 
                      (xs.fst ** const ((x : xs.fst) -> xs.snd x)) 
                      (yr.fst ** const ((y : yr.fst) -> yr.snd y))
ParaRDiff (MkParaLens play1 coplay1) =
  MkParaLens
    play1
    (\p, x, ry =>
      let s = \x => fst $ coplay1 p x (ry $ play1 p x)
          g = \p => snd $ coplay1 p x (ry $ play1 p x)
      in (s, g)
    )

Drunitor : DLens (() ** const (() -> ())) DUnit
Drunitor = MkDLens (\_ => ()) (\_, _ => const ())

Dlunitor : DLens DUnit (() ** const (() -> ()))
Dlunitor = MkDLens (\_ => ()) (\_, _ => ())

reparam : ParaDLens au xs yr ->
       DLens pq au ->
       ParaDLens pq xs yr
reparam (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
  MkParaLens
    (\p, x => play1 (play2 () p) x)
    (\p, x, ry =>
        let (s, u)  = coplay1 (play2 () p) x ry
            (q, _) = coplay2 () p u
        in (s, q)
    )



Argmax : (Listable a, Ord u, Eq u) => Player a a (const u)
Argmax = MkDLens id (\a, k => argmax k)

-- FIXED: Corner with internal fibration
corner : ParaDLens pq DUnit pq
corner = MkParaLens
    (\p, _ => p)
    (\p, _, ry => ((), ry))


DLensProd : DLens xs yr ->
            DLens xs' yr' ->
            DLens (DProd xs xs') (DProd yr yr')
DLensProd (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
  MkDLens
  (\(x, x') => (play1 () x, play2 () x'))
  (\(x, x'), (ry, ry') =>
      let (s1, _) = coplay1 () x ry
          (s2, _) = coplay2 () x' ry'
      in (s1, s2)
  )

idLens : DLens xs xs
idLens = MkDLens id (\x, ry => ry)

-- Equilibrium computation
Equilibrium : {p : Type} -> (Listable p) =>
              ParaDLens au xs yr ->
              Player p au.fst au.snd ->
              State xs ->
              CoState yr ->
              List p
Equilibrium game player h k  =
  let K = h |>> game <<| k
      D = Dlunitor |>> (ParaRDiff K) <<| Drunitor
      R = reparam D player
      f = ParaStateToFun R
  in fixpoints f


Arena = ParaDLens

-- Prisoner's Dilemma example
data PDAction = C | D

implementation Listable PDAction where
    allValues = [C, D]

PDPayoff : (PDAction, PDAction) -> (Int, Int)
PDPayoff (C, C) = (3, 3)
PDPayoff (C, D) = (0, 5)
PDPayoff (D, C) = (5, 0)
PDPayoff (D, D) = (1, 1)

PDPlayer : Player PDAction PDAction (const Int)
PDPlayer = Argmax

PDNashE : List (PDAction, PDAction)
PDNashE = Equilibrium corner (Nash PDPlayer PDPlayer) (scalarToState ()) (FunToCoState PDPayoff)

Sum : DLens (x ** const Int) (x ** const (Int, Int))
Sum = MkDLens id (\_, (u1, u2) => u1 + u2)

PDHicksE : List (PDAction, PDAction)
PDHicksE = Equilibrium corner Argmax (scalarToState ()) (Sum |>> FunToCoState PDPayoff)

-- Ultimatum Game example

data Offer = Fair | Unfair
implementation Listable Offer where
    allValues = [Fair, Unfair]

data Response = Accept | Reject
implementation Listable Response where
    allValues = [Accept, Reject]

UGPayoff : (Offer, Response) -> (Int, Int)
UGPayoff (Fair, Accept)   = (5, 5)
UGPayoff (Unfair, Accept) = (8, 2)
UGPayoff (_, Reject)      = (0, 0)

OfferArena : Arena (Offer ** const Int) DUnit (Offer ** const Int)
OfferArena = corner

Offerer : Player Offer Offer (const Int)
Offerer = Argmax

ResponseArena : Arena ((Offer -> Response) ** const Int) (Offer ** const Int) ((Offer, Response) ** const (Int, Int))
ResponseArena = MkParaLens
    (\p, o => (o, p o))
    (\_, _, ry => ry)

data RespProfiles = AlwaysAccept | AlwaysReject | RejectUnfair 
implementation Listable RespProfiles where
    allValues = [AlwaysAccept, AlwaysReject, RejectUnfair]



Responder : Player RespProfiles (Offer -> Response) (const Int)
Responder = MkDLens profileToFun (\p, k => argmax (k . profileToFun))
    where
    profileToFun : RespProfiles -> (Offer -> Response)
    profileToFun AlwaysAccept = \_ => Accept
    profileToFun AlwaysReject = \_ => Reject
    profileToFun RejectUnfair = \case
        Fair   => Accept
        Unfair => Reject

UltE : List (Offer, RespProfiles)
UltE = Equilibrium (OfferArena >>> ResponseArena) (Nash Offerer Responder) (scalarToState ()) (FunToCoState UGPayoff)

COffer : Type
COffer = Either () ()

ChoiceOffer : Arena (COffer ** (const Int)) DUnit (COffer ** SEither (const Int) (const Int))
ChoiceOffer = MkParaLens
    (const)
    (\o, _, ry => case o of
                     Left _   => ((), ry)
                     Right _  => ((), ry))

ChoiceResponder : Arena (Response ** const Int) (Unit ** const Int) (Response ** const (Int, Int))
ChoiceResponder = MkParaLens
    (const)
    (\_, _, ry => ry)

FairPayoff : Response -> (Int, Int)
FairPayoff Accept = (5, 5)
FairPayoff Reject = (0, 0)

UnfairPayoff : Response -> (Int, Int)
UnfairPayoff Accept = (8, 2)
UnfairPayoff Reject = (0, 0)


Argmax : (Listable a, Ord u, Eq u) => Player (a, a) (a, a) (const $ Either u u)
Argmax = Argmax
    
ChP : Player COffer COffer (const Int)
ChP = Argmax

ChoiceE : List (COffer, (Response, Response))
ChoiceE = Equilibrium (ChoiceOffer >>> ChoiceResponder +++ ChoiceResponder) (Nash ChP Argmax) (scalarToState ()) (DCoProd (FunToCoState FairPayoff) (FunToCoState UnfairPayoff) <<| CoUnitor)


Inspect : Type
Inspect = ()

NoInspect : Type
NoInspect = ()

IspectorMove : Type
IspectorMove = Either Inspect NoInspect

data IspecteeMove = Comply | Violate
implementation Listable IspecteeMove where
    allValues = [Comply, Violate]


IspectorArena : Arena (IspectorMove ** const Int) DUnit (IspectorMove ** SEither (const Int) (const Int))
IspectorArena = MkParaLens
    (const)
    (\o, _, ry => case o of
                     Left _   => ((), ry)
                     Right _  => ((), ry))

InspectionArena : Arena (IspecteeMove ** const Int) (Inspect ** const Int) (IspecteeMove ** const (Int, Int))
InspectionArena = MkParaLens
    const
    (\_, _, ry => ry)

NoInspectionArena : Arena (IspecteeMove ** const Int) (NoInspect ** const Int) (IspecteeMove ** const (Int, Int))
NoInspectionArena = MkParaLens
    const
    (\_, _, ry => ry)

IspectionPayoff : IspecteeMove -> (Int, Int)
IspectionPayoff Comply  = (2, 2)
IspectionPayoff Violate = (0, -5)

NoInspectionPayoff : IspecteeMove -> (Int, Int)
NoInspectionPayoff Comply  = (5, 1)
NoInspectionPayoff Violate = (-1, 5)

InspectorPlayer : Player IspectorMove IspectorMove (const Int)
InspectorPlayer = Argmax


InspectionE : List (IspectorMove, (IspecteeMove, IspecteeMove))
InspectionE = Equilibrium (IspectorArena >>> InspectionArena +++ NoInspectionArena) (Nash InspectorPlayer Argmax) (scalarToState ()) (DCoProd (FunToCoState IspectionPayoff) (FunToCoState NoInspectionPayoff) <<| CoUnitor)