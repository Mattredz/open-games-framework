||| Core concepts for categorical game theory
|||
||| This module defines the fundamental constructions for representing
||| games, players, and equilibria using dependent lenses.
module GameTheory.Core

import public GameTheory.Combinators
import public Lenses.DTypes
import public Lenses.ParaDLens
import public Lenses.Operators
import public Lenses.States
import public Lenses.Utils
import Interfaces.Listable

%default total

||| A player in a game
|||
||| Represents an agent that observes a profile, takes an action,
||| and evaluates utilities to determine best responses.
|||
||| @ profiles The type of strategy profiles
||| @ actions The type of available actions
||| @ utility The utility function type over actions
public export
Player : (profiles : Type) ->
         (a : Type) -> (a -> Type) ->
         Type
Player profiles a u = 
    DLens (profiles ** \p => Bool) 
          (a ** \_ => (a1 : a) -> u a1)

||| Game arena: an alias for ParaDLens representing game structure
public export
Arena : (pq : (P : Type ** P -> Type)) ->
        (xs : (X : Type ** X -> Type)) ->
        (yr : (Y : Type ** Y -> Type)) ->
        Type
Arena = ParaDLens

public export
AND : DLens ((p, p') ** \pp => Bool) ((p, p') ** \pp => (Bool, Bool))
AND = MkDLens id (\_, (b1, b2) => b1 && b2)


public export
Laxator : {u : a -> Type} -> {u' : a' -> Type} ->
            DLens ((a, a') ** const (((x1 : a) -> u x1), ((x1 : a') -> u' x1))) ((a, a') ** const $ (xx : (a, a')) -> (u $ fst xx, u' $ snd xx))
Laxator = MkDLens id (\(x, x'), f => (\x => fst $ f (x, x'), \x' => snd $ f (x, x')))


infixl 8 $$
||| Nash equilibrium composition
|||
||| Combines two players into a single player representing their
||| interaction in a Nash equilibrium.
|||
||| @ p1 The first player
||| @ p2 The second player
public export
($$) : {u : a -> Type} -> {u' : a' -> Type} ->
       Player p a u ->
       Player p' a' u' ->
       Player (p, p') (a, a') (\aa => (u (fst aa), u' (snd aa)))
($$) p1 p2 = AND |>> p1 *** p2 |>> Laxator


public export
record Game (au : (A : Type ** A -> Type))
            (xs : (X : Type ** X -> Type))
            (yr : (Y : Type ** Y -> Type)) where
    constructor MkGame
    ||| The game arena structure
    arena : Arena  au xs yr
    ||| The initial state of the game
    state : State xs
    ||| The outcome payoff function in form of a costate
    payoff : CoState yr

||| Equilibrium computation
|||
||| Given a game arena, player rationality, initial state, and outcome observation,
||| computes all equilibrium strategy profiles.
|||
||| @ game The game structure
||| @ player The player's decision rule
||| @ h The initial state
||| @ k The outcome observation
public export
Equilibrium : (Listable p) =>
              Game au xs yr ->
              Player p au.fst au.snd ->
              List p
Equilibrium (MkGame game h k) player  =
  let K = h |>> game <<| k
      D = diffLunitor |>> (lift K) <<| diffRunitor
      R = reparam D player
      f = ParaStateToFun R
  in [ p | p <- allValues, f p]
