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
         (actions : Type) ->
         (utility : Type) ->
         Type
Player profiles a u = 
    DLens (profiles ** const (profiles -> Bool)) 
          (a ** const (a -> u))

||| Game arena: an alias for ParaDLens representing game structure
public export
Arena : (p : Type) -> (q : Type) ->
        (xs : (X : Type ** X -> Type)) ->
        (yr : (Y : Type ** Y -> Type)) ->
        Type
Arena = ParaDLens

infixl 8 $$
||| Nash equilibrium composition
|||
||| Combines two players into a single player representing their
||| simultaneous interaction in a Nash equilibrium.
|||
||| @ p1 The first player
||| @ p2 The second player
public export
($$) : Player p a u ->
       Player p' a' u' ->
       Player (p, p') (a, a') (u, u')
($$) (MkParaLens play1 coplay1) (MkParaLens play2 coplay2) =
  MkDLens 
    (\pp => (play1 () (fst pp), play2 () (snd pp)))
    (\pp, payoffs => 
        let pay1 = \a1 : a => fst $ payoffs (a1, play2 () (snd pp))
            pay2 = \a2 : a' => snd $ payoffs (play1 () (fst pp), a2)
            (s1, _) = coplay1 () (fst pp) pay1
            (s2, _) = coplay2 () (snd pp) pay2
        in \(p1, p2) => s1 p1 && s2 p2)


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
Equilibrium : {p : Type} -> (Listable p) =>
              ParaDLens a u xs yr ->
              Player p a u ->
              State xs ->
              CoState yr ->
              List p
Equilibrium game player h k  =
  let K = h |>> game <<| k
      D = Dlunitor |>> (ParaRDiff K) <<| Drunitor
      R = reparam D player
      f = ParaStateToFun R
  in fixpoints f
