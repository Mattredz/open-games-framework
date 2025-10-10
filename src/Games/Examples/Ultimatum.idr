module Games.Examples.Ultimatum

import Games.Definition
import Games.Context
import Games.Equilibria
import Games.Arena
import Players.Definition
import Players.Argmax
import Interfaces.Listable
import Optics.Lens
import Games.State
import Games.CoState

public export
data MovesUltimatum = Accept | Reject

Listable MovesUltimatum where
  allValues = [Accept, Reject]




fairUltimatum : MovesUltimatum -> (Int, Int)
fairUltimatum Accept = (5, 5)
fairUltimatum Reject = (0, 0)


unfairUltimatum : MovesUltimatum -> (Int, Int)
unfairUltimatum Accept = (8, 2)
unfairUltimatum Reject = (0, 0)

ultArena : Arena  (MkCo MovesUltimatum (\_ => (Int, Int))) 
                (MkParaCont (\p => ()) (\_ => const ())) 
                (MkCo MovesUltimatum (\_ => (Int, Int)))
ultArena = corner

choicheArena :
  Arena
    (MkCo (Either MovesUltimatum MovesUltimatum)
          (SEither (const (Int, Int)) (const (Int, Int))))
    (MkParaCont (SEither (const ()) (const ()))
                ?)
    (MkCo (Either MovesUltimatum MovesUltimatum)
          (SEither (const (Int, Int)) (const (Int, Int))))
choicheArena = ultArena +++ ultArena



ultPlayer :
  Player
    MovesUltimatum
    MovesUltimatum
    (const Int)
ultPlayer = argmaxPlayer 


Game :
  Game
    (Either MovesUltimatum MovesUltimatum)
    (Either MovesUltimatum MovesUltimatum) 
    (Int, Int)
    ?
    (MkCo (Either MovesUltimatum MovesUltimatum) (SEither (const (Int, Int)) (const (Int, Int))))
Game = MkGame ultPlayer choicheArena
