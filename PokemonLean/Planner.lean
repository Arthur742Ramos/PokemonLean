import PokemonLean.Basic

namespace PokemonLean.Planner

open PokemonLean

def planOneTurn (_state : GameState) : Option (List Action) :=
  some [Action.endTurn]

theorem planOneTurn_turnOneActions (state : GameState) (actions : List Action)
    (hPlan : planOneTurn state = some actions) :
    TurnOneActions actions := by
  cases hPlan
  exact TurnOneActions.endTurn

end PokemonLean.Planner
