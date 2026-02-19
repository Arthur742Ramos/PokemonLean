import PokemonLean.Semantics
import PokemonLean.Probability

namespace PokemonLean.StochasticSemantics

open PokemonLean

abbrev Action := PokemonLean.Semantics.Action
abbrev Dist := Probability.Dist
abbrev Rat := Probability.Rat
abbrev ValidState := PokemonLean.Semantics.ValidState
abbrev totalCards := totalCardCount

def getActiveAttack? (gs : GameState) (attackIndex : Nat) : Option Attack :=
  let attacker := getPlayerState gs gs.activePlayer
  match attacker.active with
  | none => none
  | some active => listGet? active.card.attacks attackIndex

def coinFlipBonus? (gs : GameState) (action : Action) : Option Nat :=
  match action with
  | .attack attackIndex =>
      match getActiveAttack? gs attackIndex with
      | some attack =>
          if attack.name = "Triple Coins" ∨ attack.name = "Fury Swipes" then some 30 else none
      | none => none
  | _ => none

def runStep (gs : GameState) (action : Action) : GameState :=
  match PokemonLean.Semantics.step gs action with
  | .ok gs' => gs'
  | .error _ => gs

def applyCoinFlipBonus (gs : GameState) (bonusDamage : Nat) : GameState :=
  let player := gs.activePlayer
  let playerState := getPlayerState gs player
  match playerState.active with
  | none => gs
  | some active =>
      let updatedActive := applyDamage active bonusDamage
      setPlayerState gs player { playerState with active := some updatedActive }

def stepProb (gs : GameState) (action : Action) : Dist GameState :=
  match coinFlipBonus? gs action with
  | none =>
      Probability.Dist.pure (runStep gs action)
  | some bonusDamage =>
      let baseState := runStep gs action
      { outcomes :=
          [ (baseState, (1 : Rat) / (2 : Rat))
          , (applyCoinFlipBonus baseState bonusDamage, (1 : Rat) / (2 : Rat))
          ] }

def stepManyProb (gs : GameState) (actions : List Action) : Dist GameState :=
  actions.foldlM (fun st action => stepProb st action) gs

theorem runStep_preserves_totalCards (gs : GameState) (action : Action) :
    totalCards (runStep gs action) = totalCards gs := by
  unfold runStep totalCards
  cases hStep : PokemonLean.Semantics.step gs action with
  | error err =>
      simp [hStep]
  | ok gs' =>
      simpa [hStep] using PokemonLean.Semantics.step_preserves_total_cards gs action gs' hStep

theorem applyCoinFlipBonus_preserves_totalCards (gs : GameState) (bonusDamage : Nat) :
    totalCards (applyCoinFlipBonus gs bonusDamage) = totalCards gs := by
  unfold applyCoinFlipBonus totalCards
  cases hPlayer : gs.activePlayer <;> simp [getPlayerState, setPlayerState, hPlayer, playerCardCount, totalCardCount]
  · cases hActive : gs.playerOne.active <;> simp [hActive, playerCardCount, bench_card_count]
  · cases hActive : gs.playerTwo.active <;> simp [hActive, playerCardCount, bench_card_count]

theorem runStep_preserves_hasWon (gs : GameState) (action : Action) (player : PlayerId) :
    hasWon gs player → hasWon (runStep gs action) player := by
  intro hWon
  unfold runStep
  cases hStep : PokemonLean.Semantics.step gs action with
  | error err =>
      simpa [hStep] using hWon
  | ok gs' =>
      exact PokemonLean.Semantics.step_preserves_hasWon gs action gs' player hStep hWon

theorem applyCoinFlipBonus_preserves_hasWon (gs : GameState) (bonusDamage : Nat) (player : PlayerId) :
    hasWon (applyCoinFlipBonus gs bonusDamage) player ↔ hasWon gs player := by
  unfold applyCoinFlipBonus hasWon
  cases hPlayer : gs.activePlayer <;>
    cases hP1 : gs.playerOne.active <;>
      cases hP2 : gs.playerTwo.active <;>
        cases player <;>
          simp [getPlayerState, setPlayerState, hPlayer, hP1, hP2, otherPlayer]

theorem runStep_preserves_valid (gs : GameState) (action : Action) :
    ValidState gs → ValidState (runStep gs action) := by
  intro hValid
  unfold runStep
  cases hStep : PokemonLean.Semantics.step gs action with
  | error err =>
      simpa [hStep] using hValid
  | ok gs' =>
      exact PokemonLean.Semantics.step_preserves_valid gs action gs' hValid hStep

theorem applyCoinFlipBonus_preserves_valid (gs : GameState) (bonusDamage : Nat) :
    ValidState (applyCoinFlipBonus gs bonusDamage) ↔ ValidState gs := by
  unfold applyCoinFlipBonus
  cases hPlayer : gs.activePlayer <;> simp [PokemonLean.Semantics.ValidState, getPlayerState, setPlayerState, hPlayer]
  · cases hActive : gs.playerOne.active <;>
      simp [PokemonLean.Semantics.ValidState, hActive]
  · cases hActive : gs.playerTwo.active <;>
      simp [PokemonLean.Semantics.ValidState, hActive]

theorem stepProb_card_conservation :
    ∀ gs action gs' p,
      (gs', p) ∈ (stepProb gs action).outcomes →
      totalCards gs' = totalCards gs := by
  intro gs action gs' p hMem
  unfold stepProb at hMem
  cases hCoin : coinFlipBonus? gs action with
  | none =>
      have hMem' : (gs', p) ∈ (Probability.Dist.pure (runStep gs action)).outcomes := by
        simpa [stepProb, hCoin] using hMem
      have hEq : (gs', p) = (runStep gs action, (1 : Rat)) := by
        simpa [Probability.Dist.pure] using hMem'
      cases hEq
      simpa using runStep_preserves_totalCards gs action
  | some bonusDamage =>
      have hCases :
          (gs', p) = (runStep gs action, (1 : Rat) / (2 : Rat)) ∨
            (gs', p) = (applyCoinFlipBonus (runStep gs action) bonusDamage, (1 : Rat) / (2 : Rat)) := by
        simpa [hCoin] using hMem
      rcases hCases with hBase | hBonus
      · cases hBase
        simpa using runStep_preserves_totalCards gs action
      · cases hBonus
        calc
          totalCards (applyCoinFlipBonus (runStep gs action) bonusDamage) =
              totalCards (runStep gs action) := by
                simpa using applyCoinFlipBonus_preserves_totalCards (runStep gs action) bonusDamage
          _ = totalCards gs := runStep_preserves_totalCards gs action

theorem stepProb_win_monotonic :
    ∀ gs action gs' p player,
      (gs', p) ∈ (stepProb gs action).outcomes →
      hasWon gs player →
      hasWon gs' player := by
  intro gs action gs' p player hMem hWon
  unfold stepProb at hMem
  cases hCoin : coinFlipBonus? gs action with
  | none =>
      have hMem' : (gs', p) ∈ (Probability.Dist.pure (runStep gs action)).outcomes := by
        simpa [stepProb, hCoin] using hMem
      have hEq : (gs', p) = (runStep gs action, (1 : Rat)) := by
        simpa [Probability.Dist.pure] using hMem'
      cases hEq
      exact runStep_preserves_hasWon gs action player hWon
  | some bonusDamage =>
      have hCases :
          (gs', p) = (runStep gs action, (1 : Rat) / (2 : Rat)) ∨
            (gs', p) = (applyCoinFlipBonus (runStep gs action) bonusDamage, (1 : Rat) / (2 : Rat)) := by
        simpa [hCoin] using hMem
      rcases hCases with hBase | hBonus
      · cases hBase
        exact runStep_preserves_hasWon gs action player hWon
      · cases hBonus
        have hBaseWon : hasWon (runStep gs action) player :=
          runStep_preserves_hasWon gs action player hWon
        exact (applyCoinFlipBonus_preserves_hasWon (runStep gs action) bonusDamage player).2 hBaseWon

theorem stepProb_valid_preservation :
    ∀ gs action gs' p,
      ValidState gs →
      (gs', p) ∈ (stepProb gs action).outcomes →
      ValidState gs' := by
  intro gs action gs' p hValid hMem
  unfold stepProb at hMem
  cases hCoin : coinFlipBonus? gs action with
  | none =>
      have hMem' : (gs', p) ∈ (Probability.Dist.pure (runStep gs action)).outcomes := by
        simpa [stepProb, hCoin] using hMem
      have hEq : (gs', p) = (runStep gs action, (1 : Rat)) := by
        simpa [Probability.Dist.pure] using hMem'
      cases hEq
      exact runStep_preserves_valid gs action hValid
  | some bonusDamage =>
      have hCases :
          (gs', p) = (runStep gs action, (1 : Rat) / (2 : Rat)) ∨
            (gs', p) = (applyCoinFlipBonus (runStep gs action) bonusDamage, (1 : Rat) / (2 : Rat)) := by
        simpa [hCoin] using hMem
      rcases hCases with hBase | hBonus
      · cases hBase
        exact runStep_preserves_valid gs action hValid
      · cases hBonus
        have hBaseValid : ValidState (runStep gs action) :=
          runStep_preserves_valid gs action hValid
        exact (applyCoinFlipBonus_preserves_valid (runStep gs action) bonusDamage).2 hBaseValid

theorem stepProb_deterministic_embedding (gs : GameState) (action : Action)
    (hNonCoinFlip : coinFlipBonus? gs action = none) :
    stepProb gs action = Probability.Dist.pure (runStep gs action) := by
  simp [stepProb, hNonCoinFlip]

theorem expected_damage_bounds_match_probability :
    ((0 : Rat) ≤ Probability.expectedNat Probability.tripleCoinDamage ∧
      Probability.expectedNat Probability.tripleCoinDamage ≤ (90 : Rat)) ∧
    ((0 : Rat) ≤ Probability.expectedNat Probability.furySwipesDamage ∧
      Probability.expectedNat Probability.furySwipesDamage ≤ (30 : Rat)) := by
  exact ⟨Probability.tripleCoin_expectedBounds, Probability.furySwipes_expectedBounds⟩

end PokemonLean.StochasticSemantics
