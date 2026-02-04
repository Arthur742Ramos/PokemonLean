import PokemonLean.Basic

namespace PokemonLean.Abilities

open PokemonLean

inductive AbilityType
  | ability
  | power
  deriving Repr, BEq, DecidableEq

structure Ability where
  name : String
  abilityType : AbilityType
  energyCost : List EnergyType := []
  effect : Effect
  deriving Repr, BEq, DecidableEq

structure AbilityState where
  ability : Ability
  usedThisTurn : Bool := false
  deriving Repr, BEq, DecidableEq

def canPayAbilityCost (ability : Ability) (pokemon : PokemonInPlay) : Prop :=
  hasEnergyCost { name := ability.name, baseDamage := 0, effects := [], energyCost := ability.energyCost } pokemon.energy = true

def payAbilityCost (ability : Ability) (pokemon : PokemonInPlay) : Option PokemonInPlay :=
  match consumeEnergyCost ability.energyCost pokemon.energy with
  | none => none
  | some remaining => some { pokemon with energy := remaining }

theorem payAbilityCost_sound (ability : Ability) (pokemon paid : PokemonInPlay)
    (h : payAbilityCost ability pokemon = some paid) :
    canPayAbilityCost ability pokemon := by
  unfold payAbilityCost at h
  cases hConsume : consumeEnergyCost ability.energyCost pokemon.energy with
  | none =>
    simp [hConsume] at h
  | some remaining =>
    simp [hConsume] at h
    cases h
    unfold canPayAbilityCost
    simpa [hasEnergyCost] using
      (consumeEnergyCost_sound ability.energyCost pokemon.energy remaining hConsume)

theorem payAbilityCost_energy_length (ability : Ability) (pokemon paid : PokemonInPlay)
    (h : payAbilityCost ability pokemon = some paid) :
    paid.energy.length + ability.energyCost.length = pokemon.energy.length := by
  -- expose `energyCost` as an explicit list so we can induct on it
  cases ability with
  | mk name abilityType energyCost effect =>
      unfold payAbilityCost at h
      cases hConsume : consumeEnergyCost energyCost pokemon.energy with
      | none =>
          simp [hConsume] at h
      | some remaining =>
          simp [hConsume] at h
          cases h
          -- goal is now: `remaining.length + energyCost.length = pokemon.energy.length`
          induction energyCost generalizing pokemon remaining with
          | nil =>
              simp [consumeEnergyCost] at hConsume
              cases hConsume
              simp
          | cons req rest ih =>
              simp [consumeEnergyCost] at hConsume
              cases hRem : removeFirstEnergy req pokemon.energy with
              | none =>
                  simp [hRem] at hConsume
              | some remaining' =>
                  simp [hRem] at hConsume
                  have hRec :=
                    ih (pokemon := { pokemon with energy := remaining' }) (remaining := remaining) hConsume
                  have hLen := removeFirstEnergy_length req pokemon.energy remaining' hRem
                  -- `hRec : remaining.length + rest.length = remaining'.length`
                  calc
                    remaining.length + (req :: rest).length
                        = remaining.length + (rest.length + 1) := by simp
                    _ = (remaining.length + rest.length) + 1 := by
                        simp [Nat.add_assoc]
                    _ = remaining'.length + 1 := by simp [hRec]
                    _ = pokemon.energy.length := by simp [hLen]

def applyAbilityEffect (state : GameState) (ability : Ability) : GameState :=
  match ability.effect with
  | .applyStatus condition =>
      let player := state.activePlayer
      let playerState := getPlayerState state player
      match playerState.active with
      | none => state
      | some active =>
          let updatedActive := { active with status := some condition }
          setPlayerState state player { playerState with active := some updatedActive }
  | .heal amount =>
      let player := state.activePlayer
      let playerState := getPlayerState state player
      match playerState.active with
      | none => state
      | some active =>
          let updatedActive := { active with damage := Nat.sub active.damage amount }
          setPlayerState state player { playerState with active := some updatedActive }
  | .addDamage amount =>
      let opponent := otherPlayer state.activePlayer
      let oppState := getPlayerState state opponent
      match oppState.active with
      | none => state
      | some active =>
          let updatedActive := applyDamage active amount
          setPlayerState state opponent { oppState with active := some updatedActive }

theorem applyAbilityEffect_preserves_prizes (state : GameState) (ability : Ability) :
    (applyAbilityEffect state ability).playerOne.prizes = state.playerOne.prizes ∧
      (applyAbilityEffect state ability).playerTwo.prizes = state.playerTwo.prizes := by
  cases ability with
  | mk name abilityType energyCost effect =>
    cases effect with
    | applyStatus condition =>
      cases hPlayer : state.activePlayer with
      | playerOne =>
        cases hAct : state.playerOne.active <;>
          simp [applyAbilityEffect, getPlayerState, setPlayerState, hPlayer, hAct]
      | playerTwo =>
        cases hAct : state.playerTwo.active <;>
          simp [applyAbilityEffect, getPlayerState, setPlayerState, hPlayer, hAct]
    | heal amount =>
      cases hPlayer : state.activePlayer with
      | playerOne =>
        cases hAct : state.playerOne.active <;>
          simp [applyAbilityEffect, getPlayerState, setPlayerState, hPlayer, hAct]
      | playerTwo =>
        cases hAct : state.playerTwo.active <;>
          simp [applyAbilityEffect, getPlayerState, setPlayerState, hPlayer, hAct]
    | addDamage amount =>
      cases hPlayer : state.activePlayer with
      | playerOne =>
        -- opponent is playerTwo
        cases hAct : state.playerTwo.active <;>
          simp [applyAbilityEffect, getPlayerState, setPlayerState, otherPlayer, hPlayer, hAct]
      | playerTwo =>
        -- opponent is playerOne
        cases hAct : state.playerOne.active <;>
          simp [applyAbilityEffect, getPlayerState, setPlayerState, otherPlayer, hPlayer, hAct]

theorem applyAbilityEffect_preserves_totalCardCount (state : GameState) (ability : Ability) :
    totalCardCount (applyAbilityEffect state ability) = totalCardCount state := by
  cases ability with
  | mk name abilityType energyCost effect =>
    cases effect with
    | applyStatus condition =>
      cases hPlayer : state.activePlayer with
       | playerOne =>
         cases hAct : state.playerOne.active <;>
           simp [applyAbilityEffect, getPlayerState, setPlayerState,
             totalCardCount, playerCardCount, bench_card_count, hPlayer, hAct]
       | playerTwo =>
         cases hAct : state.playerTwo.active <;>
           simp [applyAbilityEffect, getPlayerState, setPlayerState,
             totalCardCount, playerCardCount, bench_card_count, hPlayer, hAct]
    | heal amount =>
       cases hPlayer : state.activePlayer with
       | playerOne =>
         cases hAct : state.playerOne.active <;>
           simp [applyAbilityEffect, getPlayerState, setPlayerState,
             totalCardCount, playerCardCount, bench_card_count, hPlayer, hAct]
       | playerTwo =>
         cases hAct : state.playerTwo.active <;>
           simp [applyAbilityEffect, getPlayerState, setPlayerState,
             totalCardCount, playerCardCount, bench_card_count, hPlayer, hAct]
    | addDamage amount =>
       cases hPlayer : state.activePlayer with
       | playerOne =>
         cases hAct : state.playerTwo.active <;>
           simp [applyAbilityEffect, getPlayerState, setPlayerState, otherPlayer,
             totalCardCount, playerCardCount, bench_card_count, hPlayer, hAct]
       | playerTwo =>
         cases hAct : state.playerOne.active <;>
           simp [applyAbilityEffect, getPlayerState, setPlayerState, otherPlayer,
             totalCardCount, playerCardCount, bench_card_count, hPlayer, hAct]

def applyAbility (state : GameState) (abilityState : AbilityState) : Option (GameState × AbilityState) :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  match playerState.active with
  | none => none
  | some active =>
      if abilityState.usedThisTurn then
        none
      else
        match payAbilityCost abilityState.ability active with
        | none => none
        | some paid =>
            let updatedActive := { paid with card := active.card, damage := active.damage, status := active.status }
            let updatedPlayerState := { playerState with active := some updatedActive }
            let updatedState := setPlayerState state player updatedPlayerState
            some (applyAbilityEffect updatedState abilityState.ability,
              { abilityState with usedThisTurn := true })

def canUseAbility (state : GameState) (abilityState : AbilityState) : Prop :=
  let playerState := getPlayerState state state.activePlayer
  ∃ active,
    playerState.active = some active ∧
    abilityState.usedThisTurn = false ∧
    canPayAbilityCost abilityState.ability active

theorem applyAbility_used (state : GameState) (abilityState abilityState' : AbilityState) (state' : GameState)
    (h : applyAbility state abilityState = some (state', abilityState')) :
    abilityState'.usedThisTurn = true := by
  unfold applyAbility at h
  cases hActive : (getPlayerState state state.activePlayer).active <;> simp [hActive] at h
  rename_i active
  cases hUsed : abilityState.usedThisTurn <;> simp [hUsed] at h
  cases hPay : payAbilityCost abilityState.ability active <;> simp [hPay] at h
  rcases h with ⟨_hState, hAbility⟩
  cases hAbility
  simp

theorem applyAbility_preserves_prizes (state : GameState) (abilityState : AbilityState)
    (result : GameState × AbilityState)
    (h : applyAbility state abilityState = some result) :
    result.1.playerOne.prizes = state.playerOne.prizes ∧
      result.1.playerTwo.prizes = state.playerTwo.prizes := by
  unfold applyAbility at h
  cases hAct : (getPlayerState state state.activePlayer).active <;> simp [hAct] at h
  rename_i active
  cases hUsed : abilityState.usedThisTurn <;> simp [hUsed] at h
  cases hPay : payAbilityCost abilityState.ability active <;> simp [hPay] at h
  rename_i paid
  cases h

  let updatedState : GameState :=
    setPlayerState state state.activePlayer
      { (getPlayerState state state.activePlayer) with
        active := some { paid with card := active.card, damage := active.damage, status := active.status } }

  have hUpd : updatedState.playerOne.prizes = state.playerOne.prizes ∧
      updatedState.playerTwo.prizes = state.playerTwo.prizes := by
    cases hPlayer : state.activePlayer <;>
      simp [updatedState, getPlayerState, setPlayerState, hPlayer]

  have hEff := applyAbilityEffect_preserves_prizes (state := updatedState) (ability := abilityState.ability)

  refine ⟨?_, ?_⟩
  · -- playerOne prizes
    calc
      (applyAbilityEffect updatedState abilityState.ability).playerOne.prizes
          = updatedState.playerOne.prizes := hEff.1
      _ = state.playerOne.prizes := hUpd.1
  · -- playerTwo prizes
    calc
      (applyAbilityEffect updatedState abilityState.ability).playerTwo.prizes
          = updatedState.playerTwo.prizes := hEff.2
      _ = state.playerTwo.prizes := hUpd.2

theorem applyAbility_preserves_total_cards (state : GameState) (abilityState : AbilityState)
    (result : GameState × AbilityState)
    (h : applyAbility state abilityState = some result) :
    totalCardCount result.1 = totalCardCount state := by
  unfold applyAbility at h
  cases hAct : (getPlayerState state state.activePlayer).active <;> simp [hAct] at h
  rename_i active
  cases hUsed : abilityState.usedThisTurn <;> simp [hUsed] at h
  cases hPay : payAbilityCost abilityState.ability active <;> simp [hPay] at h
  rename_i paid
  cases h

  let updatedState : GameState :=
    setPlayerState state state.activePlayer
      { (getPlayerState state state.activePlayer) with
        active := some { paid with card := active.card, damage := active.damage, status := active.status } }

  have hUpd : totalCardCount updatedState = totalCardCount state := by
    cases hPlayer : state.activePlayer with
    | playerOne =>
      have hAct' : state.playerOne.active = some active := by
        simpa [getPlayerState, hPlayer] using hAct
      simp [updatedState, getPlayerState, setPlayerState, totalCardCount, playerCardCount, bench_card_count,
        hPlayer, hAct']
    | playerTwo =>
      have hAct' : state.playerTwo.active = some active := by
        simpa [getPlayerState, hPlayer] using hAct
      simp [updatedState, getPlayerState, setPlayerState, totalCardCount, playerCardCount, bench_card_count,
        hPlayer, hAct']

  have hEff := applyAbilityEffect_preserves_totalCardCount (state := updatedState) (ability := abilityState.ability)

  -- `applyAbilityEffect` preserves totalCardCount, and `updatedState` only changes the active pokemon's fields.
  simpa [updatedState] using (hEff.trans hUpd)

theorem canUseAbility_of_apply (state : GameState) (abilityState : AbilityState)
    (result : GameState × AbilityState)
    (h : applyAbility state abilityState = some result) :
    canUseAbility state abilityState := by
  unfold applyAbility at h
  cases hAct : (getPlayerState state state.activePlayer).active <;> simp [hAct] at h
  rename_i active
  cases hUsed : abilityState.usedThisTurn <;> simp [hUsed] at h
  cases hPay : payAbilityCost abilityState.ability active <;> simp [hPay] at h
  -- successful branch: provide the witnessed `active`
  refine ⟨active, hAct, ?_, ?_⟩
  · simpa using hUsed
  · exact payAbilityCost_sound abilityState.ability active _ hPay

def resetAbility (abilityState : AbilityState) : AbilityState :=
  { abilityState with usedThisTurn := false }

theorem resetAbility_unused (abilityState : AbilityState) :
    (resetAbility abilityState).usedThisTurn = false := by
  rfl

end PokemonLean.Abilities
