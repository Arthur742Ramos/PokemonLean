import PokemonLean.Basic

namespace PokemonLean.EnergyAcceleration

open PokemonLean

structure AccelerationState where
  manualAttachUsed : Bool := false
  effectsUsed : Nat := 0
  cardsDrawn : Nat := 0
  deriving Repr, BEq, DecidableEq

def initialAccelerationState : AccelerationState := {}

def markAcceleration (state : AccelerationState) : AccelerationState :=
  { state with effectsUsed := state.effectsUsed + 1 }

def addDraw (state : AccelerationState) (count : Nat) : AccelerationState :=
  { state with cardsDrawn := state.cardsDrawn + count }

def canManualAttach (state : AccelerationState) : Prop :=
  state.manualAttachUsed = false

instance (state : AccelerationState) : Decidable (canManualAttach state) :=
  inferInstanceAs (Decidable (state.manualAttachUsed = false))

def manualAttach (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) : Option (PokemonInPlay × AccelerationState) :=
  if state.manualAttachUsed = false then
    some ({ pokemon with energy := pokemon.energy ++ [energyType] },
      { state with manualAttachUsed := true })
  else
    none

def attachFromZone (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) : Option (List EnergyType × PokemonInPlay) :=
  match removeFirstEnergy energyType source with
  | none => none
  | some source' =>
      some (source', { pokemon with energy := pokemon.energy ++ [energyType] })

def accelerateFromZone (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  match attachFromZone source pokemon energyType with
  | none => none
  | some (source', pokemon') =>
      some (source', pokemon', markAcceleration state)

def accelerateFromHand (hand : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  accelerateFromZone hand pokemon energyType state

def accelerateFromDeck (deck : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  accelerateFromZone deck pokemon energyType state

def accelerateFromDiscard (discard : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  accelerateFromZone discard pokemon energyType state

def welder (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  match removeFirstEnergy .fire hand with
  | none => none
  | some handAfterFirst =>
      match removeFirstEnergy .fire handAfterFirst with
      | none => none
      | some handAfterSecond =>
          some (handAfterSecond,
            { pokemon with energy := pokemon.energy ++ [.fire, .fire] },
            addDraw (markAcceleration state) 3)

def darkPatch (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  accelerateFromDiscard discard pokemon .dark state

def isBasicEnergy : EnergyType → Bool
  | .colorless => false
  | _ => true

def removeFirstBasicEnergy : List EnergyType → Option (EnergyType × List EnergyType)
  | [] => none
  | e :: rest =>
      if isBasicEnergy e then
        some (e, rest)
      else
        match removeFirstBasicEnergy rest with
        | none => none
        | some (found, rest') => some (found, e :: rest')

def maxElixir (deck : List EnergyType) (benched : PokemonInPlay)
    (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  match removeFirstBasicEnergy deck with
  | none => none
  | some (energyType, deck') =>
      some (deck',
        { benched with energy := benched.energy ++ [energyType] },
        markAcceleration state)

def melony (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  match accelerateFromDiscard discard pokemon .water state with
  | none => none
  | some (discard', pokemon', state') =>
      some (discard', pokemon', addDraw state' 3)

def moveEnergy (source target : PokemonInPlay) (energyType : EnergyType) :
    Option (PokemonInPlay × PokemonInPlay) :=
  match removeFirstEnergy energyType source.energy with
  | none => none
  | some sourceEnergy =>
      some ({ source with energy := sourceEnergy },
        { target with energy := target.energy ++ [energyType] })

def arcanineEnergyTrans (source target : PokemonInPlay) :
    Option (PokemonInPlay × PokemonInPlay) :=
  moveEnergy source target .fire

def blastoiseEnergyTrans (source target : PokemonInPlay) :
    Option (PokemonInPlay × PokemonInPlay) :=
  moveEnergy source target .water

def doubleTurboProvided : Nat := 2

def applyDoubleTurboPenalty (baseDamage : Nat) : Nat :=
  baseDamage - 20

def doubleTurboDamage (baseDamage bonusDamage : Nat) : Nat :=
  applyDoubleTurboPenalty (baseDamage + bonusDamage)

def auroraAttach (hand : List EnergyType) (discardCost providedType : EnergyType)
    (pokemon : PokemonInPlay) (state : AccelerationState) :
    Option (List EnergyType × PokemonInPlay × AccelerationState) :=
  match removeFirstEnergy discardCost hand with
  | none => none
  | some hand' =>
      some (hand', { pokemon with energy := pokemon.energy ++ [providedType] }, markAcceleration state)

-- State and helper theorems


theorem markAcceleration_effectsUsed (state : AccelerationState) :
    (markAcceleration state).effectsUsed = state.effectsUsed + 1 := by
  simp [markAcceleration]

theorem markAcceleration_manualAttachUsed (state : AccelerationState) :
    (markAcceleration state).manualAttachUsed = state.manualAttachUsed := by
  simp [markAcceleration]

theorem markAcceleration_cardsDrawn (state : AccelerationState) :
    (markAcceleration state).cardsDrawn = state.cardsDrawn := by
  simp [markAcceleration]

theorem addDraw_cardsDrawn (state : AccelerationState) (count : Nat) :
    (addDraw state count).cardsDrawn = state.cardsDrawn + count := by
  simp [addDraw]

theorem addDraw_manualAttachUsed (state : AccelerationState) (count : Nat) :
    (addDraw state count).manualAttachUsed = state.manualAttachUsed := by
  simp [addDraw]

theorem addDraw_effectsUsed (state : AccelerationState) (count : Nat) :
    (addDraw state count).effectsUsed = state.effectsUsed := by
  simp [addDraw]

-- Manual attach (once per turn)

theorem canManualAttach_initial :
    canManualAttach initialAccelerationState := by
  simp [canManualAttach, initialAccelerationState]

theorem manualAttach_none_when_used (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (hUsed : state.manualAttachUsed = true) :
    manualAttach pokemon energyType state = none := by
  simp [manualAttach, hUsed]

theorem manualAttach_adds_energy (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : manualAttach pokemon energyType state = some (pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [energyType] := by
  unfold manualAttach at h
  split at h
  · simp at h
    obtain ⟨hp, _⟩ := h
    exact hp ▸ rfl
  · simp at h

theorem manualAttach_sets_manual_flag (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : manualAttach pokemon energyType state = some (pokemon', state')) :
    state'.manualAttachUsed = true := by
  unfold manualAttach at h
  split at h
  · simp at h
    obtain ⟨_, hs⟩ := h
    exact hs ▸ rfl
  · simp at h

theorem manualAttach_preserves_effectsUsed (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : manualAttach pokemon energyType state = some (pokemon', state')) :
    state'.effectsUsed = state.effectsUsed := by
  unfold manualAttach at h
  split at h
  · simp at h
    obtain ⟨_, hs⟩ := h
    exact hs ▸ rfl
  · simp at h

theorem manualAttach_preserves_cardsDrawn (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : manualAttach pokemon energyType state = some (pokemon', state')) :
    state'.cardsDrawn = state.cardsDrawn := by
  unfold manualAttach at h
  split at h
  · simp at h
    obtain ⟨_, hs⟩ := h
    exact hs ▸ rfl
  · simp at h

theorem manualAttach_target_length (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : manualAttach pokemon energyType state = some (pokemon', state')) :
    pokemon'.energy.length = pokemon.energy.length + 1 := by
  have hEnergy := manualAttach_adds_energy pokemon energyType state pokemon' state' h
  simp [hEnergy]

theorem manualAttach_success_requires_unused (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (result : PokemonInPlay × AccelerationState)
    (h : manualAttach pokemon energyType state = some result) :
    canManualAttach state := by
  unfold manualAttach at h
  split at h
  case isTrue hCan =>
    simpa [canManualAttach] using hCan
  case isFalse =>
    simp at h

theorem manualAttach_second_fails (pokemon : PokemonInPlay) (energyType : EnergyType)
    (state : AccelerationState) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : manualAttach pokemon energyType state = some (pokemon', state')) :
    manualAttach pokemon' energyType state' = none := by
  have hFlag := manualAttach_sets_manual_flag pokemon energyType state pokemon' state' h
  unfold manualAttach
  simp [hFlag]

-- Generic acceleration from a zone

theorem attachFromZone_none_of_missing (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (hMissing : removeFirstEnergy energyType source = none) :
    attachFromZone source pokemon energyType = none := by
  simp [attachFromZone, hMissing]

theorem attachFromZone_adds_energy (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (source' : List EnergyType) (pokemon' : PokemonInPlay)
    (h : attachFromZone source pokemon energyType = some (source', pokemon')) :
    pokemon'.energy = pokemon.energy ++ [energyType] := by
  unfold attachFromZone at h
  cases hRem : removeFirstEnergy energyType source with
  | none =>
      simp [hRem] at h
  | some remaining =>
      simp [hRem] at h
      obtain ⟨_, hp⟩ := h
      exact hp ▸ rfl

theorem attachFromZone_source_length (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (source' : List EnergyType) (pokemon' : PokemonInPlay)
    (h : attachFromZone source pokemon energyType = some (source', pokemon')) :
    source'.length + 1 = source.length := by
  unfold attachFromZone at h
  cases hRem : removeFirstEnergy energyType source with
  | none =>
      simp [hRem] at h
  | some remaining =>
      simp [hRem] at h
      obtain ⟨hs, _⟩ := h
      have hLen := removeFirstEnergy_length energyType source remaining hRem
      exact hs ▸ hLen

theorem attachFromZone_target_length (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (source' : List EnergyType) (pokemon' : PokemonInPlay)
    (h : attachFromZone source pokemon energyType = some (source', pokemon')) :
    pokemon'.energy.length = pokemon.energy.length + 1 := by
  have hEnergy := attachFromZone_adds_energy source pokemon energyType source' pokemon' h
  simp [hEnergy]

theorem accelerateFromZone_effectsUsed (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState)
    (source' : List EnergyType) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : accelerateFromZone source pokemon energyType state = some (source', pokemon', state')) :
    state'.effectsUsed = state.effectsUsed + 1 := by
  unfold accelerateFromZone at h
  cases hAttach : attachFromZone source pokemon energyType with
  | none =>
      simp [hAttach] at h
  | some pair =>
      rcases pair with ⟨src, pkm⟩
      simp [hAttach] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem accelerateFromZone_preserves_manualAttachUsed (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState)
    (source' : List EnergyType) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : accelerateFromZone source pokemon energyType state = some (source', pokemon', state')) :
    state'.manualAttachUsed = state.manualAttachUsed := by
  unfold accelerateFromZone at h
  cases hAttach : attachFromZone source pokemon energyType with
  | none =>
      simp [hAttach] at h
  | some pair =>
      rcases pair with ⟨src, pkm⟩
      simp [hAttach] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem accelerateFromZone_preserves_cardsDrawn (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState)
    (source' : List EnergyType) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : accelerateFromZone source pokemon energyType state = some (source', pokemon', state')) :
    state'.cardsDrawn = state.cardsDrawn := by
  unfold accelerateFromZone at h
  cases hAttach : attachFromZone source pokemon energyType with
  | none =>
      simp [hAttach] at h
  | some pair =>
      rcases pair with ⟨src, pkm⟩
      simp [hAttach] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem accelerateFromZone_adds_energy (source : List EnergyType) (pokemon : PokemonInPlay)
    (energyType : EnergyType) (state : AccelerationState)
    (source' : List EnergyType) (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : accelerateFromZone source pokemon energyType state = some (source', pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [energyType] := by
  unfold accelerateFromZone at h
  cases hAttach : attachFromZone source pokemon energyType with
  | none =>
      simp [hAttach] at h
  | some pair =>
      rcases pair with ⟨src, pkm⟩
      simp [hAttach] at h
      obtain ⟨hs, hp, _⟩ := h
      subst hs
      subst hp
      exact attachFromZone_adds_energy source pokemon energyType src pkm hAttach


-- Specific trainer/supporter acceleration effects

theorem welder_none_if_first_fire_missing (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hMissing : removeFirstEnergy .fire hand = none) :
    welder hand pokemon state = none := by
  simp [welder, hMissing]

theorem welder_adds_two_fire (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : welder hand pokemon state = some (hand', pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [.fire, .fire] := by
  unfold welder at h
  cases hFirst : removeFirstEnergy .fire hand with
  | none => simp [hFirst] at h
  | some handAfterFirst =>
      cases hSecond : removeFirstEnergy .fire handAfterFirst with
      | none => simp [hFirst, hSecond] at h
      | some handAfterSecond =>
          simp [hFirst, hSecond] at h
          obtain ⟨_, hp, _⟩ := h
          exact hp ▸ rfl

theorem welder_effectsUsed (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : welder hand pokemon state = some (hand', pokemon', state')) :
    state'.effectsUsed = state.effectsUsed + 1 := by
  unfold welder at h
  cases hFirst : removeFirstEnergy .fire hand with
  | none => simp [hFirst] at h
  | some handAfterFirst =>
      cases hSecond : removeFirstEnergy .fire handAfterFirst with
      | none => simp [hFirst, hSecond] at h
      | some handAfterSecond =>
          simp [hFirst, hSecond] at h
          obtain ⟨_, _, hs⟩ := h
          exact hs ▸ by simp [addDraw, markAcceleration]

theorem welder_draws_three (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : welder hand pokemon state = some (hand', pokemon', state')) :
    state'.cardsDrawn = state.cardsDrawn + 3 := by
  unfold welder at h
  cases hFirst : removeFirstEnergy .fire hand with
  | none => simp [hFirst] at h
  | some handAfterFirst =>
      cases hSecond : removeFirstEnergy .fire handAfterFirst with
      | none => simp [hFirst, hSecond] at h
      | some handAfterSecond =>
          simp [hFirst, hSecond] at h
          obtain ⟨_, _, hs⟩ := h
          exact hs ▸ by simp [addDraw, markAcceleration]

theorem welder_preserves_manualAttachUsed (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : welder hand pokemon state = some (hand', pokemon', state')) :
    state'.manualAttachUsed = state.manualAttachUsed := by
  unfold welder at h
  cases hFirst : removeFirstEnergy .fire hand with
  | none => simp [hFirst] at h
  | some handAfterFirst =>
      cases hSecond : removeFirstEnergy .fire handAfterFirst with
      | none => simp [hFirst, hSecond] at h
      | some handAfterSecond =>
          simp [hFirst, hSecond] at h
          obtain ⟨_, _, hs⟩ := h
          exact hs ▸ by simp [addDraw, markAcceleration]

theorem welder_target_length (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : welder hand pokemon state = some (hand', pokemon', state')) :
    pokemon'.energy.length = pokemon.energy.length + 2 := by
  have hEnergy := welder_adds_two_fire hand pokemon state hand' pokemon' state' h
  simp [hEnergy]

theorem welder_hand_length (hand : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : welder hand pokemon state = some (hand', pokemon', state')) :
    hand'.length + 2 = hand.length := by
  unfold welder at h
  cases hFirst : removeFirstEnergy .fire hand with
  | none => simp [hFirst] at h
  | some handAfterFirst =>
      cases hSecond : removeFirstEnergy .fire handAfterFirst with
      | none => simp [hFirst, hSecond] at h
      | some handAfterSecond =>
          simp [hFirst, hSecond] at h
          obtain ⟨hh, _, _⟩ := h
          have hLen1 := removeFirstEnergy_length .fire hand handAfterFirst hFirst
          have hLen2 := removeFirstEnergy_length .fire handAfterFirst handAfterSecond hSecond
          subst hh
          omega

-- Dark Patch (discard -> attach dark)


theorem darkPatch_adds_dark (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : darkPatch discard pokemon state = some (discard', pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [.dark] := by
  simpa [darkPatch, accelerateFromDiscard]
    using accelerateFromZone_adds_energy discard pokemon .dark state discard' pokemon' state' h

theorem darkPatch_effectsUsed (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : darkPatch discard pokemon state = some (discard', pokemon', state')) :
    state'.effectsUsed = state.effectsUsed + 1 := by
  simpa [darkPatch, accelerateFromDiscard]
    using accelerateFromZone_effectsUsed discard pokemon .dark state discard' pokemon' state' h

-- Max Elixir (deck -> bench, basic only)


theorem removeFirstBasicEnergy_head (energyType : EnergyType) (deck : List EnergyType)
    (hBasic : isBasicEnergy energyType = true) :
    removeFirstBasicEnergy (energyType :: deck) = some (energyType, deck) := by
  simp [removeFirstBasicEnergy, hBasic]

theorem removeFirstBasicEnergy_found_basic :
    ∀ (deck : List EnergyType) (found : EnergyType) (rest : List EnergyType),
      removeFirstBasicEnergy deck = some (found, rest) →
      isBasicEnergy found = true := by
  intro deck found rest h
  induction deck generalizing found rest with
  | nil =>
      simp [removeFirstBasicEnergy] at h
  | cons e tail ih =>
      simp [removeFirstBasicEnergy] at h
      split at h
      · cases h
        assumption
      · cases hRec : removeFirstBasicEnergy tail with
        | none =>
            simp [hRec] at h
        | some pair =>
            rcases pair with ⟨found', rest'⟩
            simp [hRec] at h
            obtain ⟨hFound, _⟩ := h
            have hBasic := ih found' rest' hRec
            simpa [hFound] using hBasic

theorem removeFirstBasicEnergy_length :
    ∀ (deck : List EnergyType) (found : EnergyType) (rest : List EnergyType),
      removeFirstBasicEnergy deck = some (found, rest) →
      rest.length + 1 = deck.length := by
  intro deck found rest h
  induction deck generalizing found rest with
  | nil =>
      simp [removeFirstBasicEnergy] at h
  | cons e tail ih =>
      simp [removeFirstBasicEnergy] at h
      split at h
      · cases h
        simp
      · cases hRec : removeFirstBasicEnergy tail with
        | none =>
            simp [hRec] at h
        | some pair =>
            rcases pair with ⟨found', rest'⟩
            simp [hRec] at h
            obtain ⟨hFound, hRest⟩ := h
            subst hFound
            have hLen := ih found' rest' hRec
            subst hRest
            simp [hLen]

theorem maxElixir_adds_energy (deck : List EnergyType) (benched : PokemonInPlay)
    (state : AccelerationState) (deck' : List EnergyType)
    (benched' : PokemonInPlay) (state' : AccelerationState)
    (h : maxElixir deck benched state = some (deck', benched', state')) :
    ∃ attached, benched'.energy = benched.energy ++ [attached] := by
  unfold maxElixir at h
  cases hBasic : removeFirstBasicEnergy deck with
  | none =>
      simp [hBasic] at h
  | some pair =>
      rcases pair with ⟨attached, restDeck⟩
      simp [hBasic] at h
      obtain ⟨_, hb, _⟩ := h
      refine ⟨attached, ?_⟩
      exact hb ▸ rfl

theorem maxElixir_attaches_basic (deck : List EnergyType) (benched : PokemonInPlay)
    (state : AccelerationState) (deck' : List EnergyType)
    (benched' : PokemonInPlay) (state' : AccelerationState)
    (h : maxElixir deck benched state = some (deck', benched', state')) :
    ∃ attached, isBasicEnergy attached = true ∧ benched'.energy = benched.energy ++ [attached] := by
  unfold maxElixir at h
  cases hBasic : removeFirstBasicEnergy deck with
  | none =>
      simp [hBasic] at h
  | some pair =>
      rcases pair with ⟨attached, restDeck⟩
      simp [hBasic] at h
      obtain ⟨_, hb, _⟩ := h
      refine ⟨attached, ?_, ?_⟩
      · exact removeFirstBasicEnergy_found_basic deck attached restDeck hBasic
      · exact hb ▸ rfl

theorem maxElixir_effectsUsed (deck : List EnergyType) (benched : PokemonInPlay)
    (state : AccelerationState) (deck' : List EnergyType)
    (benched' : PokemonInPlay) (state' : AccelerationState)
    (h : maxElixir deck benched state = some (deck', benched', state')) :
    state'.effectsUsed = state.effectsUsed + 1 := by
  unfold maxElixir at h
  cases hBasic : removeFirstBasicEnergy deck with
  | none =>
      simp [hBasic] at h
  | some pair =>
      rcases pair with ⟨attached, restDeck⟩
      simp [hBasic] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem maxElixir_preserves_manualAttachUsed (deck : List EnergyType) (benched : PokemonInPlay)
    (state : AccelerationState) (deck' : List EnergyType)
    (benched' : PokemonInPlay) (state' : AccelerationState)
    (h : maxElixir deck benched state = some (deck', benched', state')) :
    state'.manualAttachUsed = state.manualAttachUsed := by
  unfold maxElixir at h
  cases hBasic : removeFirstBasicEnergy deck with
  | none =>
      simp [hBasic] at h
  | some pair =>
      rcases pair with ⟨attached, restDeck⟩
      simp [hBasic] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem maxElixir_deck_length (deck : List EnergyType) (benched : PokemonInPlay)
    (state : AccelerationState) (deck' : List EnergyType)
    (benched' : PokemonInPlay) (state' : AccelerationState)
    (h : maxElixir deck benched state = some (deck', benched', state')) :
    deck'.length + 1 = deck.length := by
  unfold maxElixir at h
  cases hBasic : removeFirstBasicEnergy deck with
  | none =>
      simp [hBasic] at h
  | some pair =>
      rcases pair with ⟨attached, restDeck⟩
      simp [hBasic] at h
      obtain ⟨hd, _, _⟩ := h
      have hLen := removeFirstBasicEnergy_length deck attached restDeck hBasic
      exact hd ▸ hLen

-- Melony (discard water + draw)

theorem melony_adds_water (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : melony discard pokemon state = some (discard', pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [.water] := by
  unfold melony at h
  cases hAccel : accelerateFromDiscard discard pokemon .water state with
  | none =>
      simp [hAccel] at h
  | some triple =>
      rcases triple with ⟨discard1, pokemon1, state1⟩
      simp [hAccel] at h
      obtain ⟨hd, hp, hs⟩ := h
      subst hd
      subst hp
      have hAdd := accelerateFromZone_adds_energy discard pokemon .water state discard1 pokemon1 state1
        (by simpa [accelerateFromDiscard] using hAccel)
      simpa using hAdd

theorem melony_effectsUsed (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : melony discard pokemon state = some (discard', pokemon', state')) :
    state'.effectsUsed = state.effectsUsed + 1 := by
  unfold melony at h
  cases hAccel : accelerateFromDiscard discard pokemon .water state with
  | none =>
      simp [hAccel] at h
  | some triple =>
      rcases triple with ⟨discard1, pokemon1, state1⟩
      simp [hAccel] at h
      obtain ⟨_, _, hs⟩ := h
      subst hs
      have hEff := accelerateFromZone_effectsUsed discard pokemon .water state discard1 pokemon1 state1
        (by simpa [accelerateFromDiscard] using hAccel)
      simp [addDraw, hEff]

theorem melony_draws_three (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : melony discard pokemon state = some (discard', pokemon', state')) :
    state'.cardsDrawn = state.cardsDrawn + 3 := by
  unfold melony at h
  cases hAccel : accelerateFromDiscard discard pokemon .water state with
  | none =>
      simp [hAccel] at h
  | some triple =>
      rcases triple with ⟨discard1, pokemon1, state1⟩
      simp [hAccel] at h
      obtain ⟨_, _, hs⟩ := h
      subst hs
      have hDraw : state1.cardsDrawn = state.cardsDrawn := by
        exact accelerateFromZone_preserves_cardsDrawn discard pokemon .water state discard1 pokemon1 state1
          (by simpa [accelerateFromDiscard] using hAccel)
      simp [addDraw, hDraw]

theorem melony_preserves_manualAttachUsed (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : melony discard pokemon state = some (discard', pokemon', state')) :
    state'.manualAttachUsed = state.manualAttachUsed := by
  unfold melony at h
  cases hAccel : accelerateFromDiscard discard pokemon .water state with
  | none =>
      simp [hAccel] at h
  | some triple =>
      rcases triple with ⟨discard1, pokemon1, state1⟩
      simp [hAccel] at h
      obtain ⟨_, _, hs⟩ := h
      subst hs
      have hManual := accelerateFromZone_preserves_manualAttachUsed discard pokemon .water state discard1 pokemon1 state1
        (by simpa [accelerateFromDiscard] using hAccel)
      simp [addDraw, hManual]

theorem melony_target_length (discard : List EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (discard' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : melony discard pokemon state = some (discard', pokemon', state')) :
    pokemon'.energy.length = pokemon.energy.length + 1 := by
  have hWater := melony_adds_water discard pokemon state discard' pokemon' state' h
  simp [hWater]

-- Energy trans abilities (Arcanine/Blastoise)

theorem moveEnergy_source_length (source target : PokemonInPlay) (energyType : EnergyType)
    (source' target' : PokemonInPlay)
    (h : moveEnergy source target energyType = some (source', target')) :
    source'.energy.length + 1 = source.energy.length := by
  unfold moveEnergy at h
  cases hRem : removeFirstEnergy energyType source.energy with
  | none =>
      simp [hRem] at h
  | some sourceEnergy =>
      simp [hRem] at h
      obtain ⟨hs, _⟩ := h
      subst hs
      exact removeFirstEnergy_length energyType source.energy sourceEnergy hRem

theorem moveEnergy_target_energy (source target : PokemonInPlay) (energyType : EnergyType)
    (source' target' : PokemonInPlay)
    (h : moveEnergy source target energyType = some (source', target')) :
    target'.energy = target.energy ++ [energyType] := by
  unfold moveEnergy at h
  cases hRem : removeFirstEnergy energyType source.energy with
  | none =>
      simp [hRem] at h
  | some sourceEnergy =>
      simp [hRem] at h
      obtain ⟨_, ht⟩ := h
      exact ht ▸ rfl

theorem moveEnergy_target_length (source target : PokemonInPlay) (energyType : EnergyType)
    (source' target' : PokemonInPlay)
    (h : moveEnergy source target energyType = some (source', target')) :
    target'.energy.length = target.energy.length + 1 := by
  have hEnergy := moveEnergy_target_energy source target energyType source' target' h
  simp [hEnergy]

theorem moveEnergy_preserves_source_card (source target : PokemonInPlay) (energyType : EnergyType)
    (source' target' : PokemonInPlay)
    (h : moveEnergy source target energyType = some (source', target')) :
    source'.card = source.card := by
  unfold moveEnergy at h
  cases hRem : removeFirstEnergy energyType source.energy with
  | none =>
      simp [hRem] at h
  | some sourceEnergy =>
      simp [hRem] at h
      obtain ⟨hs, _⟩ := h
      exact hs ▸ rfl

theorem moveEnergy_preserves_target_card (source target : PokemonInPlay) (energyType : EnergyType)
    (source' target' : PokemonInPlay)
    (h : moveEnergy source target energyType = some (source', target')) :
    target'.card = target.card := by
  unfold moveEnergy at h
  cases hRem : removeFirstEnergy energyType source.energy with
  | none =>
      simp [hRem] at h
  | some sourceEnergy =>
      simp [hRem] at h
      obtain ⟨_, ht⟩ := h
      exact ht ▸ rfl


theorem arcanineEnergyTrans_adds_fire (source target : PokemonInPlay)
    (source' target' : PokemonInPlay)
    (h : arcanineEnergyTrans source target = some (source', target')) :
    target'.energy = target.energy ++ [.fire] := by
  simpa [arcanineEnergyTrans] using moveEnergy_target_energy source target .fire source' target' h

theorem blastoiseEnergyTrans_adds_water (source target : PokemonInPlay)
    (source' target' : PokemonInPlay)
    (h : blastoiseEnergyTrans source target = some (source', target')) :
    target'.energy = target.energy ++ [.water] := by
  simpa [blastoiseEnergyTrans] using moveEnergy_target_energy source target .water source' target' h

-- Double Turbo Energy


theorem applyDoubleTurboPenalty_le_base (baseDamage : Nat) :
    applyDoubleTurboPenalty baseDamage ≤ baseDamage := by
  simp [applyDoubleTurboPenalty]

theorem applyDoubleTurboPenalty_zero_of_small (baseDamage : Nat)
    (hSmall : baseDamage ≤ 20) :
    applyDoubleTurboPenalty baseDamage = 0 := by
  simp [applyDoubleTurboPenalty, Nat.sub_eq_zero_of_le hSmall]


-- Aurora Energy (discard cost on attach)

theorem auroraAttach_none_if_missing_cost (hand : List EnergyType)
    (discardCost providedType : EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState)
    (hMissing : removeFirstEnergy discardCost hand = none) :
    auroraAttach hand discardCost providedType pokemon state = none := by
  simp [auroraAttach, hMissing]

theorem auroraAttach_adds_selected_energy (hand : List EnergyType)
    (discardCost providedType : EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : auroraAttach hand discardCost providedType pokemon state = some (hand', pokemon', state')) :
    pokemon'.energy = pokemon.energy ++ [providedType] := by
  unfold auroraAttach at h
  cases hRem : removeFirstEnergy discardCost hand with
  | none =>
      simp [hRem] at h
  | some remaining =>
      simp [hRem] at h
      obtain ⟨_, hp, _⟩ := h
      exact hp ▸ rfl

theorem auroraAttach_discards_one (hand : List EnergyType)
    (discardCost providedType : EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : auroraAttach hand discardCost providedType pokemon state = some (hand', pokemon', state')) :
    hand'.length + 1 = hand.length := by
  unfold auroraAttach at h
  cases hRem : removeFirstEnergy discardCost hand with
  | none =>
      simp [hRem] at h
  | some remaining =>
      simp [hRem] at h
      obtain ⟨hh, _, _⟩ := h
      have hLen := removeFirstEnergy_length discardCost hand remaining hRem
      exact hh ▸ hLen

theorem auroraAttach_effectsUsed (hand : List EnergyType)
    (discardCost providedType : EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : auroraAttach hand discardCost providedType pokemon state = some (hand', pokemon', state')) :
    state'.effectsUsed = state.effectsUsed + 1 := by
  unfold auroraAttach at h
  cases hRem : removeFirstEnergy discardCost hand with
  | none =>
      simp [hRem] at h
  | some remaining =>
      simp [hRem] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem auroraAttach_preserves_manualAttachUsed (hand : List EnergyType)
    (discardCost providedType : EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : auroraAttach hand discardCost providedType pokemon state = some (hand', pokemon', state')) :
    state'.manualAttachUsed = state.manualAttachUsed := by
  unfold auroraAttach at h
  cases hRem : removeFirstEnergy discardCost hand with
  | none =>
      simp [hRem] at h
  | some remaining =>
      simp [hRem] at h
      obtain ⟨_, _, hs⟩ := h
      exact hs ▸ by simp [markAcceleration]

theorem auroraAttach_target_length (hand : List EnergyType)
    (discardCost providedType : EnergyType) (pokemon : PokemonInPlay)
    (state : AccelerationState) (hand' : List EnergyType)
    (pokemon' : PokemonInPlay) (state' : AccelerationState)
    (h : auroraAttach hand discardCost providedType pokemon state = some (hand', pokemon', state')) :
    pokemon'.energy.length = pokemon.energy.length + 1 := by
  have hEnergy := auroraAttach_adds_selected_energy hand discardCost providedType pokemon state hand' pokemon' state' h
  simp [hEnergy]

end PokemonLean.EnergyAcceleration
