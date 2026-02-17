/-
  PokemonLean / AbilityMechanics.lean

  Pokémon TCG Ability mechanics formalised in Lean 4.
  Covers: abilities (Intimidate, Gale Wings, Protean, Weather abilities),
  ability triggers as state transitions, ability negation
  (Path to the Peak interaction), ability ordering/priority.

  All proofs are sorry‑free.  Uses computational paths for state transitions.
-/

namespace PokemonLean.AbilityMechanics

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Pokémon types. -/
inductive PType where
  | fire | water | grass | electric | psychic | fighting
  | dark | metal | dragon | fairy | normal | ice | flying
  | poison | ground | rock | bug | ghost | steel
  deriving DecidableEq, Repr

/-- Card categories relevant to ability interactions. -/
inductive CardKind where
  | basic | stage1 | stage2 | ex | gx | vstar | vmax | ruleBox
  deriving DecidableEq, Repr

/-- Whether a card is a Rule Box Pokémon (relevant for Path to the Peak). -/
def CardKind.isRuleBox : CardKind → Bool
  | .ex => true
  | .gx => true
  | .vstar => true
  | .vmax => true
  | .ruleBox => true
  | _ => false

/-- Ability identifiers. -/
inductive Ability where
  | intimidate       -- On entry: reduce opponent active's attack by 20
  | galeWings        -- Priority +1 for Flying moves if HP is full
  | protean          -- Change type to match the move used
  | drizzle          -- On entry: set weather to Rain
  | drought          -- On entry: set weather to Sun
  | sandStream       -- On entry: set weather to Sandstorm
  | snowWarning      -- On entry: set weather to Hail
  | levitate         -- Immune to Ground attacks
  | sturdy           -- Survive a OHKO at 1 HP if at full HP
  | pressureAbility  -- Opponent uses 2 energy per attack
  | moldBreaker      -- Ignore opponent's ability
  | neutralizingGas  -- All other abilities are suppressed
  | noAbility        -- Placeholder: no ability
  deriving DecidableEq, Repr

/-- Weather conditions. -/
inductive Weather where
  | none | rain | sun | sandstorm | hail
  deriving DecidableEq, Repr

/-- A simplified Pokémon in play. -/
structure Pokemon where
  name      : String
  kind      : CardKind
  ptype     : PType
  ability   : Ability
  hp        : Nat
  maxHp     : Nat
  damage    : Nat
  isActive  : Bool
  deriving DecidableEq, Repr

/-- Whether a Pokémon is at full HP. -/
def Pokemon.fullHp (p : Pokemon) : Bool := p.damage == 0

-- ============================================================
-- §2  Game state for ability interactions
-- ============================================================

/-- Negation sources that can shut off abilities. -/
inductive NegationSource where
  | pathToThePeak    -- Stadium card: Rule Box Pokémon have no abilities
  | neutralizingGas  -- Weezing ability: all other abilities off
  | moldBreaker      -- Attacker ignores defender's ability
  | none             -- No negation active
  deriving DecidableEq, Repr

/-- The game state relevant to ability mechanics. -/
structure GameState where
  weather        : Weather
  negation       : NegationSource
  playerActive   : Pokemon
  opponentActive : Pokemon
  playerBench    : List Pokemon
  opponentBench  : List Pokemon
  atkModifier    : Int       -- global attack modifier
  turnNumber     : Nat
  deriving Repr

-- ============================================================
-- §3  Ability active check (accounting for negation)
-- ============================================================

/-- Whether a Pokémon's ability is currently active, given negation. -/
def abilityActive (neg : NegationSource) (p : Pokemon) : Bool :=
  match neg with
  | .none => true
  | .pathToThePeak => !p.kind.isRuleBox
  | .neutralizingGas => p.ability == .neutralizingGas -- only NeutGas itself stays on
  | .moldBreaker => true  -- mold breaker is checked per-interaction

/-- Theorem 1: With no negation, every ability is active. -/
theorem abilityActive_none (p : Pokemon) :
    abilityActive .none p = true := by
  simp [abilityActive]

/-- Theorem 2: Path to the Peak shuts off Rule Box abilities. -/
theorem pathToThePeak_negates_ruleBox (p : Pokemon)
    (hrb : p.kind.isRuleBox = true) :
    abilityActive .pathToThePeak p = false := by
  simp [abilityActive, hrb]

/-- Theorem 3: Path to the Peak does NOT negate non‑Rule‑Box Pokémon. -/
theorem pathToThePeak_allows_nonRuleBox (p : Pokemon)
    (hnrb : p.kind.isRuleBox = false) :
    abilityActive .pathToThePeak p = true := by
  simp [abilityActive, hnrb]

/-- Theorem 4: Basic Pokémon are never Rule Box. -/
theorem basic_not_ruleBox : CardKind.isRuleBox .basic = false := by
  simp [CardKind.isRuleBox]

/-- Theorem 5: EX Pokémon are Rule Box. -/
theorem ex_is_ruleBox : CardKind.isRuleBox .ex = true := by
  simp [CardKind.isRuleBox]

-- ============================================================
-- §4  Steps (state transitions triggered by abilities)
-- ============================================================

/-- One‑step ability‑triggered state transition. -/
inductive AbilityStep : GameState → GameState → Prop where
  | drizzle (gs : GameState)
      (hact : abilityActive gs.negation gs.playerActive = true)
      (hab  : gs.playerActive.ability = .drizzle) :
      AbilityStep gs { gs with weather := .rain }
  | drought (gs : GameState)
      (hact : abilityActive gs.negation gs.playerActive = true)
      (hab  : gs.playerActive.ability = .drought) :
      AbilityStep gs { gs with weather := .sun }
  | sandStream (gs : GameState)
      (hact : abilityActive gs.negation gs.playerActive = true)
      (hab  : gs.playerActive.ability = .sandStream) :
      AbilityStep gs { gs with weather := .sandstorm }
  | snowWarning (gs : GameState)
      (hact : abilityActive gs.negation gs.playerActive = true)
      (hab  : gs.playerActive.ability = .snowWarning) :
      AbilityStep gs { gs with weather := .hail }
  | intimidate (gs : GameState)
      (hact : abilityActive gs.negation gs.playerActive = true)
      (hab  : gs.playerActive.ability = .intimidate) :
      AbilityStep gs { gs with atkModifier := gs.atkModifier - 20 }
  | neutralizingGasOn (gs : GameState)
      (hab : gs.playerActive.ability = .neutralizingGas) :
      AbilityStep gs { gs with negation := .neutralizingGas }
  | sturdySurvive (gs : GameState)
      (hact : abilityActive gs.negation gs.playerActive = true)
      (hab  : gs.playerActive.ability = .sturdy)
      (hfull : gs.playerActive.fullHp = true)
      (hlethal : gs.playerActive.damage ≥ gs.playerActive.maxHp) :
      AbilityStep gs { gs with
        playerActive := { gs.playerActive with damage := gs.playerActive.maxHp - 1 } }

/-- Multi‑step ability path (trans structure). -/
inductive AbilityPath : GameState → GameState → Prop where
  | refl (gs : GameState) : AbilityPath gs gs
  | step {a b c : GameState} (s : AbilityStep a b) (p : AbilityPath b c) :
      AbilityPath a c

/-- Theorem 6: Transitivity of ability paths. -/
theorem AbilityPath.trans {a b c : GameState}
    (p : AbilityPath a b) (q : AbilityPath b c) : AbilityPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact AbilityPath.step s (ih q)

/-- Theorem 7: Single step lifts to a path. -/
theorem AbilityPath.single {a b : GameState}
    (s : AbilityStep a b) : AbilityPath a b :=
  AbilityPath.step s (AbilityPath.refl b)

-- ============================================================
-- §5  Weather ability theorems
-- ============================================================

/-- Theorem 8: Drizzle sets rain weather. -/
theorem drizzle_sets_rain (gs : GameState)
    (hact : abilityActive gs.negation gs.playerActive = true)
    (hab : gs.playerActive.ability = .drizzle) :
    ∃ gs', AbilityStep gs gs' ∧ gs'.weather = .rain := by
  exact ⟨{ gs with weather := .rain }, AbilityStep.drizzle gs hact hab, rfl⟩

/-- Theorem 9: Drought sets sun weather. -/
theorem drought_sets_sun (gs : GameState)
    (hact : abilityActive gs.negation gs.playerActive = true)
    (hab : gs.playerActive.ability = .drought) :
    ∃ gs', AbilityStep gs gs' ∧ gs'.weather = .sun := by
  exact ⟨{ gs with weather := .sun }, AbilityStep.drought gs hact hab, rfl⟩

/-- Theorem 10: Weather abilities only change weather, not negation. -/
theorem weather_ability_preserves_negation (gs gs' : GameState)
    (hstep : AbilityStep gs gs') (hw : gs.playerActive.ability = .drizzle ∨
        gs.playerActive.ability = .drought ∨
        gs.playerActive.ability = .sandStream ∨
        gs.playerActive.ability = .snowWarning) :
    gs'.negation = gs.negation := by
  cases hstep <;> simp_all

-- ============================================================
-- §6  Intimidate theorems
-- ============================================================

/-- Theorem 11: Intimidate reduces attack by 20. -/
theorem intimidate_reduces_atk (gs : GameState)
    (hact : abilityActive gs.negation gs.playerActive = true)
    (hab : gs.playerActive.ability = .intimidate) :
    ∃ gs', AbilityStep gs gs' ∧ gs'.atkModifier = gs.atkModifier - 20 := by
  exact ⟨_, AbilityStep.intimidate gs hact hab, rfl⟩

/-- Theorem 12: Intimidate preserves weather. -/
theorem intimidate_preserves_weather (gs : GameState)
    (hact : abilityActive gs.negation gs.playerActive = true)
    (hab : gs.playerActive.ability = .intimidate) :
    ({ gs with atkModifier := gs.atkModifier - 20 } : GameState).weather = gs.weather := by
  rfl

-- ============================================================
-- §7  Negation interaction theorems
-- ============================================================

/-- Theorem 13: Neutralizing Gas shuts off other abilities. -/
theorem neutralizing_gas_shuts_off (gs : GameState)
    (hab : gs.playerActive.ability = .neutralizingGas) :
    ∃ gs', AbilityStep gs gs' ∧ gs'.negation = .neutralizingGas := by
  exact ⟨_, AbilityStep.neutralizingGasOn gs hab, rfl⟩

/-- Theorem 14: Under Neutralizing Gas, non‑NeutGas abilities are inactive. -/
theorem neutGas_suppresses (p : Pokemon)
    (hne : p.ability ≠ .neutralizingGas) :
    abilityActive .neutralizingGas p = false := by
  simp [abilityActive]
  intro h
  exact absurd h hne

/-- Theorem 15: Under Neutralizing Gas, the NeutGas holder itself stays active. -/
theorem neutGas_self_active (p : Pokemon)
    (hab : p.ability = .neutralizingGas) :
    abilityActive .neutralizingGas p = true := by
  simp [abilityActive, hab]

-- ============================================================
-- §8  Ability ordering / priority
-- ============================================================

/-- Priority of an ability (higher = resolves first). -/
def abilityPriority : Ability → Nat
  | .neutralizingGas => 100  -- resolves first (shuts others off)
  | .moldBreaker     => 90   -- resolves before defender ability
  | .intimidate      => 50   -- on-entry
  | .drizzle         => 40
  | .drought         => 40
  | .sandStream      => 40
  | .snowWarning     => 40
  | .galeWings       => 30
  | .protean         => 20
  | .levitate        => 10
  | .sturdy          => 10
  | .pressureAbility => 10
  | .noAbility       => 0

/-- Theorem 16: Neutralizing Gas has the highest priority. -/
theorem neutGas_highest_priority (a : Ability) :
    abilityPriority a ≤ abilityPriority .neutralizingGas := by
  cases a <;> simp [abilityPriority] <;> omega

/-- Theorem 17: Mold Breaker has second highest priority. -/
theorem moldBreaker_high_priority (a : Ability)
    (hne : a ≠ .neutralizingGas) :
    abilityPriority a ≤ abilityPriority .moldBreaker := by
  cases a <;> simp_all [abilityPriority] <;> omega

/-- Theorem 18: Weather abilities all have the same priority. -/
theorem weather_abilities_same_priority :
    abilityPriority .drizzle = abilityPriority .drought ∧
    abilityPriority .drought = abilityPriority .sandStream ∧
    abilityPriority .sandStream = abilityPriority .snowWarning := by
  simp [abilityPriority]

-- ============================================================
-- §9  Gale Wings and Protean (type‑changing abilities)
-- ============================================================

/-- Gale Wings condition: full HP. -/
def galeWingsActive (p : Pokemon) : Bool :=
  p.ability == .galeWings && p.fullHp

/-- Theorem 19: Gale Wings requires full HP. -/
theorem galeWings_needs_fullHp (p : Pokemon)
    (hab : p.ability = .galeWings) (hdmg : p.damage > 0) :
    galeWingsActive p = false := by
  simp [galeWingsActive, Pokemon.fullHp, hab]
  omega

/-- Protean type change. -/
def proteanTypeChange (p : Pokemon) (moveType : PType) : Pokemon :=
  if p.ability == .protean then { p with ptype := moveType } else p

/-- Theorem 20: Protean changes the Pokémon's type to the move's type. -/
theorem protean_changes_type (p : Pokemon) (mt : PType)
    (hab : p.ability = .protean) :
    (proteanTypeChange p mt).ptype = mt := by
  simp [proteanTypeChange, hab]

/-- Theorem 21: Without Protean, type doesn't change. -/
theorem no_protean_no_change (p : Pokemon) (mt : PType)
    (hab : p.ability ≠ .protean) :
    (proteanTypeChange p mt).ptype = p.ptype := by
  simp [proteanTypeChange]
  split
  · next h => exact absurd h hab
  · rfl

-- ============================================================
-- §10  Path to the Peak interaction (deep)
-- ============================================================

/-- Theorem 22: Stage 1 Pokémon keep abilities under Path to the Peak. -/
theorem stage1_keeps_ability_under_peak (p : Pokemon)
    (hk : p.kind = .stage1) :
    abilityActive .pathToThePeak p = true := by
  simp [abilityActive, CardKind.isRuleBox, hk]

/-- Theorem 23: VSTAR loses abilities under Path to the Peak. -/
theorem vstar_loses_ability_under_peak (p : Pokemon)
    (hk : p.kind = .vstar) :
    abilityActive .pathToThePeak p = false := by
  simp [abilityActive, CardKind.isRuleBox, hk]

/-- Theorem 24: A drizzle-bearing EX Pokémon can't set rain under Path to the Peak. -/
theorem ex_drizzle_blocked_by_peak (gs : GameState)
    (hpeak : gs.negation = .pathToThePeak)
    (hex : gs.playerActive.kind = .ex)
    (hab : gs.playerActive.ability = .drizzle) :
    abilityActive gs.negation gs.playerActive = false := by
  simp [hpeak, abilityActive, CardKind.isRuleBox, hex]

-- ============================================================
-- §11  Congruence / transport along ability paths
-- ============================================================

/-- A property of game states is ability‑invariant. -/
def AbilityInvariant (P : GameState → Prop) : Prop :=
  ∀ gs gs', AbilityStep gs gs' → P gs → P gs'

/-- Theorem 25: Transport along ability paths. -/
theorem transport_ability_path {P : GameState → Prop}
    (hinv : AbilityInvariant P) {a b : GameState}
    (p : AbilityPath a b) (ha : P a) : P b := by
  induction p with
  | refl _ => exact ha
  | step s _ ih => exact ih (hinv _ _ s ha)

/-- Theorem 26: Turn number is preserved by ability steps. -/
theorem ability_step_preserves_turn (gs gs' : GameState)
    (h : AbilityStep gs gs') : gs'.turnNumber = gs.turnNumber := by
  cases h <;> rfl

/-- Theorem 27: Turn number is preserved along ability paths (transport). -/
theorem ability_path_preserves_turn {a b : GameState}
    (p : AbilityPath a b) : b.turnNumber = a.turnNumber := by
  induction p with
  | refl _ => rfl
  | step s _ ih => rw [ih, ability_step_preserves_turn _ _ s]

end PokemonLean.AbilityMechanics
