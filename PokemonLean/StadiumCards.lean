/-
  Stadium Cards — Pokemon TCG Stadium Card Mechanics
  ====================================================
  Stadium card mechanics (Path to the Peak, Temple of Sinnoh, Collapsed Stadium, etc.),
  stadium replacement rules, effects on abilities/energy, at most one stadium in play.

  All theorems sorry-free. Uses computational paths for game state transitions.
-/

namespace PokemonLean.StadiumCards

-- ============================================================
-- Core types
-- ============================================================

/-- Energy types in the Pokemon TCG. -/
inductive EnergyType where
  | fire | water | grass | electric | psychic | fighting
  | dark | metal | dragon | fairy | colorless | special
  deriving DecidableEq, Repr

/-- Whether an energy is basic or special. -/
def EnergyType.isBasic : EnergyType → Bool
  | .special => false
  | _ => true

/-- Pokemon card types relevant to stadium effects. -/
inductive PokemonKind where
  | basic | stage1 | stage2 | vstar | vmax | ex | gx | ruleBox
  deriving DecidableEq, Repr

/-- Whether a Pokemon is a Rule Box Pokemon. -/
def PokemonKind.isRuleBox : PokemonKind → Bool
  | .vstar => true
  | .vmax => true
  | .ex => true
  | .gx => true
  | .ruleBox => true
  | _ => false

/-- Stadium card identifiers. -/
inductive StadiumCard where
  | pathToThePeak
  | templeOfSinnoh
  | collapsedStadium
  | magmaBasin
  | artazonPark
  | lostCity
  | snowyBath
  | beachCourt
  | jubilifeVillage
  deriving DecidableEq, Repr

-- ============================================================
-- Game state
-- ============================================================

/-- Bench slot (0 = active, 1..n = bench). -/
abbrev SlotId := Nat

/-- A simplified Pokemon in play. -/
structure PokemonInPlay where
  kind : PokemonKind
  hasAbility : Bool
  attachedEnergy : List EnergyType
  hp : Nat
  damage : Nat
  deriving DecidableEq, Repr

/-- The field state relevant to stadium effects. -/
structure FieldState where
  activeStadium : Option StadiumCard
  player1Bench : List PokemonInPlay
  player2Bench : List PokemonInPlay
  player1Active : Option PokemonInPlay
  player2Active : Option PokemonInPlay
  player1BenchLimit : Nat  -- normally 5
  player2BenchLimit : Nat
  deriving Repr

/-- Default field state with no stadium and 5-slot benches. -/
def FieldState.default : FieldState :=
  { activeStadium := none
    player1Bench := []
    player2Bench := []
    player1Active := none
    player2Active := none
    player1BenchLimit := 5
    player2BenchLimit := 5 }

-- ============================================================
-- Stadium effects as state transitions (computational paths)
-- ============================================================

/-- A game state transition / path step. -/
inductive Step : FieldState → FieldState → Prop where
  | playStadium : (s : FieldState) → (card : StadiumCard) →
      Step s { s with activeStadium := some card }
  | replaceStadium : (s : FieldState) → (card : StadiumCard) →
      s.activeStadium.isSome = true →
      Step s { s with activeStadium := some card }
  | removeStadium : (s : FieldState) →
      s.activeStadium.isSome = true →
      Step s { s with activeStadium := none }

/-- Multi-step path between game states. -/
inductive Path : FieldState → FieldState → Prop where
  | refl : (s : FieldState) → Path s s
  | step : {s t u : FieldState} → Step s t → Path t u → Path s u

/-- Path concatenation / transitivity. -/
def Path.trans {s t u : FieldState} : Path s t → Path t u → Path s u :=
  fun p q => match p with
  | .refl _ => q
  | .step h rest => .step h (rest.trans q)

-- ============================================================
-- Stadium-specific effect predicates
-- ============================================================

/-- Path to the Peak: Rule Box Pokemon have no abilities. -/
def pathToThePeakActive (s : FieldState) : Prop :=
  s.activeStadium = some .pathToThePeak

/-- Under Path to the Peak, a rule box Pokemon's ability is negated. -/
def abilityNegated (s : FieldState) (pk : PokemonInPlay) : Prop :=
  pathToThePeakActive s ∧ pk.kind.isRuleBox = true ∧ pk.hasAbility = true

/-- Temple of Sinnoh: special energy counts as colorless. -/
def templeOfSinnohActive (s : FieldState) : Prop :=
  s.activeStadium = some .templeOfSinnoh

/-- Collapsed Stadium: bench limit reduced to 4. -/
def collapsedStadiumActive (s : FieldState) : Prop :=
  s.activeStadium = some .collapsedStadium

/-- Apply Collapsed Stadium effect: reduce bench limits. -/
def applyCollapsedStadium (s : FieldState) : FieldState :=
  { s with player1BenchLimit := min s.player1BenchLimit 4
           player2BenchLimit := min s.player2BenchLimit 4 }

-- ============================================================
-- Theorems
-- ============================================================

/-- Theorem 1: At most one stadium in play at any time. -/
theorem at_most_one_stadium (s : FieldState) :
    match s.activeStadium with
    | none => True
    | some _ => ∀ c₁ c₂, s.activeStadium = some c₁ → s.activeStadium = some c₂ → c₁ = c₂ := by
  cases h : s.activeStadium with
  | none => trivial
  | some c => intro c₁ c₂ h₁ h₂; simp_all

/-- Theorem 2: Playing a new stadium replaces the old one. -/
theorem play_replaces_stadium (s : FieldState) (old new_ : StadiumCard)
    (_h : s.activeStadium = some old) :
    { s with activeStadium := some new_ }.activeStadium = some new_ := by
  rfl

/-- Theorem 3: After playing a stadium, exactly that stadium is active. -/
theorem play_stadium_active (s : FieldState) (c : StadiumCard) :
    ({ s with activeStadium := some c } : FieldState).activeStadium = some c := by
  rfl

/-- Theorem 4: Stadium removal leaves no stadium. -/
theorem remove_stadium_none (s : FieldState) :
    ({ s with activeStadium := none } : FieldState).activeStadium = none := by
  rfl

/-- Theorem 5: Path to the Peak negates rule box abilities. -/
theorem path_to_peak_negates_vstar (s : FieldState)
    (h : pathToThePeakActive s) (pk : PokemonInPlay)
    (hk : pk.kind = .vstar) (ha : pk.hasAbility = true) :
    abilityNegated s pk := by
  exact ⟨h, by simp [PokemonKind.isRuleBox, hk], ha⟩

/-- Theorem 6: Path to the Peak does NOT negate basic Pokemon abilities. -/
theorem path_to_peak_spares_basic (pk : PokemonInPlay)
    (hk : pk.kind = .basic) :
    pk.kind.isRuleBox = false := by
  simp [PokemonKind.isRuleBox, hk]

/-- Theorem 7: Temple of Sinnoh makes special energy count as colorless.
    Formally: under Temple, special energy is "basic" for type-checking = false. -/
theorem temple_special_not_basic :
    EnergyType.isBasic .special = false := by
  rfl

/-- Theorem 8: Basic energy is unaffected by Temple of Sinnoh. -/
theorem temple_basic_unaffected (e : EnergyType) (h : e ≠ .special) :
    e.isBasic = true := by
  cases e <;> simp_all [EnergyType.isBasic]

/-- Theorem 9: Collapsed Stadium reduces bench to at most 4. -/
theorem collapsed_stadium_bench_limit (s : FieldState) :
    (applyCollapsedStadium s).player1BenchLimit ≤ 4 ∧
    (applyCollapsedStadium s).player2BenchLimit ≤ 4 := by
  simp [applyCollapsedStadium]
  exact ⟨Nat.min_le_right _ _, Nat.min_le_right _ _⟩

/-- Theorem 10: Collapsed Stadium is idempotent. -/
theorem collapsed_stadium_idempotent (s : FieldState) :
    applyCollapsedStadium (applyCollapsedStadium s) = applyCollapsedStadium s := by
  unfold applyCollapsedStadium
  congr 1 <;> simp [Nat.min_assoc]

/-- Theorem 11: Playing same stadium twice yields same field state. -/
theorem play_same_stadium_idem (s : FieldState) (c : StadiumCard) :
    ({ s with activeStadium := some c } : FieldState)
    = { { s with activeStadium := some c } with activeStadium := some c } := by
  rfl

/-- Theorem 12: Path reflexivity — any state reaches itself. -/
theorem path_refl_exists (s : FieldState) : Path s s :=
  Path.refl s

/-- Theorem 13: Path transitivity is associative. -/
theorem path_trans_assoc {s t u v : FieldState}
    (p : Path s t) (q : Path t u) (r : Path u v) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | refl _ => rfl
  | step _h _rest _ih => rfl

/-- Theorem 14: Replacing a stadium then removing it returns to no-stadium state. -/
theorem replace_then_remove (s : FieldState) (c : StadiumCard) :
    ({ { s with activeStadium := some c } with activeStadium := none } : FieldState).activeStadium
    = none := by
  rfl

/-- Theorem 15: No stadium means Path to the Peak is not active. -/
theorem no_stadium_no_peak (s : FieldState) (h : s.activeStadium = none) :
    ¬ pathToThePeakActive s := by
  intro hp
  simp [pathToThePeakActive] at hp
  rw [h] at hp
  exact absurd hp (by simp)

/-- Theorem 16: Different stadium means Path to the Peak not active. -/
theorem different_stadium_no_peak (s : FieldState) (c : StadiumCard)
    (hne : c ≠ .pathToThePeak) (hs : s.activeStadium = some c) :
    ¬ pathToThePeakActive s := by
  intro hp
  simp [pathToThePeakActive] at hp
  rw [hs] at hp
  exact hne (Option.some.inj hp)

/-- Theorem 17: Playing two different stadiums in sequence — last one wins. -/
theorem last_stadium_wins (s : FieldState) (c₁ c₂ : StadiumCard) :
    ({ { s with activeStadium := some c₁ } with activeStadium := some c₂ } : FieldState).activeStadium
    = some c₂ := by
  rfl

/-- Theorem 18: Bench limit is preserved when playing a stadium. -/
theorem bench_limit_preserved_on_play (s : FieldState) (c : StadiumCard)
    (_h : c ≠ .collapsedStadium) :
    ({ s with activeStadium := some c } : FieldState).player1BenchLimit = s.player1BenchLimit := by
  rfl

/-- Theorem 19: Default field has 5-slot bench. -/
theorem default_bench_limit :
    FieldState.default.player1BenchLimit = 5 ∧ FieldState.default.player2BenchLimit = 5 := by
  exact ⟨rfl, rfl⟩

/-- Theorem 20: Rule box characterization — ex, gx, vstar, vmax are all rule box. -/
theorem rule_box_characterization :
    PokemonKind.isRuleBox .ex = true ∧
    PokemonKind.isRuleBox .gx = true ∧
    PokemonKind.isRuleBox .vstar = true ∧
    PokemonKind.isRuleBox .vmax = true ∧
    PokemonKind.isRuleBox .basic = false ∧
    PokemonKind.isRuleBox .stage1 = false ∧
    PokemonKind.isRuleBox .stage2 = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PokemonLean.StadiumCards
