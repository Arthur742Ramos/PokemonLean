/-
  Stadium Cards — Pokemon TCG Stadium Card Mechanics
  ====================================================
  Stadium card mechanics: one Stadium in play at a time, new replaces old,
  symmetrical effects (both players), Path to the Peak (blocks Rule Box abilities),
  Collapsed Stadium (bench limit 4), Temple of Sinnoh (removes special energy effects),
-/

namespace PokemonLean.StadiumCards

-- ============================================================
-- §2  Core types
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
-- §3  Game state
-- ============================================================

/-- A simplified Pokemon in play. -/
structure PokemonInPlay where
  kind : PokemonKind
  hasAbility : Bool
  attachedEnergy : List EnergyType
  hp : Nat
  damage : Nat
  deriving DecidableEq, Repr

/-- Which player performed an action. -/
inductive Player where
  | p1 | p2
  deriving DecidableEq, Repr

/-- The field state relevant to stadium effects. -/
structure FieldState where
  activeStadium : Option StadiumCard
  player1Bench : List PokemonInPlay
  player2Bench : List PokemonInPlay
  player1Active : Option PokemonInPlay
  player2Active : Option PokemonInPlay
  player1BenchLimit : Nat
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
-- §4  Stadium effects as state transitions
-- ============================================================

/-- Apply Collapsed Stadium effect: reduce bench limits to 4. -/
def applyCollapsedStadium (s : FieldState) : FieldState :=
  { s with player1BenchLimit := min s.player1BenchLimit 4
           player2BenchLimit := min s.player2BenchLimit 4 }


/-- Temple of Sinnoh active predicate. -/
def templeOfSinnohActive (s : FieldState) : Prop :=
  s.activeStadium = some .templeOfSinnoh

/-- Collapsed Stadium active predicate. -/
def collapsedStadiumActive (s : FieldState) : Prop :=
  s.activeStadium = some .collapsedStadium


/-- Count special energy in a Pokemon's attached energy. -/
def countSpecialEnergy (pk : PokemonInPlay) : Nat :=
  pk.attachedEnergy.filter (fun e => e == .special) |>.length

/-- Effective energy under Temple of Sinnoh: special → colorless. -/
def effectiveEnergy (temple : Bool) (e : EnergyType) : EnergyType :=
  if temple then
    match e with
    | .special => .colorless
    | other => other
  else e

/-- Get bench limit for a player. -/
def benchLimit (s : FieldState) (p : Player) : Nat :=
  match p with
  | .p1 => s.player1BenchLimit
  | .p2 => s.player2BenchLimit

-- ============================================================
-- §5  Stadium replacement path steps
-- ============================================================

/-- Play a new stadium (may replace existing). -/
def playStadium (s : FieldState) (c : StadiumCard) : FieldState :=
  { s with activeStadium := some c }

/-- Remove the active stadium. -/
def removeStadium (s : FieldState) : FieldState :=
  { s with activeStadium := none }

/-- Stadium war: play → opponent plays → play again. -/
def stadiumWarSequence (s : FieldState) (c1 c2 c3 : StadiumCard) : FieldState :=
  playStadium (playStadium (playStadium s c1) c2) c3

-- ============================================================
-- §6  Core theorems
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
    (playStadium s new_).activeStadium = some new_ := by
  rfl

/-- Theorem 3: After playing a stadium, exactly that stadium is active. -/
theorem play_stadium_active (s : FieldState) (c : StadiumCard) :
    (playStadium s c).activeStadium = some c := by
  rfl

/-- Theorem 4: Stadium removal leaves no stadium. -/
theorem remove_stadium_none (s : FieldState) :
    (removeStadium s).activeStadium = none := by
  rfl


/-- Theorem 7: Path to the Peak does NOT negate basic Pokemon abilities. -/
theorem path_to_peak_spares_basic (pk : PokemonInPlay)
    (hk : pk.kind = .basic) :
    pk.kind.isRuleBox = false := by
  simp [PokemonKind.isRuleBox, hk]

/-- Theorem 8: Path to the Peak spares Stage 1 Pokemon. -/
theorem path_to_peak_spares_stage1 (pk : PokemonInPlay)
    (hk : pk.kind = .stage1) :
    pk.kind.isRuleBox = false := by
  simp [PokemonKind.isRuleBox, hk]

/-- Theorem 9: Temple of Sinnoh — special energy is not basic. -/
theorem temple_special_not_basic :
    EnergyType.isBasic .special = false := by
  rfl

/-- Theorem 10: Basic energy is unaffected by Temple of Sinnoh. -/
theorem temple_basic_unaffected (e : EnergyType) (h : e ≠ .special) :
    e.isBasic = true := by
  cases e <;> simp_all [EnergyType.isBasic]

/-- Theorem 11: Temple of Sinnoh converts special energy to colorless. -/
theorem temple_converts_special :
    effectiveEnergy true .special = .colorless := by
  rfl

/-- Theorem 12: Temple of Sinnoh doesn't affect basic energy types. -/
theorem temple_preserves_fire :
    effectiveEnergy true .fire = .fire := by
  rfl

/-- Theorem 13: Collapsed Stadium reduces bench to at most 4. -/
theorem collapsed_stadium_bench_limit (s : FieldState) :
    (applyCollapsedStadium s).player1BenchLimit ≤ 4 ∧
    (applyCollapsedStadium s).player2BenchLimit ≤ 4 := by
  simp [applyCollapsedStadium]
  exact ⟨Nat.min_le_right _ _, Nat.min_le_right _ _⟩

/-- Theorem 14: Collapsed Stadium is symmetrical (both players get limit 4). -/
theorem collapsed_stadium_symmetrical (s : FieldState)
    (h1 : s.player1BenchLimit = s.player2BenchLimit) :
    (applyCollapsedStadium s).player1BenchLimit =
    (applyCollapsedStadium s).player2BenchLimit := by
  simp [applyCollapsedStadium, h1]

/-- Theorem 15: Collapsed Stadium is idempotent. -/
theorem collapsed_stadium_idempotent (s : FieldState) :
    applyCollapsedStadium (applyCollapsedStadium s) = applyCollapsedStadium s := by
  unfold applyCollapsedStadium
  congr 1 <;> simp [Nat.min_assoc]

/-- Theorem 16: Playing same stadium twice yields same field state. -/
theorem play_same_stadium_idem (s : FieldState) (c : StadiumCard) :
    playStadium s c = playStadium (playStadium s c) c := by
  rfl

/-- Theorem 17: Replacing a stadium then removing it returns to no-stadium state. -/
theorem replace_then_remove (s : FieldState) (c : StadiumCard) :
    (removeStadium (playStadium s c)).activeStadium = none := by
  rfl


/-- Theorem 20: Playing two different stadiums — last one wins. -/
theorem last_stadium_wins (s : FieldState) (c₁ c₂ : StadiumCard) :
    (playStadium (playStadium s c₁) c₂).activeStadium = some c₂ := by
  rfl

/-- Theorem 21: Stadium war — after 3 plays, the 3rd stadium stands. -/
theorem stadium_war_last_wins (s : FieldState) (c1 c2 c3 : StadiumCard) :
    (stadiumWarSequence s c1 c2 c3).activeStadium = some c3 := by
  rfl

/-- Theorem 22: Default field has 5-slot bench. -/
theorem default_bench_limit :
    FieldState.default.player1BenchLimit = 5 ∧ FieldState.default.player2BenchLimit = 5 := by
  exact ⟨rfl, rfl⟩

/-- Theorem 23: Rule box characterization. -/
theorem rule_box_characterization :
    PokemonKind.isRuleBox .ex = true ∧
    PokemonKind.isRuleBox .gx = true ∧
    PokemonKind.isRuleBox .vstar = true ∧
    PokemonKind.isRuleBox .vmax = true ∧
    PokemonKind.isRuleBox .basic = false ∧
    PokemonKind.isRuleBox .stage1 = false ∧
    PokemonKind.isRuleBox .stage2 = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theorem 24: Bench limit preserved when playing non-collapsed stadium. -/
theorem bench_limit_preserved_on_play (s : FieldState) (c : StadiumCard) :
    (playStadium s c).player1BenchLimit = s.player1BenchLimit := by
  rfl

/-- Theorem 25: Stadium play preserves benches. -/
theorem bench_preserved_on_play (s : FieldState) (c : StadiumCard) :
    (playStadium s c).player1Bench = s.player1Bench ∧
    (playStadium s c).player2Bench = s.player2Bench := by
  exact ⟨rfl, rfl⟩

-- ============================================================
-- §7  Path-based stadium transition proofs
-- ============================================================


/-- Theorem 27: Symmetric path — playing for p1 then p2 yields same effect. -/
theorem stadium_symmetry_both_players (s : FieldState) (c : StadiumCard) :
    benchLimit (playStadium s c) .p1 = s.player1BenchLimit ∧
    benchLimit (playStadium s c) .p2 = s.player2BenchLimit := by
  simp [benchLimit, playStadium]


/-- Theorem 32: Collapsed Stadium after default reduces both benches to 4. -/
theorem collapsed_from_default :
    (applyCollapsedStadium FieldState.default).player1BenchLimit = 4 ∧
    (applyCollapsedStadium FieldState.default).player2BenchLimit = 4 := by
  exact ⟨rfl, rfl⟩

/-- Theorem 33: Already-reduced bench is unchanged by Collapsed Stadium. -/
theorem collapsed_no_change_if_small (s : FieldState)
    (h1 : s.player1BenchLimit ≤ 4) (h2 : s.player2BenchLimit ≤ 4) :
    (applyCollapsedStadium s).player1BenchLimit = s.player1BenchLimit ∧
    (applyCollapsedStadium s).player2BenchLimit = s.player2BenchLimit := by
  simp [applyCollapsedStadium]
  constructor <;> omega

/-- Theorem 34: countSpecialEnergy of a Pokemon with no energy is 0. -/
theorem no_energy_no_special (pk : PokemonInPlay) (h : pk.attachedEnergy = []) :
    countSpecialEnergy pk = 0 := by
  simp [countSpecialEnergy, h]


end PokemonLean.StadiumCards
