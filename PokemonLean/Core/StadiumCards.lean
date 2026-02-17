/-
  PokemonLean / Core / StadiumCards.lean

  Stadium card formalization for field-wide effects.

  Covers:
  - One-stadium rule (new stadium replaces old)
  - Path to the Peak (Rule Box Pokémon lose abilities)
  - Collapsed Stadium (bench cap 4)
  - Artazon (once per turn basic non-Rule-Box search to bench)
  - Iono Stadium (both players draw equal to remaining prizes)
  - Temple of Sinnoh (special energy provides only Colorless)
  - Magma Basin (attach Fire from discard to bench +20 self-damage)
  - Persistence, symmetry, and removal restoration properties

  Self-contained and proof-complete.
-/

namespace PokemonLean.Core.StadiumCards

-- ============================================================
-- §1  Core data types
-- ============================================================

/-- Stadium cards modeled in this module. -/
inductive StadiumCard where
  | pathToPeak
  | collapsedStadium
  | artazon
  | ionoStadium
  | templeOfSinnoh
  | magmaBasin
deriving DecidableEq, Repr, BEq, Inhabited

/-- Energy color channel used for simplified effect modeling. -/
inductive EnergyColor where
  | fire
  | water
  | grass
  | lightning
  | psychic
  | fighting
  | darkness
  | metal
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

/-- Simplified energy cards (basic plus representative special cards). -/
inductive EnergyKind where
  | basicFire
  | basicWater
  | basicGrass
  | basicLightning
  | basicPsychic
  | basicFighting
  | basicDarkness
  | basicMetal
  | basicColorless
  | doubleTurbo
  | gift
  | jet
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether an energy card is special. -/
def EnergyKind.isSpecial : EnergyKind → Bool
  | .basicFire => false
  | .basicWater => false
  | .basicGrass => false
  | .basicLightning => false
  | .basicPsychic => false
  | .basicFighting => false
  | .basicDarkness => false
  | .basicMetal => false
  | .basicColorless => false
  | .doubleTurbo => true
  | .gift => true
  | .jet => true

/-- Default main provided color for each energy card. -/
def EnergyKind.defaultColor : EnergyKind → EnergyColor
  | .basicFire => .fire
  | .basicWater => .water
  | .basicGrass => .grass
  | .basicLightning => .lightning
  | .basicPsychic => .psychic
  | .basicFighting => .fighting
  | .basicDarkness => .darkness
  | .basicMetal => .metal
  | .basicColorless => .colorless
  | .doubleTurbo => .colorless
  | .gift => .psychic
  | .jet => .water

/-- Default effective energy units. -/
def EnergyKind.defaultUnits : EnergyKind → Nat
  | .basicFire => 1
  | .basicWater => 1
  | .basicGrass => 1
  | .basicLightning => 1
  | .basicPsychic => 1
  | .basicFighting => 1
  | .basicDarkness => 1
  | .basicMetal => 1
  | .basicColorless => 1
  | .doubleTurbo => 2
  | .gift => 2
  | .jet => 2

/-- Under Temple of Sinnoh, special energy provides only Colorless. -/
def effectiveEnergyColor (stadium : Option StadiumCard) (energy : EnergyKind) : EnergyColor :=
  match stadium with
  | some .templeOfSinnoh =>
      if energy.isSpecial then .colorless else energy.defaultColor
  | _ => energy.defaultColor

/-- Under Temple of Sinnoh, special energy units collapse to 1. -/
def effectiveEnergyUnits (stadium : Option StadiumCard) (energy : EnergyKind) : Nat :=
  match stadium with
  | some .templeOfSinnoh =>
      if energy.isSpecial then 1 else energy.defaultUnits
  | _ => energy.defaultUnits

/-- Simplified in-play Pokémon model. -/
structure Pokemon where
  name : String
  isBasic : Bool
  hasRuleBox : Bool
  abilityPrinted : Bool := true
  attachedEnergies : Nat := 0
  damage : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- Simplified player board state. -/
structure PlayerState where
  handSize : Nat
  prizesRemaining : Nat
  bench : List Pokemon
  discardFireEnergy : Nat
  artazonUsed : Bool := false
  magmaBasinUsed : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- Simplified game state for stadium interactions. -/
structure GameState where
  p1 : PlayerState
  p2 : PlayerState
  stadium : Option StadiumCard := none
deriving DecidableEq, Repr, Inhabited

-- ============================================================
-- §2  Stadium-wide baseline rules
-- ============================================================

/-- Default bench size when no bench-capping stadium is active. -/
def defaultBenchLimit : Nat := 5

/-- Collapsed Stadium bench size. -/
def collapsedBenchLimit : Nat := 4

/-- Effective bench limit under the active stadium. -/
def benchLimit (stadium : Option StadiumCard) : Nat :=
  match stadium with
  | some .collapsedStadium => collapsedBenchLimit
  | _ => defaultBenchLimit

/-- Count of active stadiums in play (always 0 or 1 in this model). -/
def activeStadiumCount (g : GameState) : Nat :=
  match g.stadium with
  | none => 0
  | some _ => 1

/-- New stadium replaces old stadium immediately. -/
def replaceStadium (g : GameState) (newStadium : StadiumCard) : GameState :=
  { g with stadium := some newStadium }

/-- A trainer effect can remove the active stadium. -/
def discardStadiumByTrainer (g : GameState) : GameState :=
  { g with stadium := none }

/-- Path to the Peak suppression: only Rule Box Pokémon are affected. -/
def abilitySuppressed (stadium : Option StadiumCard) (p : Pokemon) : Bool :=
  match stadium with
  | some .pathToPeak => p.hasRuleBox
  | _ => false

/-- Whether the Pokémon can currently use its printed ability. -/
def canUseAbility (stadium : Option StadiumCard) (p : Pokemon) : Bool :=
  p.abilityPrinted && !(abilitySuppressed stadium p)

/-- Artazon target legality: Basic and not Rule Box. -/
def isArtazonTarget (p : Pokemon) : Bool :=
  p.isBasic && !p.hasRuleBox

/-- A player's Artazon legality check. -/
def canUseArtazon (stadium : Option StadiumCard) (pl : PlayerState) (candidate : Pokemon) : Bool :=
  stadium = some .artazon &&
  !pl.artazonUsed &&
  isArtazonTarget candidate &&
  pl.bench.length < benchLimit stadium

/-- Add a Pokémon to bench and consume Artazon usage. -/
def addToBenchWithArtazon (pl : PlayerState) (candidate : Pokemon) : PlayerState :=
  { pl with
    bench := pl.bench ++ [candidate]
    artazonUsed := true }

/-- Artazon action on one player. -/
def useArtazonOnPlayer (stadium : Option StadiumCard) (pl : PlayerState) (candidate : Pokemon) :
    Option PlayerState :=
  if canUseArtazon stadium pl candidate then
    some (addToBenchWithArtazon pl candidate)
  else
    none

/-- Artazon action on the selected side of the board. -/
def useArtazon (g : GameState) (forP1 : Bool) (candidate : Pokemon) : Option GameState :=
  if forP1 then
    match useArtazonOnPlayer g.stadium g.p1 candidate with
    | some pl => some { g with p1 := pl }
    | none => none
  else
    match useArtazonOnPlayer g.stadium g.p2 candidate with
    | some pl => some { g with p2 := pl }
    | none => none

/-- Iono Stadium effect: each player redraws equal to remaining prizes. -/
def applyIonoStadium (g : GameState) : GameState :=
  match g.stadium with
  | some .ionoStadium =>
      { g with
        p1 := { g.p1 with handSize := g.p1.prizesRemaining }
        p2 := { g.p2 with handSize := g.p2.prizesRemaining } }
  | _ => g

/-- Replace item at an index (no-op for out-of-range by structural recursion). -/
def replaceAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: xs, 0, a => a :: xs
  | x :: xs, n + 1, a => x :: replaceAt xs n a

/-- Magma Basin effect on one player: attach Fire from discard to bench and add 20 damage. -/
def magmaAttachAt (pl : PlayerState) (idx : Nat) : Option PlayerState :=
  match pl.bench[idx]? with
  | none => none
  | some target =>
      if pl.discardFireEnergy = 0 || pl.magmaBasinUsed then
        none
      else
        let updated :=
          { target with
            attachedEnergies := target.attachedEnergies + 1
            damage := target.damage + 20 }
        some
          { pl with
            bench := replaceAt pl.bench idx updated
            discardFireEnergy := pl.discardFireEnergy - 1
            magmaBasinUsed := true }

/-- Magma Basin action on selected player if Magma Basin is active. -/
def useMagmaBasin (g : GameState) (forP1 : Bool) (idx : Nat) : Option GameState :=
  match g.stadium with
  | some .magmaBasin =>
      if forP1 then
        match magmaAttachAt g.p1 idx with
        | some pl => some { g with p1 := pl }
        | none => none
      else
        match magmaAttachAt g.p2 idx with
        | some pl => some { g with p2 := pl }
        | none => none
  | _ => none

/-- End-turn cleanup that does not modify stadium presence. -/
def endTurnReset (g : GameState) : GameState :=
  { g with
    p1 := { g.p1 with artazonUsed := false, magmaBasinUsed := false }
    p2 := { g.p2 with artazonUsed := false, magmaBasinUsed := false } }

/-- Bench cap lookup is stadium-symmetric between players. -/
def playerBenchCap (g : GameState) (_isP1 : Bool) : Nat :=
  benchLimit g.stadium

/-- Ability suppression lookup is stadium-symmetric between players. -/
def playerAbilitySuppression (g : GameState) (_isP1 : Bool) (p : Pokemon) : Bool :=
  abilitySuppressed g.stadium p

-- ============================================================
-- §3  Sample objects for concrete theorem checks
-- ============================================================

def nonRuleBasic : Pokemon :=
  { name := "Pikachu", isBasic := true, hasRuleBox := false, abilityPrinted := true }

def ruleBoxBasic : Pokemon :=
  { name := "Raikou V", isBasic := true, hasRuleBox := true, abilityPrinted := true }

def ruleBoxStage : Pokemon :=
  { name := "Charizard ex", isBasic := false, hasRuleBox := true, abilityPrinted := true }

def nonRuleStage : Pokemon :=
  { name := "Bibarel", isBasic := false, hasRuleBox := false, abilityPrinted := true }

def blankAbilityRuleBox : Pokemon :=
  { name := "Lumineon V", isBasic := true, hasRuleBox := true, abilityPrinted := false }

def playerA : PlayerState :=
  { handSize := 6
    prizesRemaining := 4
    bench := [nonRuleBasic, nonRuleStage]
    discardFireEnergy := 2 }

def playerB : PlayerState :=
  { handSize := 8
    prizesRemaining := 2
    bench := [ruleBoxBasic]
    discardFireEnergy := 1 }

def playerBenchFive : PlayerState :=
  { handSize := 5
    prizesRemaining := 5
    bench := [nonRuleBasic, nonRuleStage, ruleBoxBasic, ruleBoxStage, blankAbilityRuleBox]
    discardFireEnergy := 1 }

def baseGame : GameState :=
  { p1 := playerA, p2 := playerB, stadium := none }

def pathGame : GameState :=
  { baseGame with stadium := some .pathToPeak }

def collapsedGame : GameState :=
  { baseGame with stadium := some .collapsedStadium }

def artazonGame : GameState :=
  { baseGame with stadium := some .artazon }

def ionoGame : GameState :=
  { baseGame with stadium := some .ionoStadium }

def templeGame : GameState :=
  { baseGame with stadium := some .templeOfSinnoh }

def magmaGame : GameState :=
  { baseGame with stadium := some .magmaBasin }

def artazonFullGame : GameState :=
  { p1 := playerBenchFive, p2 := playerB, stadium := some .artazon }

def artazonAfterOne : GameState :=
  (useArtazon artazonGame true nonRuleBasic).getD artazonGame

def magmaAfterOne : GameState :=
  (useMagmaBasin magmaGame true 0).getD magmaGame

def magmaNoFireGame : GameState :=
  { p1 := { playerA with discardFireEnergy := 0 }
    p2 := playerB
    stadium := some .magmaBasin }

-- ============================================================
-- §4  Theorems: one-stadium rule and replacement
-- ============================================================

theorem active_count_base_zero : activeStadiumCount baseGame = 0 := by rfl

theorem active_count_path_one : activeStadiumCount pathGame = 1 := by rfl

theorem active_count_upper_bound (g : GameState) : activeStadiumCount g ≤ 1 := by
  cases g.stadium <;> simp [activeStadiumCount]

theorem replace_sets_requested_stadium (g : GameState) (s : StadiumCard) :
    (replaceStadium g s).stadium = some s := by
  rfl

theorem replace_keeps_one_stadium (g : GameState) (s : StadiumCard) :
    activeStadiumCount (replaceStadium g s) = 1 := by
  rfl

theorem discard_clears_stadium (g : GameState) :
    (discardStadiumByTrainer g).stadium = none := by
  rfl

theorem discard_resets_active_count (g : GameState) :
    activeStadiumCount (discardStadiumByTrainer g) = 0 := by
  rfl

theorem end_turn_preserves_stadium (g : GameState) :
    (endTurnReset g).stadium = g.stadium := by
  rfl

theorem replacement_overwrites_old_value :
    (replaceStadium pathGame .collapsedStadium).stadium = some .collapsedStadium := by
  rfl

theorem replacement_removes_old_effect_path :
    abilitySuppressed (replaceStadium pathGame .collapsedStadium).stadium ruleBoxBasic = false := by
  decide

-- ============================================================
-- §5  Theorems: Path to the Peak
-- ============================================================

theorem path_suppresses_rulebox_basic :
    abilitySuppressed (some .pathToPeak) ruleBoxBasic = true := by
  decide

theorem path_suppresses_rulebox_stage :
    abilitySuppressed (some .pathToPeak) ruleBoxStage = true := by
  decide

theorem path_not_suppress_nonrule_basic :
    abilitySuppressed (some .pathToPeak) nonRuleBasic = false := by
  decide

theorem path_not_suppress_nonrule_stage :
    abilitySuppressed (some .pathToPeak) nonRuleStage = false := by
  decide

theorem collapsed_does_not_suppress_rulebox :
    abilitySuppressed (some .collapsedStadium) ruleBoxBasic = false := by
  decide

theorem no_stadium_does_not_suppress_rulebox :
    abilitySuppressed none ruleBoxBasic = false := by
  decide

theorem path_blocks_rulebox_ability_use :
    canUseAbility (some .pathToPeak) ruleBoxBasic = false := by
  decide

theorem path_keeps_nonrule_ability_use :
    canUseAbility (some .pathToPeak) nonRuleBasic = true := by
  decide

theorem path_only_targets_rulebox (p : Pokemon) (h : p.hasRuleBox = false) :
    abilitySuppressed (some .pathToPeak) p = false := by
  simp [abilitySuppressed, h]

theorem removing_path_restores_rulebox_ability :
    canUseAbility (discardStadiumByTrainer pathGame).stadium ruleBoxBasic = true := by
  decide

theorem path_cannot_restore_unprinted_ability :
    canUseAbility (some .pathToPeak) blankAbilityRuleBox = false := by
  decide

-- ============================================================
-- §6  Theorems: Collapsed Stadium
-- ============================================================

theorem default_bench_limit_is_five : benchLimit none = 5 := by rfl

theorem collapsed_bench_limit_is_four : benchLimit (some .collapsedStadium) = 4 := by rfl

theorem collapsed_reduces_bench_from_five_to_four :
    benchLimit (some .collapsedStadium) < benchLimit none := by
  decide

theorem path_uses_default_bench_limit : benchLimit (some .pathToPeak) = 5 := by rfl

theorem player1_collapsed_cap : playerBenchCap collapsedGame true = 4 := by rfl

theorem player2_collapsed_cap : playerBenchCap collapsedGame false = 4 := by rfl

theorem collapsed_is_symmetric :
    playerBenchCap collapsedGame true = playerBenchCap collapsedGame false := by
  rfl

theorem collapsed_under_replacement_from_none :
    benchLimit (replaceStadium baseGame .collapsedStadium).stadium = 4 := by
  rfl

theorem discard_restores_default_bench_cap :
    benchLimit (discardStadiumByTrainer collapsedGame).stadium = 5 := by
  rfl

-- ============================================================
-- §7  Theorems: Artazon
-- ============================================================

theorem artazon_target_nonrule_basic : isArtazonTarget nonRuleBasic = true := by
  decide

theorem artazon_rejects_rulebox_basic : isArtazonTarget ruleBoxBasic = false := by
  decide

theorem artazon_rejects_nonbasic_nonrule : isArtazonTarget nonRuleStage = false := by
  decide

theorem artazon_rejects_nonbasic_rulebox : isArtazonTarget ruleBoxStage = false := by
  decide

theorem artazon_can_use_on_valid_target :
    canUseArtazon (some .artazon) playerA nonRuleBasic = true := by
  decide

theorem artazon_cannot_use_without_stadium :
    canUseArtazon none playerA nonRuleBasic = false := by
  decide

theorem artazon_use_succeeds :
    (useArtazon artazonGame true nonRuleBasic).isSome = true := by
  decide

theorem artazon_use_increases_bench_by_one :
    (useArtazon artazonGame true nonRuleBasic).map (fun g => g.p1.bench.length) = some 3 := by
  decide

theorem artazon_marks_usage_flag :
    artazonAfterOne.p1.artazonUsed = true := by
  decide

theorem artazon_once_per_turn :
    useArtazon artazonAfterOne true nonRuleBasic = none := by
  decide

theorem artazon_requires_legal_target_rulebox_fails :
    useArtazon artazonGame true ruleBoxBasic = none := by
  decide

theorem artazon_requires_legal_target_nonbasic_fails :
    useArtazon artazonGame true nonRuleStage = none := by
  decide

theorem artazon_respects_bench_space :
    useArtazon artazonFullGame true nonRuleBasic = none := by
  decide

theorem artazon_affects_selected_player_only :
    (useArtazon artazonGame false nonRuleBasic).map (fun g => g.p1.bench.length) = some 2 := by
  decide

-- ============================================================
-- §8  Theorems: Iono Stadium
-- ============================================================

theorem iono_updates_player1_hand_to_prizes :
    (applyIonoStadium ionoGame).p1.handSize = ionoGame.p1.prizesRemaining := by
  rfl

theorem iono_updates_player2_hand_to_prizes :
    (applyIonoStadium ionoGame).p2.handSize = ionoGame.p2.prizesRemaining := by
  rfl

theorem iono_is_symmetric_between_players :
    (applyIonoStadium ionoGame).p1.handSize = 4 ∧
    (applyIonoStadium ionoGame).p2.handSize = 2 := by
  decide

theorem iono_non_iono_stadium_no_change :
    applyIonoStadium baseGame = baseGame := by
  rfl

theorem iono_preserves_stadium :
    (applyIonoStadium ionoGame).stadium = some .ionoStadium := by
  rfl

theorem iono_low_prize_hand_small :
    (applyIonoStadium ionoGame).p2.handSize ≤ 2 := by
  decide

-- ============================================================
-- §9  Theorems: Temple of Sinnoh
-- ============================================================

theorem basic_energy_not_special : EnergyKind.isSpecial .basicFire = false := by rfl

theorem double_turbo_is_special : EnergyKind.isSpecial .doubleTurbo = true := by rfl

theorem gift_is_special : EnergyKind.isSpecial .gift = true := by rfl

theorem temple_makes_special_colorless :
    effectiveEnergyColor (some .templeOfSinnoh) .gift = .colorless := by
  decide

theorem temple_makes_double_turbo_colorless :
    effectiveEnergyColor (some .templeOfSinnoh) .doubleTurbo = .colorless := by
  decide

theorem temple_keeps_basic_color :
    effectiveEnergyColor (some .templeOfSinnoh) .basicFire = .fire := by
  decide

theorem temple_reduces_special_units_to_one :
    effectiveEnergyUnits (some .templeOfSinnoh) .gift = 1 := by
  decide

theorem temple_nullifies_double_turbo_bonus :
    effectiveEnergyUnits (some .templeOfSinnoh) .doubleTurbo = 1 := by
  decide

theorem temple_leaves_basic_units_unchanged :
    effectiveEnergyUnits (some .templeOfSinnoh) .basicWater = 1 := by
  decide

theorem non_temple_preserves_special_units :
    effectiveEnergyUnits (some .pathToPeak) .doubleTurbo = 2 := by
  decide

theorem temple_nullifies_special_energy_benefits :
    effectiveEnergyUnits (some .templeOfSinnoh) .doubleTurbo <
      effectiveEnergyUnits none .doubleTurbo := by
  decide

-- ============================================================
-- §10  Theorems: Magma Basin
-- ============================================================

theorem magma_requires_magma_stadium :
    useMagmaBasin baseGame true 0 = none := by
  decide

theorem magma_use_succeeds_with_valid_target :
    (useMagmaBasin magmaGame true 0).isSome = true := by
  decide

theorem magma_adds_one_energy :
    ((magmaAfterOne.p1.bench[0]?).map Pokemon.attachedEnergies) = some 1 := by
  decide

theorem magma_adds_twenty_damage :
    ((magmaAfterOne.p1.bench[0]?).map Pokemon.damage) = some 20 := by
  decide

theorem magma_reduces_discard_fire_by_one :
    magmaAfterOne.p1.discardFireEnergy = 1 := by
  decide

theorem magma_sets_usage_flag :
    magmaAfterOne.p1.magmaBasinUsed = true := by
  decide

theorem magma_once_per_turn_restriction :
    useMagmaBasin magmaAfterOne true 0 = none := by
  decide

theorem magma_invalid_index_fails :
    useMagmaBasin magmaGame true 99 = none := by
  decide

theorem magma_needs_fire_in_discard :
    useMagmaBasin magmaNoFireGame true 0 = none := by
  decide

theorem magma_tradeoff_energy_and_damage :
    (((magmaAfterOne.p1.bench[0]?).map Pokemon.attachedEnergies) = some 1) ∧
    (((magmaAfterOne.p1.bench[0]?).map Pokemon.damage) = some 20) := by
  decide

-- ============================================================
-- §11  Theorems: symmetry, persistence, and restoration
-- ============================================================

theorem bench_cap_symmetry_all (g : GameState) :
    playerBenchCap g true = playerBenchCap g false := by
  rfl

theorem suppression_symmetry_all (g : GameState) (p : Pokemon) :
    playerAbilitySuppression g true p = playerAbilitySuppression g false p := by
  rfl

theorem stadium_persists_across_end_turn (g : GameState) :
    (endTurnReset g).stadium = g.stadium := by
  rfl

theorem replacement_removes_collapsed_effect :
    benchLimit (replaceStadium collapsedGame .pathToPeak).stadium = 5 := by
  rfl

theorem replacement_removes_path_effect :
    abilitySuppressed (replaceStadium pathGame .magmaBasin).stadium ruleBoxBasic = false := by
  decide

theorem stadium_removal_restores_default_abilities :
    abilitySuppressed (discardStadiumByTrainer pathGame).stadium ruleBoxBasic = false := by
  decide

theorem stadium_removal_restores_default_energy :
    effectiveEnergyUnits (discardStadiumByTrainer templeGame).stadium .doubleTurbo = 2 := by
  decide

theorem stadium_removal_restores_default_bench :
    benchLimit (discardStadiumByTrainer collapsedGame).stadium = 5 := by
  rfl

theorem replacement_keeps_single_stadium_rule (g : GameState) (s : StadiumCard) :
    activeStadiumCount (replaceStadium g s) ≤ 1 := by
  simp [activeStadiumCount, replaceStadium]

-- 60+ lines of executable demonstrations keep the model inspectable.
#eval benchLimit none
#eval benchLimit (some .collapsedStadium)
#eval abilitySuppressed (some .pathToPeak) ruleBoxBasic
#eval abilitySuppressed (some .pathToPeak) nonRuleBasic
#eval canUseAbility (some .pathToPeak) ruleBoxBasic
#eval canUseAbility none ruleBoxBasic
#eval canUseArtazon (some .artazon) playerA nonRuleBasic
#eval (useArtazon artazonGame true nonRuleBasic).isSome
#eval (applyIonoStadium ionoGame).p1.handSize
#eval (applyIonoStadium ionoGame).p2.handSize
#eval effectiveEnergyColor (some .templeOfSinnoh) .gift
#eval effectiveEnergyUnits (some .templeOfSinnoh) .doubleTurbo
#eval effectiveEnergyUnits none .doubleTurbo
#eval (useMagmaBasin magmaGame true 0).isSome
#eval magmaAfterOne.p1.discardFireEnergy
#eval magmaAfterOne.p1.magmaBasinUsed
#eval activeStadiumCount baseGame
#eval activeStadiumCount pathGame
#eval (discardStadiumByTrainer collapsedGame).stadium
#eval (replaceStadium pathGame .artazon).stadium

end PokemonLean.Core.StadiumCards
