import PokemonLean.Basic
import PokemonLean.Core.Types
import PokemonLean.Archetypes

namespace PokemonLean.Matchup

open PokemonLean

-- ============================================================================
-- DECK ARCHETYPES
-- ============================================================================

/-- Reuse the shared archetype type. -/
abbrev Archetype := PokemonLean.Archetypes.Archetype

/-- Numeric encoding for archetypes. -/
def Archetype.toNat : Archetype → Nat
  | .aggro    => 0
  | .control  => 1
  | .combo    => 2
  | .midrange => 3

theorem archetype_toNat_injective (a b : Archetype) (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp [Archetype.toNat] at h <;> rfl

-- ============================================================================
-- MATCHUP ADVANTAGE MATRIX
-- ============================================================================

/-- Advantage level in a matchup. -/
inductive Advantage
  | favored    -- strong advantage
  | slight     -- minor advantage
  | even       -- 50-50
  | unfavored  -- disadvantage
  deriving Repr, BEq, DecidableEq

/-- Numeric advantage score (out of 100 = win percentage estimate). -/
def Advantage.score : Advantage → Nat
  | .favored   => 65
  | .slight    => 55
  | .even      => 50
  | .unfavored => 35

/-- The matchup advantage matrix: given attacker archetype vs defender archetype.
    Rock-paper-scissors: aggro > control > combo > midrange > aggro,
    with combo also beating aggro. -/
def archetypeAdvantage : Archetype → Archetype → Advantage
  -- Aggro beats control (too fast for disruption)
  | .aggro, .control  => .favored
  -- Aggro loses to combo (combo assembles and overwhelms)
  | .aggro, .combo    => .unfavored
  -- Aggro loses to midrange (midrange adapts)
  | .aggro, .midrange => .unfavored
  -- Control beats combo (disrupts combo pieces)
  | .control, .combo    => .favored
  -- Control loses to aggro (too slow)
  | .control, .aggro    => .unfavored
  -- Control loses to midrange (midrange grinds through)
  | .control, .midrange => .unfavored
  -- Combo beats aggro (explosive turns)
  | .combo, .aggro    => .favored
  -- Combo loses to control
  | .combo, .control  => .unfavored
  -- Combo loses to midrange (midrange handles pivots)
  | .combo, .midrange => .unfavored
  -- Midrange beats aggro (sustain)
  | .midrange, .aggro    => .favored
  -- Midrange beats control (grinds through)
  | .midrange, .control  => .favored
  -- Midrange beats combo (flexible response)
  | .midrange, .combo    => .favored
  -- All mirrors are even
  | .aggro, .aggro       => .even
  | .control, .control   => .even
  | .combo, .combo       => .even
  | .midrange, .midrange => .even

-- ============================================================================
-- DECK CLASSIFICATION
-- ============================================================================

/-- Average HP of cards in a deck. -/
def avgHP (deck : List Card) : Nat :=
  match deck with
  | [] => 0
  | _ => (deck.foldl (fun acc c => acc + c.hp) 0) / deck.length

/-- Average base damage of the first attack across all Pokémon cards. -/
def avgDamage (deck : List Card) : Nat :=
  let pokemonCards := deck.filter (fun c => !c.attacks.isEmpty)
  match pokemonCards with
  | [] => 0
  | _ =>
    let totalDmg := pokemonCards.foldl (fun acc c =>
      match c.attacks with
      | [] => acc
      | a :: _ => acc + a.baseDamage) 0
    totalDmg / pokemonCards.length

/-- Classify deck archetype: high damage + low HP → aggro, low damage + high HP → control, etc. -/
def deckArchetype (deck : List Card) : Archetype :=
  let hp := avgHP deck
  let dmg := avgDamage deck
  if dmg ≥ 80 && hp ≤ 100 then .aggro
  else if dmg ≤ 30 && hp ≥ 100 then .control
  else if dmg ≥ 100 then .combo
  else .midrange

/-- Matchup score between two decks (0–100 scale, from deck1's perspective). -/
def matchupScore (deck1 deck2 : List Card) : Nat :=
  (archetypeAdvantage (deckArchetype deck1) (deckArchetype deck2)).score

-- ============================================================================
-- METAGAME SHARE & EXPECTED WIN RATE
-- ============================================================================

/-- A metagame entry: archetype with share percentage (out of 100). -/
structure MetaEntry where
  archetype : Archetype
  share : Nat  -- percentage out of 100
  deriving Repr, BEq, DecidableEq

/-- Expected win rate of an archetype against a metagame (scaled by 100 for precision).
    Returns a value that should be divided by 100 to get the actual percentage. -/
def expectedWinRate (arch : Archetype) (entries : List MetaEntry) : Nat :=
  entries.foldl (fun acc entry =>
    acc + entry.share * (archetypeAdvantage arch entry.archetype).score) 0

/-- Total metagame share (should sum to 100 for a valid metagame). -/
def totalMetaShare (entries : List MetaEntry) : Nat :=
  entries.foldl (fun acc entry => acc + entry.share) 0

-- ============================================================================
-- ROCK-PAPER-SCISSORS STRUCTURE THEOREMS
-- ============================================================================


-- The reverse directions.


-- ============================================================================
-- MIRROR MATCH THEOREMS
-- ============================================================================


/-- All mirrors are even. -/
theorem mirror_always_even (a : Archetype) :
    archetypeAdvantage a a = .even := by
  cases a <;> rfl

-- ============================================================================
-- ADVANTAGE SCORE THEOREMS
-- ============================================================================

@[simp] theorem advantage_score_favored : Advantage.favored.score = 65 := rfl
@[simp] theorem advantage_score_slight : Advantage.slight.score = 55 := rfl
@[simp] theorem advantage_score_even : Advantage.even.score = 50 := rfl
@[simp] theorem advantage_score_unfavored : Advantage.unfavored.score = 35 := rfl

theorem advantage_score_pos (a : Advantage) : 0 < a.score := by
  cases a <;> simp [Advantage.score]

theorem advantage_score_le_100 (a : Advantage) : a.score ≤ 100 := by
  cases a <;> simp [Advantage.score]


-- ============================================================================
-- MATCHUP SCORE THEOREMS
-- ============================================================================

theorem matchupScore_mirror (deck : List Card) :
    matchupScore deck deck = 50 := by
  simp [matchupScore, mirror_always_even]

theorem matchupScore_pos (deck1 deck2 : List Card) :
    0 < matchupScore deck1 deck2 := by
  simp [matchupScore]
  exact advantage_score_pos _

theorem matchupScore_le_100 (deck1 deck2 : List Card) :
    matchupScore deck1 deck2 ≤ 100 := by
  simp [matchupScore]
  exact advantage_score_le_100 _

-- ============================================================================
-- CLASSIFICATION THEOREMS
-- ============================================================================


theorem deckArchetype_nil : deckArchetype [] = .midrange := by
  simp [deckArchetype, avgHP, avgDamage]

-- ============================================================================
-- METAGAME THEOREMS
-- ============================================================================

theorem expectedWinRate_nil (arch : Archetype) :
    expectedWinRate arch [] = 0 := by
  simp [expectedWinRate]

theorem totalMetaShare_nil : totalMetaShare [] = 0 := by
  simp [totalMetaShare]

-- ============================================================================
-- ADVANTAGE SYMMETRY PROPERTIES
-- ============================================================================

/-- If A is favored vs B, then B is unfavored vs A (for the core triangle). -/
theorem aggro_control_antisymmetric :
    archetypeAdvantage .aggro .control = .favored ∧
    archetypeAdvantage .control .aggro = .unfavored := by
  exact ⟨rfl, rfl⟩

theorem control_combo_antisymmetric :
    archetypeAdvantage .control .combo = .favored ∧
    archetypeAdvantage .combo .control = .unfavored := by
  exact ⟨rfl, rfl⟩

theorem combo_aggro_antisymmetric :
    archetypeAdvantage .combo .aggro = .favored ∧
    archetypeAdvantage .aggro .combo = .unfavored := by
  exact ⟨rfl, rfl⟩

/-- No archetype has a favored matchup against itself. -/
theorem no_self_favored (a : Archetype) :
    archetypeAdvantage a a ≠ .favored := by
  cases a <;> simp [archetypeAdvantage]

/-- No archetype has an unfavored matchup against itself. -/
theorem no_self_unfavored (a : Archetype) :
    archetypeAdvantage a a ≠ .unfavored := by
  cases a <;> simp [archetypeAdvantage]

/-- Every archetype has at least one favored matchup. -/
theorem every_archetype_has_advantage (a : Archetype) :
    ∃ b : Archetype, archetypeAdvantage a b = .favored := by
  cases a with
  | aggro    => exact ⟨.control, rfl⟩
  | control  => exact ⟨.combo, rfl⟩
  | combo    => exact ⟨.aggro, rfl⟩
  | midrange => exact ⟨.aggro, rfl⟩

/-- Every non-midrange archetype has at least one unfavored matchup. -/
theorem every_non_midrange_has_weakness (a : Archetype) (h : a ≠ .midrange) :
    ∃ b : Archetype, archetypeAdvantage a b = .unfavored := by
  cases a with
  | aggro    => exact ⟨.combo, rfl⟩
  | control  => exact ⟨.aggro, rfl⟩
  | combo    => exact ⟨.control, rfl⟩
  | midrange => exact absurd rfl h

/-- The advantage score is always one of the four canonical values. -/
theorem advantage_score_values (a : Advantage) :
    a.score = 35 ∨ a.score = 50 ∨ a.score = 55 ∨ a.score = 65 := by
  cases a <;> simp [Advantage.score]

/-- Mirror matchup scores are always 50. -/
theorem mirror_score_50 (a : Archetype) :
    (archetypeAdvantage a a).score = 50 := by
  cases a <;> rfl

end PokemonLean.Matchup
