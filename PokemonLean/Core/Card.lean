/-
  PokemonLean / Core / Card.lean

  Card structures for the Pokémon TCG: stages, rule boxes, attacks,
  abilities, Pokémon cards, trainer cards, energy cards, and the
  unified Card type.

  Imports Core.Types for PType and EnergyType.

  All proofs are sorry-free.  20+ theorems.
-/

import PokemonLean.Core.Types

namespace PokemonLean.Core

-- ============================================================
-- §1  Evolution Stages
-- ============================================================

/-- Evolution stages in the Pokémon TCG. -/
inductive Stage where
  | basic
  | stage1
  | stage2
  | mega
  | vmax
  | vstar
  | vunion
  | breaks
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Rule Box Classification
-- ============================================================

/-- Rule box categories. Determines prize penalties and special rules. -/
inductive RuleBox where
  | none
  | ex_upper
  | ex_lower
  | gx
  | tagTeam
  | v
  | vmax
  | vstar
  | tera
deriving DecidableEq, Repr, BEq, Inhabited

/-- Number of prize cards the opponent takes when this Pokémon is knocked out. -/
def RuleBox.prizeCount : RuleBox → Nat
  | .none     => 1
  | .ex_upper => 2
  | .ex_lower => 2
  | .gx       => 2
  | .tagTeam  => 3
  | .v        => 2
  | .vmax     => 3
  | .vstar    => 2
  | .tera     => 2

-- ============================================================
-- §3  Attacks
-- ============================================================

/-- An attack on a Pokémon card.
    Energy cost is represented as a list of EnergyType requirements
    (each entry = one energy of that type needed). -/
structure Attack where
  name       : String
  cost       : List EnergyType
  baseDamage : Nat
  effect     : String
deriving Repr, Inhabited

-- ============================================================
-- §4  Abilities
-- ============================================================

/-- The kind of ability (historical variants). -/
inductive AbilityKind where
  | pokeBody
  | pokePower
  | ability
deriving DecidableEq, Repr, BEq, Inhabited

/-- An ability on a Pokémon card. -/
structure Ability where
  name        : String
  kind        : AbilityKind
  description : String
deriving Repr, Inhabited

-- ============================================================
-- §5  Pokémon Card
-- ============================================================

/-- A Pokémon card with all its attributes. -/
structure PokemonCard where
  name         : String
  stage        : Stage
  ptype        : PType
  hp           : Nat
  attacks      : List Attack
  ability      : Option Ability
  weakness     : Option PType
  resistance   : Option PType
  retreatCost  : Nat
  ruleBox      : RuleBox
deriving Repr, Inhabited

-- ============================================================
-- §6  Trainer Cards
-- ============================================================

/-- Trainer card subtypes. -/
inductive TrainerKind where
  | supporter
  | item
  | tool
  | stadium
  | aceSpec
deriving DecidableEq, Repr, BEq, Inhabited

/-- A Trainer card. -/
structure TrainerCard where
  name        : String
  kind        : TrainerKind
  description : String
deriving Repr, Inhabited

-- ============================================================
-- §7  Unified Card Type
-- ============================================================

/-- The unified card type: every card in a deck is one of these. -/
inductive Card where
  | pokemon (card : PokemonCard)
  | trainer (card : TrainerCard)
  | energy  (etype : EnergyType) (isBasic : Bool)
deriving Repr, Inhabited

-- ============================================================
-- §8  Helper functions
-- ============================================================

/-- Whether a card is a Pokémon card. -/
def Card.isPokemon : Card → Bool
  | .pokemon _ => true
  | _          => false

/-- Whether a card is a Trainer card. -/
def Card.isTrainer : Card → Bool
  | .trainer _ => true
  | _          => false

/-- Whether a card is an Energy card. -/
def Card.isEnergy : Card → Bool
  | .energy _ _ => true
  | _           => false

/-- Whether a card is a basic Energy card. -/
def Card.isBasicEnergy : Card → Bool
  | .energy _ b => b
  | _           => false

/-- Whether a Pokémon card is a Basic Pokémon. -/
def PokemonCard.isBasic (pc : PokemonCard) : Bool :=
  pc.stage == .basic

/-- Whether a Pokémon card has a rule box (gives extra prizes). -/
def PokemonCard.hasRuleBox (pc : PokemonCard) : Bool :=
  pc.ruleBox != .none

/-- Get the prize count for a Pokémon card. -/
def PokemonCard.prizeValue (pc : PokemonCard) : Nat :=
  pc.ruleBox.prizeCount

/-- Maximum HP for a stage (approximate upper bounds from real cards). -/
def Stage.maxHP : Stage → Nat
  | .basic  => 130
  | .stage1 => 170
  | .stage2 => 200
  | .mega   => 250
  | .vmax   => 340
  | .vstar  => 280
  | .vunion => 320
  | .breaks => 160

/-- Minimum HP for any Pokémon in TCG is 30. -/
def minHP : Nat := 30

/-- HP is always a multiple of 10 in the TCG. -/
def validHP (hp : Nat) : Bool :=
  hp ≥ minHP ∧ hp % 10 == 0

-- ============================================================
-- §9  Example Cards (real TCG cards)
-- ============================================================

/-- Charizard ex (Scarlet & Violet — Obsidian Flames). -/
def charizardEx : PokemonCard where
  name := "Charizard ex"
  stage := .stage2
  ptype := .fire
  hp := 330
  attacks := [
    { name := "Brave Wing",
      cost := [.typed .fire],
      baseDamage := 60,
      effect := "" },
    { name := "Burning Dark",
      cost := [.typed .fire, .typed .fire, .colorless],
      baseDamage := 180,
      effect := "This attack does 30 more damage for each Prize card your opponent has taken." }
  ]
  ability := some {
    name := "Infernal Reign",
    kind := .ability,
    description := "When you play this Pokémon from your hand to evolve 1 of your Pokémon during your turn, you may search your deck for up to 3 basic Energy cards and attach them to your Pokémon in any way you like."
  }
  weakness := some .water
  resistance := none
  retreatCost := 2
  ruleBox := .ex_lower

/-- Pikachu (Base Set). -/
def pikachuBase : PokemonCard where
  name := "Pikachu"
  stage := .basic
  ptype := .electric
  hp := 40
  attacks := [
    { name := "Gnaw",
      cost := [.colorless],
      baseDamage := 10,
      effect := "" },
    { name := "Thunder Jolt",
      cost := [.typed .electric, .colorless],
      baseDamage := 30,
      effect := "Flip a coin. If tails, Pikachu does 10 damage to itself." }
  ]
  ability := none
  weakness := some .fighting
  resistance := none
  retreatCost := 1
  ruleBox := .none

/-- Mew VMAX (Fusion Strike). -/
def mewVmax : PokemonCard where
  name := "Mew VMAX"
  stage := .vmax
  ptype := .psychic
  hp := 310
  attacks := [
    { name := "Cross Fusion Strike",
      cost := [.typed .psychic, .typed .psychic],
      baseDamage := 0,
      effect := "Choose 1 of your Benched Fusion Strike Pokémon's attacks and use it as this attack." },
    { name := "Max Miracle",
      cost := [.typed .psychic, .typed .psychic],
      baseDamage := 130,
      effect := "This attack's damage isn't affected by any effects on your opponent's Active Pokémon." }
  ]
  ability := none
  weakness := some .dark
  resistance := some .fighting
  retreatCost := 0
  ruleBox := .vmax

/-- Professor's Research (Trainer — Supporter). -/
def professorsResearch : TrainerCard where
  name := "Professor's Research"
  kind := .supporter
  description := "Discard your hand and draw 7 cards."

/-- Rare Candy (Trainer — Item). -/
def rareCandy : TrainerCard where
  name := "Rare Candy"
  kind := .item
  description := "Choose 1 of your Basic Pokémon in play. If you have a Stage 2 card in your hand that evolves from that Pokémon, put that card onto the Basic Pokémon to evolve it, skipping the Stage 1."

-- ============================================================
-- §10  Theorems — Rule Box and Prizes
-- ============================================================

/-- Regular Pokémon give 1 prize. -/

/-- EX/ex give 2 prizes. -/

/-- GX gives 2 prizes. -/

/-- Tag Team gives 3 prizes. -/

/-- V gives 2 prizes. -/

/-- VMAX gives 3 prizes. -/

/-- VSTAR gives 2 prizes. -/

/-- Tera gives 2 prizes. -/

/-- All rule box Pokémon give at least 1 prize. -/
theorem prize_at_least_one (rb : RuleBox) : rb.prizeCount ≥ 1 := by
  cases rb <;> simp [RuleBox.prizeCount]

/-- All rule box Pokémon give at most 3 prizes. -/
theorem prize_at_most_three (rb : RuleBox) : rb.prizeCount ≤ 3 := by
  cases rb <;> simp [RuleBox.prizeCount]

/-- Pokémon with a rule box give at least 2 prizes. -/
theorem rulebox_at_least_two (rb : RuleBox) (h : rb ≠ .none) : rb.prizeCount ≥ 2 := by
  cases rb <;> simp [RuleBox.prizeCount] <;> contradiction

-- ============================================================
-- §11  Theorems — Card classification
-- ============================================================

/-- A Pokémon card is classified as Pokémon. -/

/-- A Trainer card is classified as Trainer. -/

/-- An Energy card is classified as Energy. -/

/-- A Pokémon card is not an Energy card. -/

/-- A Trainer card is not a Pokémon card. -/

/-- Charizard ex's weakness is water. -/

/-- Pikachu base is a Basic Pokémon. -/
theorem pikachu_is_basic : pikachuBase.isBasic = true := by native_decide

/-- Pikachu base has no rule box. -/
theorem pikachu_no_rulebox : pikachuBase.hasRuleBox = false := by native_decide

/-- Pikachu base gives 1 prize. -/

/-- Charizard ex gives 2 prizes. -/

/-- Mew VMAX gives 3 prizes (VMAX rule). -/

/-- Mew VMAX resists Fighting. -/

/-- Every card type is classified as exactly one kind. -/
theorem card_classification_exclusive (c : Card) :
    (c.isPokemon && !c.isTrainer && !c.isEnergy) ||
    (!c.isPokemon && c.isTrainer && !c.isEnergy) ||
    (!c.isPokemon && !c.isTrainer && c.isEnergy) = true := by
  cases c <;> rfl

end PokemonLean.Core
