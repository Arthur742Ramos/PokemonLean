/-
  PokemonLean / Core / SpecialMechanics.lean

  Consolidated special mechanics for the Pokémon TCG.
  Merges content from: AncientTraits, BreakMechanics, DeltaSpecies,
  MegaEvolution, PrismStarMechanics, RadiantCollection.

  Covers:
  - Ancient Traits (XY era): Ω Barrier, α Growth, Δ Evolution, θ Double
  - BREAK Evolution: evolves from Stage 1/2, keeps attacks, sideways card
  - Delta Species (EX era): Pokémon with different types, Holon energy
  - Mega Evolution: evolves from EX, ends turn (unless Spirit Link), 2 prizes
  - Prism Star: exactly 1 per deck per name, goes to Lost Zone when discarded
  - Radiant Pokémon: exactly 1 per deck, always Basic, non-Rule Box

  All proofs are sorry-free.  35+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.SpecialMechanics

-- ============================================================
-- §1  Shared types
-- ============================================================

inductive PType where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | fairy | dragon | colorless
  deriving DecidableEq, Repr

inductive Stage where
  | basic | stage1 | stage2 | break_ | megaEx | primal
  deriving DecidableEq, Repr

structure Attack where
  name   : String
  damage : Nat
  cost   : Nat
  deriving DecidableEq, Repr

-- ============================================================
-- §2  Ancient Traits (XY era)
-- ============================================================

/-- The four Ancient Traits from XY era. -/
inductive AncientTrait where
  | omegaBarrier   -- Ω Barrier: prevents all effects of Trainer cards
  | alphaGrowth    -- α Growth: attach 2 energy per turn instead of 1
  | deltaEvolution -- Δ Evolution: can evolve on first turn or turn played
  | thetaDouble    -- θ Double: doubles damage output
  deriving DecidableEq, Repr

structure AncientPokemon where
  name          : String
  hp            : Nat
  ancientTrait  : Option AncientTrait
  attackDamage  : Nat
  deriving Repr

def hasOmegaBarrier (p : AncientPokemon) : Prop := p.ancientTrait = some .omegaBarrier
def hasAlphaGrowth (p : AncientPokemon) : Prop := p.ancientTrait = some .alphaGrowth
def hasDeltaEvolution (p : AncientPokemon) : Prop := p.ancientTrait = some .deltaEvolution
def hasThetaDouble (p : AncientPokemon) : Prop := p.ancientTrait = some .thetaDouble

/-- Maximum energy attachments per turn. -/
def maxEnergyPerTurn (poke : AncientPokemon) : Nat :=
  if poke.ancientTrait = some .alphaGrowth then 2 else 1

/-- Calculate damage with θ Double trait. -/
def calcTraitDamage (poke : AncientPokemon) : Nat :=
  if poke.ancientTrait = some .thetaDouble then poke.attackDamage * 2
  else poke.attackDamage

/-- Theorem 1: α Growth allows 2 energy per turn. -/
theorem alpha_growth_max (poke : AncientPokemon) (h : hasAlphaGrowth poke) :
    maxEnergyPerTurn poke = 2 := by
  simp [maxEnergyPerTurn, hasAlphaGrowth] at *; simp [h]

/-- Theorem 2: Normal Pokémon allows 1 energy per turn. -/
theorem normal_max_energy (poke : AncientPokemon) (h : ¬hasAlphaGrowth poke) :
    maxEnergyPerTurn poke = 1 := by
  simp [maxEnergyPerTurn, hasAlphaGrowth] at *; simp [h]

/-- Theorem 3: θ Double doubles damage. -/
theorem theta_doubles (poke : AncientPokemon) (h : hasThetaDouble poke) :
    calcTraitDamage poke = poke.attackDamage * 2 := by
  simp [calcTraitDamage, hasThetaDouble] at *; simp [h]

/-- Theorem 4: Without θ Double, damage is base. -/
theorem normal_damage (poke : AncientPokemon) (h : ¬hasThetaDouble poke) :
    calcTraitDamage poke = poke.attackDamage := by
  simp [calcTraitDamage, hasThetaDouble] at *; simp [h]

/-- Theorem 5: Traits are mutually exclusive. -/
theorem trait_exclusive (poke : AncientPokemon) (t1 t2 : AncientTrait)
    (h1 : poke.ancientTrait = some t1) (h2 : poke.ancientTrait = some t2) :
    t1 = t2 := by
  rw [h1] at h2; exact Option.some.inj h2

/-- Theorem 6: Ω Barrier implies not α Growth. -/
theorem omega_not_alpha (poke : AncientPokemon)
    (h : hasOmegaBarrier poke) : ¬hasAlphaGrowth poke := by
  intro ha
  have := trait_exclusive poke _ _ h ha
  cases this

-- Concrete examples
def primalGroudonAT : AncientPokemon :=
  { name := "Primal Groudon-EX", hp := 240, ancientTrait := some .omegaBarrier, attackDamage := 100 }
def machampAT : AncientPokemon :=
  { name := "Machamp AT", hp := 150, ancientTrait := some .thetaDouble, attackDamage := 80 }

/-- Theorem 7: Machamp θ Double: 80 base → 160 actual. -/
theorem machamp_160 : calcTraitDamage machampAT = 160 := by
  simp [calcTraitDamage, machampAT]

-- ============================================================
-- §3  BREAK Evolution
-- ============================================================

structure BreakPokemon where
  name        : String
  stage       : Stage
  hp          : Nat
  pokeType    : PType
  attacks     : List Attack
  prizeValue  : Nat
  isBreak     : Bool
  deriving DecidableEq, Repr

/-- BREAK card can evolve from Stage 1 or Stage 2. -/
def canBreakEvolve (base : BreakPokemon) (breakCard : BreakPokemon) : Bool :=
  breakCard.isBreak &&
  breakCard.stage == .break_ &&
  (base.stage == .stage1 || base.stage == .stage2) &&
  base.pokeType == breakCard.pokeType

/-- After BREAK evolution, attacks = base attacks ++ BREAK attacks. -/
def breakAttacks (base breakCard : BreakPokemon) : List Attack :=
  base.attacks ++ breakCard.attacks

/-- Theorem 8: Stage 1 can BREAK evolve. -/
theorem stage1_can_break (base breakCard : BreakPokemon)
    (hBase : base.stage = .stage1) (hBreak : breakCard.isBreak = true)
    (hStage : breakCard.stage = .break_) (hType : base.pokeType = breakCard.pokeType) :
    canBreakEvolve base breakCard = true := by
  simp [canBreakEvolve, hBase, hBreak, hStage, hType]

/-- Theorem 9: Stage 2 can BREAK evolve. -/
theorem stage2_can_break (base breakCard : BreakPokemon)
    (hBase : base.stage = .stage2) (hBreak : breakCard.isBreak = true)
    (hStage : breakCard.stage = .break_) (hType : base.pokeType = breakCard.pokeType) :
    canBreakEvolve base breakCard = true := by
  simp [canBreakEvolve, hBase, hBreak, hStage, hType]

/-- Theorem 10: Basic cannot BREAK evolve. -/
theorem basic_cannot_break (base breakCard : BreakPokemon)
    (hBase : base.stage = .basic) :
    canBreakEvolve base breakCard = false := by
  simp [canBreakEvolve, hBase]

/-- Theorem 11: BREAK cannot evolve from another BREAK. -/
theorem break_cannot_break (base breakCard : BreakPokemon)
    (hBase : base.stage = .break_) :
    canBreakEvolve base breakCard = false := by
  simp [canBreakEvolve, hBase]

/-- Theorem 12: BREAK keeps lower-stage attacks. -/
theorem break_keeps_lower_attacks (base breakCard : BreakPokemon)
    (atk : Attack) (hIn : atk ∈ base.attacks) :
    atk ∈ breakAttacks base breakCard := by
  simp [breakAttacks, List.mem_append]
  exact Or.inl hIn

/-- Theorem 13: BREAK gains BREAK attacks. -/
theorem break_gains_new_attack (base breakCard : BreakPokemon)
    (atk : Attack) (hIn : atk ∈ breakCard.attacks) :
    atk ∈ breakAttacks base breakCard := by
  simp [breakAttacks, List.mem_append]
  exact Or.inr hIn

/-- Theorem 14: Combined attack list length. -/
theorem breakAttacks_length (base breakCard : BreakPokemon) :
    (breakAttacks base breakCard).length = base.attacks.length + breakCard.attacks.length := by
  simp [breakAttacks, List.length_append]

-- Concrete: Greninja BREAK
def greninja : BreakPokemon := ⟨"Greninja", .stage2, 130, .water,
  [⟨"Shadow Stitching", 40, 1⟩, ⟨"Moonlight Slash", 60, 2⟩], 1, false⟩
def greninjaBREAK : BreakPokemon := ⟨"Greninja BREAK", .break_, 170, .water,
  [⟨"Giant Water Shuriken", 0, 0⟩], 1, true⟩

/-- Theorem 15: Greninja can BREAK evolve. -/
theorem greninja_can_break : canBreakEvolve greninja greninjaBREAK = true := by
  native_decide

/-- Theorem 16: Greninja BREAK keeps Shadow Stitching. -/
theorem greninja_keeps_shadow_stitching :
    ⟨"Shadow Stitching", 40, 1⟩ ∈ breakAttacks greninja greninjaBREAK := by
  simp [breakAttacks, greninja, greninjaBREAK]

-- ============================================================
-- §4  Mega Evolution
-- ============================================================

inductive CardKind where
  | basic | stage1 | stage2 | ex | megaEx | primalReversion
  deriving DecidableEq, Repr

inductive ToolCard where
  | megaStone   : String → ToolCard
  | spiritLink  : String → ToolCard
  | otherTool   : String → ToolCard
  deriving DecidableEq, Repr

structure MegaPokemon where
  name       : String
  kind       : CardKind
  hp         : Nat
  attacks    : List Attack
  isRuleBox  : Bool
  prizeValue : Nat
  deriving DecidableEq, Repr

structure MegaState where
  active        : MegaPokemon
  attachedTool  : Option ToolCard
  megaThisTurn  : Bool
  turnEnded     : Bool
  energyCount   : Nat
  deriving DecidableEq, Repr

def isEX (p : MegaPokemon) : Bool := p.kind == .ex
def isMegaEX (p : MegaPokemon) : Bool := p.kind == .megaEx

def hasMegaStone (s : MegaState) : Bool :=
  match s.attachedTool with
  | some (.megaStone _) => true
  | _ => false

def hasSpiritLink (s : MegaState) : Bool :=
  match s.attachedTool with
  | some (.spiritLink _) => true
  | _ => false

def canMegaEvolve (s : MegaState) : Bool :=
  isEX s.active && hasMegaStone s && !s.megaThisTurn

def megaEvolve (s : MegaState) (mega : MegaPokemon) (spiritLink : Bool) : MegaState :=
  { active := mega,
    attachedTool := s.attachedTool,
    megaThisTurn := true,
    turnEnded := !spiritLink,
    energyCount := s.energyCount }

-- Concrete
def charizardEX : MegaPokemon :=
  { name := "Charizard-EX", kind := .ex, hp := 180,
    attacks := [⟨"Combustion", 60, 2⟩, ⟨"Fire Blast", 120, 4⟩],
    isRuleBox := true, prizeValue := 2 }
def megaCharizardX : MegaPokemon :=
  { name := "M Charizard-EX (X)", kind := .megaEx, hp := 220,
    attacks := [⟨"Combustion", 60, 2⟩, ⟨"Fire Blast", 120, 4⟩, ⟨"Wild Blaze", 300, 5⟩],
    isRuleBox := true, prizeValue := 2 }

/-- Theorem 17: With Spirit Link, turn does not end. -/
theorem spirit_link_no_end_turn (s0 : MegaState) :
    (megaEvolve s0 megaCharizardX true).turnEnded = false := rfl

/-- Theorem 18: Without Spirit Link, turn ends. -/
theorem no_spirit_link_ends_turn (s0 : MegaState) :
    (megaEvolve s0 megaCharizardX false).turnEnded = true := rfl

/-- Theorem 19: Mega EX gives 2 prizes. -/
theorem mega_gives_two_prizes : megaCharizardX.prizeValue = 2 := rfl

/-- Theorem 20: Mega EX is a Rule Box. -/
theorem mega_is_rule_box : megaCharizardX.isRuleBox = true := rfl

/-- Theorem 21: HP boost from Mega Evolution. -/
theorem mega_hp_boost : megaCharizardX.hp > charizardEX.hp := by native_decide

/-- Theorem 22: Mega EX keeps old attacks (prefix). -/
theorem mega_keeps_attacks :
    charizardEX.attacks.isPrefixOf megaCharizardX.attacks = true := by native_decide

/-- Theorem 23: One Mega per turn — second attempt blocked. -/
theorem one_mega_per_turn (s0 : MegaState) :
    let s1 := megaEvolve s0 megaCharizardX false
    canMegaEvolve s1 = false := by
  simp [canMegaEvolve, megaEvolve, isEX]

/-- Theorem 24: Mega evolve preserves energy count. -/
theorem mega_preserves_energy (s : MegaState) (mega : MegaPokemon) (sl : Bool) :
    (megaEvolve s mega sl).energyCount = s.energyCount := rfl

-- ============================================================
-- §5  Prism Star (◇)
-- ============================================================

inductive PrismStarName where
  | superBoostEnergy | beastEnergy | diancie | jirachi
  | cyrus | giratina | arceus
  deriving DecidableEq, Repr, BEq

inductive PCard where
  | prismStar : PrismStarName → PCard
  | regular   : String → PCard
  deriving DecidableEq, Repr

abbrev PDeck := List PCard

def prismCountByName (d : PDeck) (n : PrismStarName) : Nat :=
  d.filter (fun c => match c with
    | .prismStar p => decide (p = n)
    | .regular _   => false) |>.length

/-- Prism Star deck rule: at most one copy of each named Prism Star. -/
def prismValid (d : PDeck) : Prop :=
  ∀ n : PrismStarName, prismCountByName d n ≤ 1

/-- Discard routing: Prism Stars go to Lost Zone. -/
structure PrismGameState where
  discard  : List PCard
  lostZone : List PCard
  deriving Repr

def discardPrismStar (gs : PrismGameState) (c : PrismStarName) : PrismGameState :=
  { gs with lostZone := .prismStar c :: gs.lostZone }

def discardRegular (gs : PrismGameState) (name : String) : PrismGameState :=
  { gs with discard := .regular name :: gs.discard }

def discardCard (gs : PrismGameState) (c : PCard) : PrismGameState :=
  match c with
  | .prismStar p => discardPrismStar gs p
  | .regular n   => discardRegular gs n

/-- Theorem 25: Empty deck is Prism-valid. -/
theorem empty_prism_valid : prismValid [] := by
  intro n; simp [prismCountByName, List.filter]

/-- Theorem 26: Single Prism Star card is valid. -/
theorem singleton_prism_valid (c : PrismStarName) :
    prismValid [.prismStar c] := by
  intro n; simp [prismCountByName, List.filter]; split <;> simp

/-- Theorem 27: Discarding a Prism Star sends it to Lost Zone. -/
theorem prism_discard_to_lost_zone (gs : PrismGameState) (c : PrismStarName) :
    (discardPrismStar gs c).lostZone = .prismStar c :: gs.lostZone := by
  simp [discardPrismStar]

/-- Theorem 28: Discarding a Prism Star does not change discard pile. -/
theorem prism_discard_preserves_discard (gs : PrismGameState) (c : PrismStarName) :
    (discardPrismStar gs c).discard = gs.discard := by
  simp [discardPrismStar]

/-- Theorem 29: Discarding a regular card does not change Lost Zone. -/
theorem regular_discard_preserves_lostzone (gs : PrismGameState) (n : String) :
    (discardRegular gs n).lostZone = gs.lostZone := by
  simp [discardRegular]

/-- Theorem 30: discardCard routes correctly — Prism Star case. -/
theorem discard_card_prism_routes (gs : PrismGameState) (c : PrismStarName) :
    discardCard gs (.prismStar c) = discardPrismStar gs c := by
  simp [discardCard]

-- ============================================================
-- §6  Radiant Pokémon
-- ============================================================

inductive RadiantName where
  | charizard | greninja | alakazam | eevee | gardevoir | hawlucha | jirachi
  deriving DecidableEq, Repr, BEq

structure RadiantCard where
  name        : RadiantName
  hp          : Nat
  abilityName : String
  attackDamage : Nat
  deriving DecidableEq, Repr

inductive RCard where
  | radiant : RadiantCard → RCard
  | regular : String → RCard
  deriving DecidableEq, Repr

abbrev RDeck := List RCard

def radiantCount (d : RDeck) : Nat :=
  d.filter (fun c => match c with | .radiant _ => true | .regular _ => false) |>.length

/-- A deck is Radiant-valid: at most one Radiant Pokémon. -/
def radiantValid (d : RDeck) : Prop := radiantCount d ≤ 1

/-- Radiant Pokémon are NOT Rule Box. -/
def radiantIsRuleBox : RCard → Bool
  | .radiant _ => false
  | .regular _ => false

/-- Radiant Pokémon cannot evolve. -/
def radiantCanEvolve : RCard → Bool
  | .radiant _ => false
  | .regular _ => true

/-- Prizes given up when KO'd. -/
def radiantPrizesGiven : RCard → Nat
  | .radiant _ => 1
  | .regular _ => 1

-- Concrete
def radiantCharizard : RadiantCard :=
  ⟨.charizard, 160, "Excited Heart", 250⟩
def radiantGreninja : RadiantCard :=
  ⟨.greninja, 130, "Concealed Cards", 90⟩
def radiantAlakazam : RadiantCard :=
  ⟨.alakazam, 130, "Painful Spoons", 20⟩

/-- Theorem 31: Empty deck is Radiant-valid. -/
theorem empty_radiant_valid : radiantValid [] := by
  simp [radiantValid, radiantCount, List.filter, List.length]

/-- Theorem 32: Single Radiant deck is valid. -/
theorem single_radiant_valid (rc : RadiantCard) :
    radiantValid [RCard.radiant rc] := by
  simp [radiantValid, radiantCount, List.filter, List.length]

/-- Theorem 33: Radiant Pokémon are never Rule Box. -/
theorem radiant_not_rule_box (rc : RadiantCard) :
    radiantIsRuleBox (RCard.radiant rc) = false := by
  simp [radiantIsRuleBox]

/-- Theorem 34: Radiant Pokémon cannot evolve. -/
theorem radiant_no_evolve (rc : RadiantCard) :
    radiantCanEvolve (RCard.radiant rc) = false := by
  simp [radiantCanEvolve]

/-- Theorem 35: Radiant gives exactly 1 prize. -/
theorem radiant_one_prize (rc : RadiantCard) :
    radiantPrizesGiven (RCard.radiant rc) = 1 := by
  simp [radiantPrizesGiven]

/-- Theorem 36: Charizard has highest HP among the big three Radiants. -/
theorem charizard_highest_hp :
    radiantCharizard.hp ≥ radiantGreninja.hp ∧
    radiantCharizard.hp ≥ radiantAlakazam.hp := by
  constructor <;> decide

-- ============================================================
-- §7  Delta Species (EX era)
-- ============================================================

structure DeltaPokemon where
  dexNum     : Nat
  name       : String
  normalType : PType
  deltaType  : PType
  isDelta    : Bool
  deriving DecidableEq, Repr

def DeltaPokemon.hasTypeShift (p : DeltaPokemon) : Prop :=
  p.deltaType ≠ p.normalType

/-- Weakness uses delta type, not normal type. -/
def deltaWeakTo : PType → PType → Bool
  | .fire,      .water     => true
  | .water,     .lightning  => true
  | .grass,     .fire      => true
  | .lightning, .fighting  => true
  | .metal,     .fire      => true
  | _,          _          => false

def pikachuDelta : DeltaPokemon :=
  ⟨25, "Pikachu", .lightning, .metal, true⟩

/-- Theorem 37: Metal-type Pikachu δ is weak to fire. -/
theorem pikachu_delta_weak_fire :
    deltaWeakTo .metal .fire = true := by native_decide

/-- Theorem 38: Pikachu δ has a type shift (lightning → metal). -/
theorem pikachu_delta_type_shift :
    pikachuDelta.hasTypeShift := by
  simp [DeltaPokemon.hasTypeShift, pikachuDelta]

-- ============================================================
-- §8  Excited Heart bonus (Radiant Charizard)
-- ============================================================

def excitedHeartBonus (energyInDiscard : Nat) (baseDamage : Nat) : Nat :=
  baseDamage + energyInDiscard * 30

/-- Theorem 39: Excited Heart with 0 energy = base damage. -/
theorem excited_heart_zero : excitedHeartBonus 0 250 = 250 := by
  simp [excitedHeartBonus]

/-- Theorem 40: Excited Heart with 5 energy = 400. -/
theorem excited_heart_five : excitedHeartBonus 5 250 = 400 := by
  simp [excitedHeartBonus]

/-- Theorem 41: Excited Heart bonus is monotone in energy count. -/
theorem excited_heart_monotone (e₁ e₂ base : Nat) (h : e₁ ≤ e₂) :
    excitedHeartBonus e₁ base ≤ excitedHeartBonus e₂ base := by
  simp [excitedHeartBonus]; omega

end PokemonLean.Core.SpecialMechanics
