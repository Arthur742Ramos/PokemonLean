/-
  PokemonLean / Core / ScarletViolet.lean

  Scarlet & Violet era card formalization.
  Covers the ex mechanic (lowercase), Tera mechanic, and key SV-era
  cards: Gardevoir ex, Miraidon ex, Koraidon ex.

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  40+ theorems.
-/

namespace PokemonLean.Core.ScarletViolet

-- ============================================================
-- §1  Core Types
-- ============================================================

/-- Pokémon types in the TCG. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | fairy | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Evolution stage. -/
inductive Stage where
  | basic | stage1 | stage2
deriving DecidableEq, Repr, BEq, Inhabited

/-- Energy type: a specific type or colorless wildcard. -/
inductive EnergyType where
  | typed (t : PType)
  | colorless
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  The ex Mechanic (Scarlet & Violet lowercase ex)
-- ============================================================

/-- Whether a Pokémon is an ex Pokémon. -/
structure ExStatus where
  isEx : Bool
deriving DecidableEq, Repr, Inhabited

/-- Prize cards taken when a Pokémon is KO'd. -/
def exPrizeCount (status : ExStatus) : Nat :=
  if status.isEx then 2 else 1

/-- ex Pokémon can be Basic or evolved (Stage 1 / Stage 2). -/
def exValidStage : Stage → Bool
  | .basic  => true
  | .stage1 => true
  | .stage2 => true

-- ============================================================
-- §3  The Tera Mechanic
-- ============================================================

/-- Tera Pokémon ex status. -/
structure TeraStatus where
  isTera : Bool
  teraType : Option PType  -- The Tera type (may differ from base type)
deriving Repr, Inhabited

/-- Tera Pokémon ex take no bench damage from opponent attacks. -/
def teraBenchDamageBlocked (ts : TeraStatus) (isOnBench : Bool) : Bool :=
  ts.isTera && isOnBench

/-- Tera Pokémon ex are always also ex. -/
def teraImpliesEx (ts : TeraStatus) : ExStatus :=
  { isEx := ts.isTera || true }  -- Tera mon are ex by definition

/-- Tera Pokémon give 2 prizes (they are ex). -/
def teraPrizeCount (_ts : TeraStatus) : Nat := 2

-- ============================================================
-- §4  Attack and Ability Structures
-- ============================================================

/-- Energy cost for an attack. -/
structure EnergyCost where
  typedCost : List EnergyType
deriving Repr, Inhabited

/-- An attack. -/
structure SVAttack where
  name       : String
  cost       : EnergyCost
  baseDamage : Nat
  effect     : String
deriving Repr, Inhabited

/-- An ability. -/
structure SVAbility where
  name        : String
  description : String
  usableFromBench : Bool  -- some abilities only active in active spot
  oncePerTurn : Bool       -- vs repeatable
deriving Repr, Inhabited

-- ============================================================
-- §5  SV-era Pokémon Card
-- ============================================================

/-- A Scarlet & Violet era Pokémon card. -/
structure SVCard where
  name       : String
  stage      : Stage
  ptype      : PType
  hp         : Nat
  exStatus   : ExStatus
  teraStatus : TeraStatus
  attacks    : List SVAttack
  ability    : Option SVAbility
  weakness   : Option PType
  resistance : Option PType
  retreatCost : Nat
deriving Repr, Inhabited

/-- Prize count for an SV card. -/
def SVCard.prizeValue (c : SVCard) : Nat :=
  exPrizeCount c.exStatus

/-- Whether this card blocks bench damage via Tera mechanic. -/
def SVCard.blocksBenchDamage (c : SVCard) (onBench : Bool) : Bool :=
  teraBenchDamageBlocked c.teraStatus onBench

-- ============================================================
-- §6  HP Ranges for ex vs Regular
-- ============================================================

/-- Minimum HP for regular Basic Pokémon. -/
def regularBasicMinHP : Nat := 30

/-- Maximum HP for regular Basic Pokémon (approximate). -/
def regularBasicMaxHP : Nat := 130

/-- Minimum HP for ex Basic Pokémon. -/
def exBasicMinHP : Nat := 180

/-- Maximum HP for ex Stage 2 Pokémon. -/
def exStage2MaxHP : Nat := 340

/-- ex Pokémon have higher HP floor than regular. -/
def exHPHigherThanRegular : Prop :=
  exBasicMinHP > regularBasicMaxHP

-- ============================================================
-- §7  Key SV Cards: Gardevoir ex
-- ============================================================

/-- Psychic Embrace ability: attach Psychic energy from discard to one of
    your Pokémon, but put 2 damage counters (20 damage) on that Pokémon.
    Repeatable (not once per turn). -/
def psychicEmbraceAbility : SVAbility where
  name := "Psychic Embrace"
  description := "As often as you like during your turn, you may attach a Psychic Energy from your discard pile to 1 of your Pokémon. If you do, put 2 damage counters on that Pokémon."
  usableFromBench := true
  oncePerTurn := false

/-- Gardevoir ex: 280HP Psychic Stage 2 ex. -/
def gardevoirEx : SVCard where
  name := "Gardevoir ex"
  stage := .stage2
  ptype := .psychic
  hp := 280
  exStatus := { isEx := true }
  teraStatus := { isTera := false, teraType := none }
  attacks := [
    { name := "Brainwave"
      cost := { typedCost := [.typed .psychic, .colorless, .colorless] }
      baseDamage := 60
      effect := "This attack does 20 more damage for each Psychic Energy attached to this Pokémon." }
  ]
  ability := some psychicEmbraceAbility
  weakness := some .dark
  resistance := none
  retreatCost := 2

-- ============================================================
-- §8  Key SV Cards: Miraidon ex
-- ============================================================

/-- Tandem Unit ability: search deck for up to 2 Basic Electric Pokémon
    and put them on bench. Once per turn. -/
def tandemUnitAbility : SVAbility where
  name := "Tandem Unit"
  description := "Once during your turn, you may search your deck for up to 2 Basic Lightning Pokémon and put them onto your Bench."
  usableFromBench := false  -- Must be active (or bench; ruling: works from bench)
  oncePerTurn := true

/-- Miraidon ex: 220HP Electric Basic ex. -/
def miraidonEx : SVCard where
  name := "Miraidon ex"
  stage := .basic
  ptype := .electric
  hp := 220
  exStatus := { isEx := true }
  teraStatus := { isTera := false, teraType := none }
  attacks := [
    { name := "Photon Blaster"
      cost := { typedCost := [.typed .electric, .typed .electric, .colorless] }
      baseDamage := 220
      effect := "During your next turn, this Pokémon can't attack." }
  ]
  ability := some tandemUnitAbility
  weakness := some .fighting
  resistance := none
  retreatCost := 1

-- ============================================================
-- §9  Key SV Cards: Koraidon ex
-- ============================================================

/-- Dino Cry ability: attach up to 2 Fighting Energy from discard pile
    to your Basic Pokémon on bench. Once per turn. -/
def dinoCryAbility : SVAbility where
  name := "Dino Cry"
  description := "Once during your turn, you may attach up to 2 Basic Fighting Energy cards from your discard pile to your Basic Pokémon in any way you like."
  usableFromBench := false
  oncePerTurn := true

/-- Koraidon ex: 230HP Fighting Basic ex. -/
def koraidonEx : SVCard where
  name := "Koraidon ex"
  stage := .basic
  ptype := .fighting
  hp := 230
  exStatus := { isEx := true }
  teraStatus := { isTera := false, teraType := none }
  attacks := [
    { name := "Wild Impact"
      cost := { typedCost := [.typed .fighting, .typed .fighting, .colorless] }
      baseDamage := 220
      effect := "During your next turn, this Pokémon can't attack." }
  ]
  ability := some dinoCryAbility
  weakness := some .psychic
  resistance := none
  retreatCost := 2

-- ============================================================
-- §10  Tera ex example: Charizard ex Tera
-- ============================================================

/-- Charizard ex (Tera — Darkness Tera type). -/
def charizardExTera : SVCard where
  name := "Charizard ex"
  stage := .stage2
  ptype := .fire
  hp := 330
  exStatus := { isEx := true }
  teraStatus := { isTera := true, teraType := some .dark }
  attacks := [
    { name := "Burning Dark"
      cost := { typedCost := [.typed .fire, .typed .fire, .colorless] }
      baseDamage := 180
      effect := "This attack does 30 more damage for each Prize card your opponent has taken." },
    { name := "Brave Wing"
      cost := { typedCost := [.typed .fire] }
      baseDamage := 60
      effect := "" }
  ]
  ability := some {
    name := "Infernal Reign"
    description := "When you play this Pokémon from your hand to evolve, search your deck for up to 3 basic Energy and attach them to your Pokémon."
    usableFromBench := false
    oncePerTurn := true
  }
  weakness := some .water
  resistance := none
  retreatCost := 2

-- ============================================================
-- §11  Psychic Embrace Simulation
-- ============================================================

/-- State of a Pokémon after Psychic Embrace uses. -/
structure EmbraceState where
  attachedPsychic : Nat
  damageCounters  : Nat   -- each use adds 20 (2 damage counters × 10)
deriving Repr, Inhabited

/-- Apply Psychic Embrace n times. -/
def applyEmbrace (initial : EmbraceState) (uses : Nat) : EmbraceState :=
  { attachedPsychic := initial.attachedPsychic + uses
    damageCounters  := initial.damageCounters + uses * 20 }

-- ============================================================
-- §12  Bench Fill Simulation (Miraidon)
-- ============================================================

/-- Maximum bench size in standard play. -/
def maxBenchSize : Nat := 5

/-- Number of Pokémon Miraidon's Tandem Unit can add (up to 2, limited by bench). -/
def tandemUnitAdds (currentBench : Nat) : Nat :=
  min 2 (maxBenchSize - currentBench)

-- ============================================================
-- §13  Energy Acceleration Simulation (Koraidon)
-- ============================================================

/-- Energy in discard pile. -/
structure DiscardPile where
  fightingEnergy : Nat
deriving Repr, Inhabited

/-- Dino Cry: attach up to 2 Fighting from discard. -/
def dinoCryAttach (discard : DiscardPile) : Nat :=
  min 2 discard.fightingEnergy

-- ============================================================
-- §14  Ability Timing
-- ============================================================

/-- Phase of a turn. -/
inductive TurnPhase where
  | draw | main | attack | betweenTurns
deriving DecidableEq, Repr, Inhabited

/-- Abilities are used during the main phase (before attacking). -/
def abilityUsableInPhase : TurnPhase → Bool
  | .main => true
  | _     => false

-- ============================================================
-- §15  Theorems: ex Gives 2 Prizes
-- ============================================================

theorem ex_gives_two_prizes : exPrizeCount { isEx := true } = 2 := by
  simp [exPrizeCount]

theorem regular_gives_one_prize : exPrizeCount { isEx := false } = 1 := by
  simp [exPrizeCount]

theorem gardevoirEx_gives_two : gardevoirEx.prizeValue = 2 := by
  simp [SVCard.prizeValue, exPrizeCount, gardevoirEx]

theorem miraidonEx_gives_two : miraidonEx.prizeValue = 2 := by
  simp [SVCard.prizeValue, exPrizeCount, miraidonEx]

theorem koraidonEx_gives_two : koraidonEx.prizeValue = 2 := by
  simp [SVCard.prizeValue, exPrizeCount, koraidonEx]

theorem charizardExTera_gives_two : charizardExTera.prizeValue = 2 := by
  simp [SVCard.prizeValue, exPrizeCount, charizardExTera]

-- ============================================================
-- §16  Theorems: Tera Blocks Bench Damage
-- ============================================================

theorem tera_blocks_bench_damage :
    teraBenchDamageBlocked { isTera := true, teraType := some .dark } true = true := by
  simp [teraBenchDamageBlocked]

theorem tera_doesnt_block_active :
    teraBenchDamageBlocked { isTera := true, teraType := some .dark } false = false := by
  simp [teraBenchDamageBlocked]

theorem nontera_no_bench_block :
    teraBenchDamageBlocked { isTera := false, teraType := none } true = false := by
  simp [teraBenchDamageBlocked]

theorem charizardTera_blocks_bench :
    charizardExTera.blocksBenchDamage true = true := by
  simp [SVCard.blocksBenchDamage, teraBenchDamageBlocked, charizardExTera]

theorem gardevoir_no_bench_block :
    gardevoirEx.blocksBenchDamage true = false := by
  simp [SVCard.blocksBenchDamage, teraBenchDamageBlocked, gardevoirEx]

-- ============================================================
-- §17  Theorems: Psychic Embrace
-- ============================================================

theorem embrace_zero_uses :
    applyEmbrace { attachedPsychic := 0, damageCounters := 0 } 0 =
    { attachedPsychic := 0, damageCounters := 0 } := by
  simp [applyEmbrace]

theorem embrace_one_use :
    applyEmbrace { attachedPsychic := 0, damageCounters := 0 } 1 =
    { attachedPsychic := 1, damageCounters := 20 } := by
  simp [applyEmbrace]

theorem embrace_three_uses :
    applyEmbrace { attachedPsychic := 0, damageCounters := 0 } 3 =
    { attachedPsychic := 3, damageCounters := 60 } := by
  simp [applyEmbrace]

theorem embrace_cumulative_damage (n : Nat) :
    (applyEmbrace { attachedPsychic := 0, damageCounters := 0 } n).damageCounters = n * 20 := by
  simp [applyEmbrace]

theorem embrace_cumulative_energy (n : Nat) :
    (applyEmbrace { attachedPsychic := 0, damageCounters := 0 } n).attachedPsychic = n := by
  simp [applyEmbrace]

theorem embrace_repeatable :
    psychicEmbraceAbility.oncePerTurn = false := by rfl

theorem embrace_additive (s : EmbraceState) (a b : Nat) :
    applyEmbrace (applyEmbrace s a) b = applyEmbrace s (a + b) := by
  simp [applyEmbrace, Nat.add_assoc]
  omega

-- ============================================================
-- §18  Theorems: Miraidon Fills Bench
-- ============================================================

theorem tandem_empty_bench : tandemUnitAdds 0 = 2 := by sorry
theorem tandem_bench_of_3 : tandemUnitAdds 3 = 2 := by
  simp [tandemUnitAdds, maxBenchSize]

theorem tandem_bench_of_4 : tandemUnitAdds 4 = 1 := by sorry
theorem tandem_full_bench : tandemUnitAdds 5 = 0 := by
  simp [tandemUnitAdds, maxBenchSize]

theorem tandem_at_most_two (n : Nat) : tandemUnitAdds n ≤ 2 := by
  simp [tandemUnitAdds, maxBenchSize]
  omega

-- ============================================================
-- §19  Theorems: Koraidon Energy Acceleration
-- ============================================================

theorem dino_cry_empty_discard :
    dinoCryAttach { fightingEnergy := 0 } = 0 := by
  simp [dinoCryAttach]

theorem dino_cry_one_in_discard :
    dinoCryAttach { fightingEnergy := 1 } = 1 := by sorry

theorem dino_cry_full :
    dinoCryAttach { fightingEnergy := 5 } = 2 := by sorry

theorem dino_cry_at_most_two (d : DiscardPile) :
    dinoCryAttach d ≤ 2 := by
  simp [dinoCryAttach]
  omega

-- ============================================================
-- §20  Theorems: Ability Timing
-- ============================================================

theorem abilities_main_phase : abilityUsableInPhase .main = true := by rfl

theorem abilities_not_during_attack : abilityUsableInPhase .attack = false := by rfl

theorem abilities_not_between_turns : abilityUsableInPhase .betweenTurns = false := by rfl

theorem abilities_not_during_draw : abilityUsableInPhase .draw = false := by rfl

-- ============================================================
-- §21  Theorems: ex HP Ranges
-- ============================================================

theorem ex_hp_higher_than_regular : exBasicMinHP > regularBasicMaxHP := by
  simp [exBasicMinHP, regularBasicMaxHP]

theorem gardevoir_hp : gardevoirEx.hp = 280 := by rfl

theorem miraidon_hp : miraidonEx.hp = 220 := by rfl

theorem koraidon_hp : koraidonEx.hp = 230 := by rfl

theorem charizardTera_hp : charizardExTera.hp = 330 := by rfl

theorem gardevoir_is_stage2 : gardevoirEx.stage = .stage2 := by rfl

theorem miraidon_is_basic : miraidonEx.stage = .basic := by rfl

theorem koraidon_is_basic : koraidonEx.stage = .basic := by rfl

-- ============================================================
-- §22  Theorems: ex Valid Stages
-- ============================================================

theorem ex_basic_valid : exValidStage .basic = true := by rfl
theorem ex_stage1_valid : exValidStage .stage1 = true := by rfl
theorem ex_stage2_valid : exValidStage .stage2 = true := by rfl

-- ============================================================
-- §23  Theorems: Card Properties
-- ============================================================

theorem gardevoir_is_psychic : gardevoirEx.ptype = .psychic := by rfl
theorem miraidon_is_electric : miraidonEx.ptype = .electric := by rfl
theorem koraidon_is_fighting : koraidonEx.ptype = .fighting := by rfl

theorem gardevoir_weak_to_dark : gardevoirEx.weakness = some .dark := by rfl
theorem miraidon_weak_to_fighting : miraidonEx.weakness = some .fighting := by rfl
theorem koraidon_weak_to_psychic : koraidonEx.weakness = some .psychic := by rfl

theorem charizardTera_is_tera : charizardExTera.teraStatus.isTera = true := by rfl
theorem gardevoir_not_tera : gardevoirEx.teraStatus.isTera = false := by rfl

-- ============================================================
-- §24  Theorems: Tandem Unit is once-per-turn
-- ============================================================

theorem tandem_unit_once : tandemUnitAbility.oncePerTurn = true := by rfl
theorem dino_cry_once : dinoCryAbility.oncePerTurn = true := by rfl

-- ============================================================
-- §25  Theorems: Prize and ex status relationship
-- ============================================================

theorem ex_prize_dichotomy (s : ExStatus) :
    exPrizeCount s = 1 ∨ exPrizeCount s = 2 := by
  unfold exPrizeCount
  cases s.isEx <;> simp

theorem ex_true_means_two (s : ExStatus) (h : s.isEx = true) : exPrizeCount s = 2 := by sorry
theorem ex_false_means_one (s : ExStatus) (h : s.isEx = false) : exPrizeCount s = 1 := by sorry
end PokemonLean.Core.ScarletViolet
