/-
  PokemonLean / Core / PocketBattle.lean

  Battle system specific to Pokémon TCG Pocket.
  ==============================================

  Models the turn structure, combat mechanics, and card-specific
  interactions unique to TCG Pocket:

    - Turn structure: draw → energy auto-attach → main phase → attack
    - Free retreat (switch once per turn, no retreat cost)
    - Supporters: one per turn
    - Items: unlimited per turn
    - Weakness: +20 damage (additive, not ×2 like physical)
    - No resistance in Pocket
    - Evolution: can evolve same turn played (unlike physical)
    - Specific Pocket card interactions

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  37 theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.PocketBattle

-- ============================================================
-- §1  Types and Constants
-- ============================================================

/-- Pokémon types. -/
inductive PType where
  | fire | water | grass | electric | psychic
  | fighting | dark | steel | dragon | normal
deriving DecidableEq, Repr, BEq, Inhabited

/-- Pocket weakness bonus: +20 damage (additive). -/
def pocketWeaknessBonus : Nat := 20

/-- Physical TCG weakness: ×2 damage (multiplicative). -/
def physicalWeaknessMultiplier : Nat := 2

/-- Physical TCG resistance: −30 damage. -/
def physicalResistanceReduction : Nat := 30

/-- Max bench slots in Pocket. -/
def maxBenchSlots : Nat := 3

/-- Energy zone generates exactly 1 per turn. -/
def energyZoneRate : Nat := 1

/-- Max switches per turn (free retreat). -/
def maxSwitchesPerTurn : Nat := 1

-- ============================================================
-- §2  Weakness Chart (Pocket-specific)
-- ============================================================

/-- Pocket weakness: each type has exactly one weakness type. -/
def weaknessType : PType → PType
  | .fire      => .water
  | .water     => .electric
  | .grass     => .fire
  | .electric  => .fighting
  | .psychic   => .dark
  | .fighting  => .psychic
  | .dark      => .fighting
  | .steel     => .fire
  | .dragon    => .dragon  -- dragon weak to dragon
  | .normal    => .fighting

/-- Is attacker type weak to defender type? -/
def isWeakTo (defender attacker : PType) : Bool :=
  weaknessType defender == attacker

-- ============================================================
-- §3  Damage Calculation (Pocket-specific)
-- ============================================================

/-- Calculate Pocket damage.
    - Base damage from attack
    - +20 if attacker's type is the defender's weakness
    - NO resistance in Pocket
    - Minimum 0 damage -/
def calculateDamage (baseDmg : Nat) (attackerType defenderType : PType) : Nat :=
  if isWeakTo defenderType attackerType then
    baseDmg + pocketWeaknessBonus
  else
    baseDmg

/-- Calculate physical TCG damage for comparison.
    - Base × 2 if weak, −30 if resistant, min 0. -/
def calculatePhysicalDamage (baseDmg : Nat) (isWeak isResistant : Bool) : Nat :=
  let afterWeak := if isWeak then baseDmg * physicalWeaknessMultiplier else baseDmg
  if isResistant then
    if afterWeak > physicalResistanceReduction then afterWeak - physicalResistanceReduction
    else 0
  else afterWeak

-- ============================================================
-- §4  Turn Structure
-- ============================================================

/-- Turn phases in Pocket. -/
inductive TurnPhase where
  | drawPhase        -- Draw 1 card
  | energyPhase      -- Energy zone auto-attaches 1 energy
  | mainPhase        -- Play trainers, evolve, switch (once)
  | attackPhase      -- Declare attack (optional)
  | endPhase         -- End of turn
deriving DecidableEq, Repr, BEq, Inhabited

/-- The ordered sequence of phases in a Pocket turn. -/
def turnPhaseOrder : List TurnPhase :=
  [.drawPhase, .energyPhase, .mainPhase, .attackPhase, .endPhase]

/-- Next phase in the turn. -/
def nextPhase : TurnPhase → TurnPhase
  | .drawPhase   => .energyPhase
  | .energyPhase => .mainPhase
  | .mainPhase   => .attackPhase
  | .attackPhase  => .endPhase
  | .endPhase    => .drawPhase   -- loops to next turn

-- ============================================================
-- §5  Battle State
-- ============================================================

/-- An attack definition. -/
structure Attack where
  name      : String
  baseDmg   : Nat
  energyCost : Nat
deriving DecidableEq, Repr, BEq, Inhabited

/-- Pokémon kind. -/
inductive PokemonKind where
  | basic | ex
deriving DecidableEq, Repr, BEq, Inhabited

/-- A Pokémon card. -/
structure PokemonCard where
  name     : String
  ptype    : PType
  kind     : PokemonKind
  hp       : Nat
  attacks  : List Attack
  canEvolveFrom : Option String   -- None for basics
deriving Repr, Inhabited

/-- In-play Pokémon. -/
structure BattlePokemon where
  card            : PokemonCard
  attachedEnergy  : Nat
  damageTaken     : Nat
  justPlayed      : Bool   -- played this turn (physical: can't evolve)
  evolvedThisTurn : Bool   -- in Pocket, evolution same turn is OK
deriving Repr, Inhabited

/-- Is this Pokémon knocked out? -/
def BattlePokemon.isKO (p : BattlePokemon) : Bool :=
  p.damageTaken ≥ p.card.hp

/-- Remaining HP. -/
def BattlePokemon.remainingHP (p : BattlePokemon) : Nat :=
  if p.card.hp > p.damageTaken then p.card.hp - p.damageTaken else 0

/-- Can this Pokémon use the given attack? -/
def BattlePokemon.canUseAttack (p : BattlePokemon) (a : Attack) : Bool :=
  p.attachedEnergy ≥ a.energyCost

/-- Player battle state. -/
structure PlayerBattleState where
  active          : Option BattlePokemon
  bench           : List BattlePokemon
  hand            : Nat   -- simplified: just count
  deckSize        : Nat
  prizesRemaining : Nat
  energyGenerated : Nat   -- total energy from zone
  switchesUsed    : Nat   -- 0 or 1 this turn
  supportersUsed  : Nat   -- 0 or 1 this turn
  itemsUsed       : Nat   -- unlimited
deriving Repr, Inhabited

/-- Can the player switch? (free retreat, once per turn) -/
def PlayerBattleState.canSwitch (ps : PlayerBattleState) : Bool :=
  ps.switchesUsed < maxSwitchesPerTurn && !ps.bench.isEmpty

/-- Can the player play a supporter? (one per turn) -/
def PlayerBattleState.canPlaySupporter (ps : PlayerBattleState) : Bool :=
  ps.supportersUsed < 1

/-- Can the player play an item? (unlimited per turn) -/
def PlayerBattleState.canPlayItem (_ : PlayerBattleState) : Bool :=
  true   -- always allowed

-- ============================================================
-- §6  Retreat / Switch Mechanics
-- ============================================================

/-- Retreat cost in Pocket: always 0 (free retreat). -/
def pocketRetreatCost : Nat := 0

/-- Switch is free but limited to once per turn. -/
def performSwitch (ps : PlayerBattleState) (benchIdx : Nat) :
    Option PlayerBattleState :=
  if !ps.canSwitch then none
  else if benchIdx ≥ ps.bench.length then none
  else
    let newActive := ps.bench[benchIdx]?
    match newActive, ps.active with
    | some na, some oldActive =>
      let newBench := (ps.bench.eraseIdx benchIdx) ++ [oldActive]
      some { ps with
        active := some na
        bench := newBench
        switchesUsed := ps.switchesUsed + 1
      }
    | some na, none =>
      let newBench := ps.bench.eraseIdx benchIdx
      some { ps with
        active := some na
        bench := newBench
        switchesUsed := ps.switchesUsed + 1
      }
    | _, _ => none

-- ============================================================
-- §7  Evolution Mechanics (Pocket)
-- ============================================================

/-- In Pocket, evolution is allowed same turn the Pokémon is played.
    This is unlike the physical TCG where you must wait a turn. -/
def canEvolvePocket (_ : BattlePokemon) (evoCard : PokemonCard)
    (baseName : String) : Bool :=
  evoCard.canEvolveFrom == some baseName

/-- In physical TCG, can NOT evolve a Pokémon played this turn. -/
def canEvolvePhysical (bp : BattlePokemon) (evoCard : PokemonCard)
    (baseName : String) : Bool :=
  !bp.justPlayed && evoCard.canEvolveFrom == some baseName

-- ============================================================
-- §8  Specific Pocket Cards
-- ============================================================

/-- Mewtwo ex: 150HP, Psychic Sphere 50, Psydrive 150. -/
def mewtwoEx : PokemonCard :=
  { name := "Mewtwo ex", ptype := .psychic, kind := .ex,
    hp := 150, attacks := [⟨"Psychic Sphere", 50, 2⟩, ⟨"Psydrive", 150, 3⟩],
    canEvolveFrom := none }

/-- Pikachu ex: 120HP, Circle Circuit 30×bench. -/
def pikachuEx : PokemonCard :=
  { name := "Pikachu ex", ptype := .electric, kind := .ex,
    hp := 120, attacks := [⟨"Circle Circuit", 30, 2⟩],
    canEvolveFrom := none }

/-- Charizard ex: 180HP, Slash 60, Crimson Storm 200. -/
def charizardEx : PokemonCard :=
  { name := "Charizard ex", ptype := .fire, kind := .ex,
    hp := 180, attacks := [⟨"Slash", 60, 2⟩, ⟨"Crimson Storm", 200, 4⟩],
    canEvolveFrom := some "Charmeleon" }

/-- Charmeleon: 90HP, Flare 30. Evolves from Charmander. -/
def charmeleon : PokemonCard :=
  { name := "Charmeleon", ptype := .fire, kind := .basic,
    hp := 90, attacks := [⟨"Flare", 30, 1⟩],
    canEvolveFrom := some "Charmander" }

/-- Charmander: 60HP, Scratch 10. Basic. -/
def charmander : PokemonCard :=
  { name := "Charmander", ptype := .fire, kind := .basic,
    hp := 60, attacks := [⟨"Scratch", 10, 1⟩],
    canEvolveFrom := none }

/-- Circle Circuit damage: 30 × number of bench Pokémon. -/
def circleCircuitDamage (benchCount : Nat) : Nat :=
  30 * benchCount

/-- Crimson Storm base damage. -/
def crimsonStormDamage : Nat := 200

-- ============================================================
-- §9  Energy Zone Auto-Attach
-- ============================================================

/-- Auto-attach energy from the energy zone to a target Pokémon.
    Exactly 1 energy per turn. -/
def autoAttachEnergy (bp : BattlePokemon) : BattlePokemon :=
  { bp with attachedEnergy := bp.attachedEnergy + energyZoneRate }

/-- After n turns of auto-attach, a Pokémon has n more energy. -/
def autoAttachNTurns (bp : BattlePokemon) : Nat → BattlePokemon
  | 0     => bp
  | n + 1 => autoAttachEnergy (autoAttachNTurns bp n)

-- ============================================================
-- §10  Theorems — Battle Mechanics
-- ============================================================

-- Free retreat: retreat cost is always 0
theorem free_retreat : pocketRetreatCost = 0 := by rfl

-- Weakness is additive: +20 damage
theorem weakness_is_additive : pocketWeaknessBonus = 20 := by rfl

-- Physical weakness is multiplicative: ×2
theorem physical_weakness_multiplicative : physicalWeaknessMultiplier = 2 := by rfl

-- Weakness adds exactly 20, not doubles
theorem pocket_weakness_calc (baseDmg : Nat) (at' dt : PType)
    (h : isWeakTo dt at' = true) :
    calculateDamage baseDmg at' dt = baseDmg + 20 := by
  simp [calculateDamage, h, pocketWeaknessBonus]

-- No weakness: damage unchanged
theorem no_weakness_calc (baseDmg : Nat) (at' dt : PType)
    (h : isWeakTo dt at' = false) :
    calculateDamage baseDmg at' dt = baseDmg := by
  simp [calculateDamage, h]

-- Pocket damage ≤ base + 20 (bounded by weakness)
theorem pocket_damage_bounded (baseDmg : Nat) (at' dt : PType) :
    calculateDamage baseDmg at' dt ≤ baseDmg + pocketWeaknessBonus := by
  simp [calculateDamage, pocketWeaknessBonus]
  split <;> omega

-- Pocket damage ≥ base (never reduced, no resistance)
theorem pocket_damage_no_reduction (baseDmg : Nat) (at' dt : PType) :
    calculateDamage baseDmg at' dt ≥ baseDmg := by
  simp [calculateDamage]
  split <;> omega

-- No resistance in Pocket (contrast with physical)
theorem no_resistance_in_pocket (baseDmg : Nat) (at' dt : PType) :
    calculateDamage baseDmg at' dt ≥ baseDmg := by
  exact pocket_damage_no_reduction baseDmg at' dt

-- Same-turn evolution allowed in Pocket
theorem pocket_same_turn_evolution (bp : BattlePokemon) (evoCard : PokemonCard)
    (baseName : String) (h : evoCard.canEvolveFrom = some baseName) :
    canEvolvePocket bp evoCard baseName = true := by
  simp [canEvolvePocket, h]

-- Physical TCG blocks same-turn evolution
theorem physical_blocks_same_turn (bp : BattlePokemon) (evoCard : PokemonCard)
    (baseName : String) (hp : bp.justPlayed = true) :
    canEvolvePhysical bp evoCard baseName = false := by
  simp [canEvolvePhysical, hp]

-- Energy zone provides exactly 1 per turn
theorem energy_zone_exactly_one : energyZoneRate = 1 := by rfl

-- Auto-attach increases energy by 1
theorem auto_attach_plus_one (bp : BattlePokemon) :
    (autoAttachEnergy bp).attachedEnergy = bp.attachedEnergy + 1 := by
  simp [autoAttachEnergy, energyZoneRate]

-- After n turns, energy increased by n
theorem auto_attach_n_turns (bp : BattlePokemon) (n : Nat) :
    (autoAttachNTurns bp n).attachedEnergy = bp.attachedEnergy + n := by
  induction n with
  | zero => simp [autoAttachNTurns]
  | succ n ih =>
    simp [autoAttachNTurns, autoAttachEnergy, energyZoneRate]
    omega

-- Max switches per turn is 1
theorem max_one_switch : maxSwitchesPerTurn = 1 := by rfl

-- Items always playable
theorem items_always_playable (ps : PlayerBattleState) :
    ps.canPlayItem = true := by
  simp [PlayerBattleState.canPlayItem]

-- After using supporter, can't play another
theorem supporter_once_per_turn (ps : PlayerBattleState)
    (h : ps.supportersUsed ≥ 1) :
    ps.canPlaySupporter = false := by
  simp [PlayerBattleState.canPlaySupporter]
  omega

-- Turn phase order has 5 phases
theorem turn_has_5_phases : turnPhaseOrder.length = 5 := by
  simp [turnPhaseOrder]

-- Draw phase is first
theorem draw_phase_first : turnPhaseOrder.head? = some TurnPhase.drawPhase := by
  simp [turnPhaseOrder]

-- Energy phase follows draw phase
theorem energy_after_draw : nextPhase .drawPhase = .energyPhase := by rfl

-- Attack phase follows main phase
theorem attack_after_main : nextPhase .mainPhase = .attackPhase := by rfl

-- Mewtwo ex HP is 150
theorem mewtwo_hp : mewtwoEx.hp = 150 := by rfl

-- Pikachu ex HP is 120
theorem pikachu_ex_hp : pikachuEx.hp = 120 := by rfl

-- Charizard ex HP is 180
theorem charizard_ex_hp : charizardEx.hp = 180 := by rfl

-- Crimson Storm does 200 damage
theorem crimson_storm_200 : crimsonStormDamage = 200 := by rfl

-- Circle Circuit max damage with full bench (3 slots)
theorem circle_circuit_max_bench :
    circleCircuitDamage maxBenchSlots = 90 := by
  simp [circleCircuitDamage, maxBenchSlots]

-- Circle Circuit with 0 bench = 0 damage
theorem circle_circuit_empty_bench :
    circleCircuitDamage 0 = 0 := by
  simp [circleCircuitDamage]

-- Circle Circuit monotone in bench count
theorem circle_circuit_monotone (a b : Nat) (h : a ≤ b) :
    circleCircuitDamage a ≤ circleCircuitDamage b := by
  simp [circleCircuitDamage]
  omega

-- Circle Circuit bounded by bench size × 30
theorem circle_circuit_bounded (n : Nat) :
    circleCircuitDamage n = 30 * n := by
  simp [circleCircuitDamage]

-- KO when damage ≥ HP
theorem ko_iff_damage_ge_hp (p : BattlePokemon) :
    p.isKO = true ↔ p.damageTaken ≥ p.card.hp := by
  constructor
  · intro h; simp [BattlePokemon.isKO] at h; omega
  · intro h; simp [BattlePokemon.isKO]; omega

-- Remaining HP is 0 when KO'd
theorem ko_zero_hp (p : BattlePokemon) (h : p.isKO = true) :
    p.remainingHP = 0 := by
  simp [BattlePokemon.isKO] at h
  unfold BattlePokemon.remainingHP
  split <;> omega

-- Charizard ex evolves from Charmeleon
theorem charizard_evolves_from_charmeleon :
    charizardEx.canEvolveFrom = some "Charmeleon" := by rfl

-- Charmeleon evolves from Charmander
theorem charmeleon_evolves_from_charmander :
    charmeleon.canEvolveFrom = some "Charmander" := by rfl

-- Charmander is a basic (no evolution source)
theorem charmander_is_basic :
    charmander.canEvolveFrom = none := by rfl

-- Bench slots are 3
theorem bench_slots_3 : maxBenchSlots = 3 := by rfl

-- Pocket damage generally lower: Crimson Storm (200) vs typical physical
-- attacks (300+ for VMAX). We prove it's ≤ 200.
theorem pocket_max_attack_bounded :
    crimsonStormDamage ≤ 200 := by
  unfold crimsonStormDamage; omega

-- Fresh Pokémon has 0 damage
theorem fresh_pokemon_no_damage (card : PokemonCard) :
    (BattlePokemon.mk card 0 0 false false).damageTaken = 0 := by rfl

-- Fresh Pokémon is not KO
theorem fresh_pokemon_not_ko (card : PokemonCard) (h : card.hp > 0) :
    (BattlePokemon.mk card 0 0 false false).isKO = false := by
  simp [BattlePokemon.isKO]
  omega

end PokemonLean.Core.PocketBattle
