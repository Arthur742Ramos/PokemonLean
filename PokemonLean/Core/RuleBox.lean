/-
  PokemonLean / Core / RuleBox.lean

  Full Rule Box taxonomy for the Pokémon TCG across all eras.
  Covers EX (uppercase, XY era), ex (lowercase, SV era), GX, Tag Team GX,
  V, VMAX, VSTAR, Tera ex.  Prize counts, HP ranges, once-per-game
  mechanics (GX attack, VSTAR Power), Tag Team GX bonus thresholds,
  and Roxanne interaction (playable when opponent ≤ 3 prizes remaining).

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.RuleBoxMod

-- ============================================================
-- §1  Era Classification
-- ============================================================

/-- TCG eras for rule box Pokémon. -/
inductive Era where
  | base       -- Base Set through BW
  | xy         -- XY era (EX uppercase, Mega)
  | sm         -- Sun & Moon (GX, Tag Team GX)
  | swsh       -- Sword & Shield (V, VMAX, VSTAR)
  | sv         -- Scarlet & Violet (ex lowercase, Tera ex)
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §2  Rule Box Category
-- ============================================================

/-- Complete rule box taxonomy across all eras. -/
inductive RuleBoxKind where
  | none         -- Regular Pokémon (no rule box)
  | exUpper      -- EX (uppercase, XY era)
  | exLower      -- ex (lowercase, SV era)
  | mega         -- Mega EX (XY era, evolves from EX)
  | gx           -- GX (SM era)
  | tagTeamGX    -- Tag Team GX (SM era, multi-Pokémon)
  | v            -- V (SWSH era)
  | vmax         -- VMAX (SWSH era, Gigantamax/Dynamax)
  | vstar        -- VSTAR (SWSH era)
  | teraEx       -- Tera ex (SV era, takes no bench damage while active)
deriving DecidableEq, Repr, BEq, Inhabited

/-- Which era a rule box kind belongs to. -/
def RuleBoxKind.era : RuleBoxKind → Era
  | .none      => .base
  | .exUpper   => .xy
  | .exLower   => .sv
  | .mega      => .xy
  | .gx        => .sm
  | .tagTeamGX => .sm
  | .v         => .swsh
  | .vmax      => .swsh
  | .vstar     => .swsh
  | .teraEx    => .sv

/-- Whether a Pokémon has a rule box. -/
def RuleBoxKind.hasRuleBox : RuleBoxKind → Bool
  | .none => false
  | _     => true

-- ============================================================
-- §3  Prize Counts
-- ============================================================

/-- Prize cards opponent takes on KO.
    none = 1, most rule box = 2, VMAX/Tag Team/Mega = 3. -/
def RuleBoxKind.prizeCount : RuleBoxKind → Nat
  | .none      => 1
  | .exUpper   => 2
  | .exLower   => 2
  | .mega      => 3
  | .gx        => 2
  | .tagTeamGX => 3
  | .v         => 2
  | .vmax      => 3
  | .vstar     => 2
  | .teraEx    => 2

/-- All rule box kinds as a list. -/
def RuleBoxKind.all : List RuleBoxKind :=
  [.none, .exUpper, .exLower, .mega, .gx, .tagTeamGX, .v, .vmax, .vstar, .teraEx]

-- ============================================================
-- §4  HP Ranges
-- ============================================================

/-- Minimum HP for a given rule box category (typical lower bounds). -/
def RuleBoxKind.minHP : RuleBoxKind → Nat
  | .none      => 30
  | .exUpper   => 170
  | .exLower   => 190
  | .mega      => 210
  | .gx        => 170
  | .tagTeamGX => 240
  | .v         => 200
  | .vmax      => 300
  | .vstar     => 250
  | .teraEx    => 230

/-- Maximum HP for a given rule box category (typical upper bounds). -/
def RuleBoxKind.maxHP : RuleBoxKind → Nat
  | .none      => 200
  | .exUpper   => 180
  | .exLower   => 340
  | .mega      => 250
  | .gx        => 250
  | .tagTeamGX => 300
  | .v         => 230
  | .vmax      => 340
  | .vstar     => 280
  | .teraEx    => 340

/-- Whether an HP value is valid for a given rule box category. -/
def RuleBoxKind.validHP (rb : RuleBoxKind) (hp : Nat) : Prop :=
  rb.minHP ≤ hp ∧ hp ≤ rb.maxHP

-- ============================================================
-- §5  Once-Per-Game Mechanics
-- ============================================================

/-- Whether a rule box kind has a GX attack (once per game, shared). -/
def RuleBoxKind.hasGXAttack : RuleBoxKind → Bool
  | .gx        => true
  | .tagTeamGX => true
  | _          => false

/-- Whether a rule box kind has a VSTAR Power (once per game). -/
def RuleBoxKind.hasVSTARPower : RuleBoxKind → Bool
  | .vstar => true
  | _      => false

/-- Game state tracking for once-per-game mechanics. -/
structure OncePerGameState where
  gxAttackUsed    : Bool   -- Has this player used their GX attack?
  vstarPowerUsed  : Bool   -- Has this player used their VSTAR Power?
deriving DecidableEq, Repr, Inhabited

/-- Initial once-per-game state: nothing used yet. -/
def OncePerGameState.initial : OncePerGameState :=
  { gxAttackUsed := false, vstarPowerUsed := false }

/-- Can this player use a GX attack? -/
def OncePerGameState.canUseGXAttack (s : OncePerGameState) : Bool :=
  !s.gxAttackUsed

/-- Can this player use a VSTAR Power? -/
def OncePerGameState.canUseVSTARPower (s : OncePerGameState) : Bool :=
  !s.vstarPowerUsed

/-- Use the GX attack (marks it as used). -/
def OncePerGameState.useGXAttack (s : OncePerGameState) : OncePerGameState :=
  { s with gxAttackUsed := true }

/-- Use the VSTAR Power (marks it as used). -/
def OncePerGameState.useVSTARPower (s : OncePerGameState) : OncePerGameState :=
  { s with vstarPowerUsed := true }

-- ============================================================
-- §6  Tag Team GX Bonus Mechanic
-- ============================================================

/-- Tag Team GX attacks have a bonus effect if you have extra energy.
    The threshold is the minimum number of EXTRA energy beyond the base cost. -/
structure TagTeamGXAttack where
  baseCostEnergy    : Nat    -- Base energy cost to use the GX attack
  bonusThreshold    : Nat    -- Extra energy needed beyond base for bonus effect
  bonusDamage       : Nat    -- Extra damage from the bonus
deriving DecidableEq, Repr, Inhabited

/-- Total energy needed for the bonus effect. -/
def TagTeamGXAttack.totalForBonus (a : TagTeamGXAttack) : Nat :=
  a.baseCostEnergy + a.bonusThreshold

/-- Whether attached energy is enough for the base GX attack. -/
def TagTeamGXAttack.canUseBase (a : TagTeamGXAttack) (attachedEnergy : Nat) : Bool :=
  attachedEnergy ≥ a.baseCostEnergy

/-- Whether attached energy is enough for the bonus effect. -/
def TagTeamGXAttack.canUseBonus (a : TagTeamGXAttack) (attachedEnergy : Nat) : Bool :=
  attachedEnergy ≥ a.totalForBonus

/-- Example: Mewtwo & Mew-GX's Miraculous Duo-GX.
    Costs 1 Psychic, bonus at +3 extra energy = 4 total. -/
def miraculousDuoGX : TagTeamGXAttack :=
  { baseCostEnergy := 1, bonusThreshold := 3, bonusDamage := 200 }

-- ============================================================
-- §7  Roxanne Interaction
-- ============================================================

/-- Roxanne can be played when the opponent has ≤ 3 prize cards remaining.
    This is particularly relevant because rule box KOs give 2-3 prizes,
    enabling Roxanne earlier. -/
def roxannePlayable (opponentPrizesRemaining : Nat) : Bool :=
  opponentPrizesRemaining ≤ 3

/-- After taking prizes from a KO, compute remaining prizes. -/
def prizesAfterKO (currentPrizes : Nat) (prizesTaken : Nat) : Nat :=
  if currentPrizes ≥ prizesTaken then currentPrizes - prizesTaken else 0

/-- Whether a single rule box KO from 6 prizes can enable Roxanne. -/
def singleKOEnablesRoxanne (rb : RuleBoxKind) : Bool :=
  roxannePlayable (prizesAfterKO 6 rb.prizeCount)

-- ============================================================
-- §8  Rule Box Pokémon Card (self-contained)
-- ============================================================

/-- A simplified rule box Pokémon card. -/
structure RBPokemon where
  name     : String
  ruleBox  : RuleBoxKind
  hp       : Nat
  isBasic  : Bool
deriving Repr, Inhabited

/-- Prize value for this Pokémon. -/
def RBPokemon.prizeValue (p : RBPokemon) : Nat := p.ruleBox.prizeCount

-- ============================================================
-- §9  Example Cards
-- ============================================================

/-- Mewtwo-EX (XY era, uppercase EX). -/
def mewtwoEX : RBPokemon :=
  { name := "Mewtwo-EX", ruleBox := .exUpper, hp := 170, isBasic := true }

/-- Charizard ex (SV era, lowercase ex). -/
def charizardEx : RBPokemon :=
  { name := "Charizard ex", ruleBox := .exLower, hp := 330, isBasic := false }

/-- Pikachu & Zekrom-GX (Tag Team). -/
def pikachuZekromGX : RBPokemon :=
  { name := "Pikachu & Zekrom-GX", ruleBox := .tagTeamGX, hp := 240, isBasic := true }

/-- Arceus VSTAR (SWSH era). -/
def arceusVSTAR : RBPokemon :=
  { name := "Arceus VSTAR", ruleBox := .vstar, hp := 280, isBasic := false }

/-- Mew VMAX (SWSH era). -/
def mewVMAX : RBPokemon :=
  { name := "Mew VMAX", ruleBox := .vmax, hp := 310, isBasic := false }

/-- Terapagos ex (Tera ex, SV era). -/
def terapagosEx : RBPokemon :=
  { name := "Terapagos ex", ruleBox := .teraEx, hp := 280, isBasic := false }

/-- Ralts (regular, no rule box). -/
def ralts : RBPokemon :=
  { name := "Ralts", ruleBox := .none, hp := 60, isBasic := true }

-- ============================================================
-- §10  Theorems — Prize Count Validation
-- ============================================================

/-- All Pokémon give at least 1 prize. -/
theorem prize_at_least_one (rb : RuleBoxKind) : rb.prizeCount ≥ 1 := by
  cases rb <;> simp [RuleBoxKind.prizeCount]

/-- All Pokémon give at most 3 prizes. -/
theorem prize_at_most_three (rb : RuleBoxKind) : rb.prizeCount ≤ 3 := by
  cases rb <;> simp [RuleBoxKind.prizeCount]

/-- Regular Pokémon give exactly 1 prize. -/
theorem none_gives_one : RuleBoxKind.none.prizeCount = 1 := by rfl

/-- EX (uppercase) gives exactly 2 prizes. -/
theorem exUpper_gives_two : RuleBoxKind.exUpper.prizeCount = 2 := by rfl

/-- ex (lowercase) gives exactly 2 prizes. -/
theorem exLower_gives_two : RuleBoxKind.exLower.prizeCount = 2 := by rfl

/-- GX gives exactly 2 prizes. -/
theorem gx_gives_two : RuleBoxKind.gx.prizeCount = 2 := by rfl

/-- Tag Team GX gives exactly 3 prizes. -/
theorem tagTeam_gives_three : RuleBoxKind.tagTeamGX.prizeCount = 3 := by rfl

/-- V gives exactly 2 prizes. -/
theorem v_gives_two : RuleBoxKind.v.prizeCount = 2 := by rfl

/-- VMAX gives exactly 3 prizes. -/
theorem vmax_gives_three : RuleBoxKind.vmax.prizeCount = 3 := by rfl

/-- VSTAR gives exactly 2 prizes. -/
theorem vstar_gives_two : RuleBoxKind.vstar.prizeCount = 2 := by rfl

/-- Tera ex gives exactly 2 prizes. -/
theorem teraEx_gives_two : RuleBoxKind.teraEx.prizeCount = 2 := by rfl

/-- Mega gives exactly 3 prizes. -/
theorem mega_gives_three : RuleBoxKind.mega.prizeCount = 3 := by rfl

/-- Rule box Pokémon (non-none) give at least 2 prizes. -/
theorem rulebox_at_least_two (rb : RuleBoxKind) (h : rb ≠ .none) :
    rb.prizeCount ≥ 2 := by
  cases rb <;> simp [RuleBoxKind.prizeCount] <;> try omega
  exact absurd rfl h

/-- Only none gives exactly 1 prize. -/
theorem only_none_gives_one (rb : RuleBoxKind) (h : rb.prizeCount = 1) :
    rb = .none := by
  cases rb <;> simp [RuleBoxKind.prizeCount] at h ⊢

-- ============================================================
-- §11  Theorems — HP Range Validation
-- ============================================================

/-- Regular Pokémon have min HP 30. -/
theorem none_min_hp : RuleBoxKind.none.minHP = 30 := by rfl

/-- VMAX have max HP 340. -/
theorem vmax_max_hp : RuleBoxKind.vmax.maxHP = 340 := by rfl

/-- Tag Team min HP is at least 240. -/
theorem tagTeam_min_hp : RuleBoxKind.tagTeamGX.minHP = 240 := by rfl

/-- VSTAR HP range is 250-280. -/
theorem vstar_hp_range :
    RuleBoxKind.vstar.minHP = 250 ∧ RuleBoxKind.vstar.maxHP = 280 := by
  constructor <;> rfl

/-- All rule box kinds have minHP ≥ 30. -/
theorem all_minHP_at_least_30 (rb : RuleBoxKind) : rb.minHP ≥ 30 := by
  cases rb <;> simp [RuleBoxKind.minHP]

-- ============================================================
-- §12  Theorems — Once-Per-Game Mechanics
-- ============================================================

/-- Initially, GX attack is available. -/
theorem initial_gx_available :
    OncePerGameState.initial.canUseGXAttack = true := by rfl

/-- Initially, VSTAR Power is available. -/
theorem initial_vstar_available :
    OncePerGameState.initial.canUseVSTARPower = true := by rfl

/-- After using GX attack, it's no longer available. -/
theorem gx_used_not_available (s : OncePerGameState) :
    (s.useGXAttack).canUseGXAttack = false := by
  simp [OncePerGameState.useGXAttack, OncePerGameState.canUseGXAttack]

/-- After using VSTAR Power, it's no longer available. -/
theorem vstar_used_not_available (s : OncePerGameState) :
    (s.useVSTARPower).canUseVSTARPower = false := by
  simp [OncePerGameState.useVSTARPower, OncePerGameState.canUseVSTARPower]

/-- Using GX attack does not affect VSTAR Power availability. -/
theorem gx_use_preserves_vstar (s : OncePerGameState) :
    (s.useGXAttack).canUseVSTARPower = s.canUseVSTARPower := by
  simp [OncePerGameState.useGXAttack, OncePerGameState.canUseVSTARPower]

/-- Using VSTAR Power does not affect GX attack availability. -/
theorem vstar_use_preserves_gx (s : OncePerGameState) :
    (s.useVSTARPower).canUseGXAttack = s.canUseGXAttack := by
  simp [OncePerGameState.useVSTARPower, OncePerGameState.canUseGXAttack]

/-- GX attack can only be used once: use → use gives same state. -/
theorem gx_idempotent (s : OncePerGameState) :
    (s.useGXAttack).useGXAttack = s.useGXAttack := by
  simp [OncePerGameState.useGXAttack]

/-- VSTAR power can only be used once: use → use gives same state. -/
theorem vstar_idempotent (s : OncePerGameState) :
    (s.useVSTARPower).useVSTARPower = s.useVSTARPower := by
  simp [OncePerGameState.useVSTARPower]

/-- Only GX and Tag Team GX have GX attacks. -/
theorem only_gx_has_gx_attack (rb : RuleBoxKind) (h : rb.hasGXAttack = true) :
    rb = .gx ∨ rb = .tagTeamGX := by
  cases rb <;> simp [RuleBoxKind.hasGXAttack] at h ⊢

/-- Only VSTAR has VSTAR Power. -/
theorem only_vstar_has_vstar_power (rb : RuleBoxKind) (h : rb.hasVSTARPower = true) :
    rb = .vstar := by
  cases rb <;> simp [RuleBoxKind.hasVSTARPower] at h ⊢

-- ============================================================
-- §13  Theorems — Tag Team GX Bonus
-- ============================================================

/-- Total for bonus = base + threshold. -/
theorem tagTeam_bonus_total (a : TagTeamGXAttack) :
    a.totalForBonus = a.baseCostEnergy + a.bonusThreshold := by
  rfl

/-- If you can use the bonus, you can also use the base. -/
theorem bonus_implies_base (a : TagTeamGXAttack) (e : Nat)
    (h : a.canUseBonus e = true) : a.canUseBase e = true := by
  simp [TagTeamGXAttack.canUseBonus, TagTeamGXAttack.canUseBase,
        TagTeamGXAttack.totalForBonus] at h ⊢
  omega

/-- Miraculous Duo GX base needs 1 energy. -/
theorem miraculous_duo_base : miraculousDuoGX.baseCostEnergy = 1 := by rfl

/-- Miraculous Duo GX bonus needs 4 total energy. -/
theorem miraculous_duo_bonus_total : miraculousDuoGX.totalForBonus = 4 := by rfl

-- ============================================================
-- §14  Theorems — Roxanne Interaction
-- ============================================================

/-- Roxanne is playable at 3 prizes remaining. -/
theorem roxanne_at_three : roxannePlayable 3 = true := by rfl

/-- Roxanne is not playable at 4 prizes remaining. -/
theorem roxanne_not_at_four : roxannePlayable 4 = false := by rfl

/-- KO-ing a VMAX from 6 prizes leaves 3 → Roxanne playable. -/
theorem vmax_ko_enables_roxanne :
    roxannePlayable (prizesAfterKO 6 RuleBoxKind.vmax.prizeCount) = true := by native_decide

/-- KO-ing a Tag Team from 6 prizes leaves 3 → Roxanne playable. -/
theorem tagTeam_ko_enables_roxanne :
    roxannePlayable (prizesAfterKO 6 RuleBoxKind.tagTeamGX.prizeCount) = true := by native_decide

/-- KO-ing a regular Pokémon from 6 prizes leaves 5 → Roxanne not playable. -/
theorem regular_ko_no_roxanne :
    roxannePlayable (prizesAfterKO 6 RuleBoxKind.none.prizeCount) = false := by native_decide

/-- A single VMAX KO from 6 prizes DOES enable Roxanne. -/
theorem single_vmax_enables_roxanne : singleKOEnablesRoxanne .vmax = true := by native_decide

/-- A single regular KO from 6 prizes does NOT enable Roxanne. -/
theorem single_regular_no_roxanne : singleKOEnablesRoxanne .none = false := by native_decide

-- ============================================================
-- §15  Theorems — Era Classification
-- ============================================================

/-- EX (uppercase) is from the XY era. -/
theorem exUpper_xy_era : RuleBoxKind.exUpper.era = .xy := by rfl

/-- ex (lowercase) is from the SV era. -/
theorem exLower_sv_era : RuleBoxKind.exLower.era = .sv := by rfl

/-- GX is from the SM era. -/
theorem gx_sm_era : RuleBoxKind.gx.era = .sm := by rfl

/-- Tag Team GX is from the SM era. -/
theorem tagTeam_sm_era : RuleBoxKind.tagTeamGX.era = .sm := by rfl

/-- V is from the SWSH era. -/
theorem v_swsh_era : RuleBoxKind.v.era = .swsh := by rfl

/-- VMAX is from the SWSH era. -/
theorem vmax_swsh_era : RuleBoxKind.vmax.era = .swsh := by rfl

/-- VSTAR is from the SWSH era. -/
theorem vstar_swsh_era : RuleBoxKind.vstar.era = .swsh := by rfl

/-- The list of all rule box kinds has 10 entries. -/
theorem all_count : RuleBoxKind.all.length = 10 := by native_decide

end PokemonLean.Core.RuleBoxMod
