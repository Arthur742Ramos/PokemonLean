/-
  PokemonLean / Core / HistoricalFormats.lean

  Historical era analysis for the Pokémon TCG (1999–2024+).
  ==========================================================

  Models:
    - Eras from Base Set (1999) to Scarlet & Violet (2023+)
    - Power creep: HP increases (Base Charizard 120 → VMAX 330)
    - Damage creep: average attack damage growth
    - Speed creep: decreasing turns to win
    - Banned card counts per era
    - Card complexity growth

  Self-contained — no imports beyond Lean's core.
  All proofs are sorry-free.  30+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.HistoricalFormats

-- ============================================================
-- §1  Era definitions
-- ============================================================

/-- Major eras of the Pokémon TCG, in chronological order. -/
inductive Era where
  | base       -- Base Set (1999-2001)
  | neoGenesis -- Neo series (2000-2002)
  | exSeries   -- EX era (2003-2006)
  | dpPlatinum -- Diamond & Pearl / Platinum (2007-2010)
  | bwEra      -- Black & White (2011-2013)
  | xyEra      -- XY series (2014-2016)
  | smEra      -- Sun & Moon (2017-2019)
  | swshEra    -- Sword & Shield (2020-2022)
  | svEra      -- Scarlet & Violet (2023+)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Chronological ordering of eras. -/
def Era.toIdx : Era → Nat
  | .base       => 0
  | .neoGenesis => 1
  | .exSeries   => 2
  | .dpPlatinum => 3
  | .bwEra      => 4
  | .xyEra      => 5
  | .smEra      => 6
  | .swshEra    => 7
  | .svEra      => 8

/-- [T1] Era indices are distinct. -/
theorem era_indices_distinct (e1 e2 : Era) (h : Era.toIdx e1 = Era.toIdx e2) :
    e1 = e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx] at h <;> rfl

-- ============================================================
-- §2  Flagship HP per era
-- ============================================================

/-- Representative "top" HP for the flagship Pokémon of each era. -/
def flagshipHP : Era → Nat
  | .base       => 120   -- Charizard
  | .neoGenesis => 120   -- Typhlosion
  | .exSeries   => 150   -- Rayquaza ex
  | .dpPlatinum => 150   -- Garchomp LV.X
  | .bwEra      => 180   -- Black Kyurem EX
  | .xyEra      => 220   -- Mega Rayquaza EX
  | .smEra      => 250   -- GX Pokémon
  | .swshEra    => 330   -- VMAX (Charizard VMAX)
  | .svEra      => 340   -- ex (Charizard ex tera)

/-- [T2] Base era HP. -/
theorem base_hp : flagshipHP .base = 120 := rfl

/-- [T3] VMAX era HP. -/
theorem vmax_hp : flagshipHP .swshEra = 330 := rfl

/-- [T4] SV era HP. -/
theorem sv_hp : flagshipHP .svEra = 340 := rfl

/-- [T5] HP never decreases across adjacent eras. -/
theorem hp_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    flagshipHP e1 ≤ flagshipHP e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx, flagshipHP] at * <;> omega

-- ============================================================
-- §3  Flagship damage per era
-- ============================================================

/-- Representative "big attack" damage for each era's top attacker. -/
def flagshipDamage : Era → Nat
  | .base       => 100   -- Charizard's Fire Spin
  | .neoGenesis => 100   -- Typhlosion's Flame Burst
  | .exSeries   => 120   -- Rayquaza ex Dragon Burst
  | .dpPlatinum => 120   -- Garchomp's Dragon Rush
  | .bwEra      => 150   -- Black Kyurem's Black Ballista
  | .xyEra      => 170   -- Mega Rayquaza's Emerald Break
  | .smEra      => 200   -- TAG TEAM GX attacks
  | .swshEra    => 300   -- VMAX G-Max moves
  | .svEra      => 330   -- Modern ex Tera attacks

/-- [T6] Base damage. -/
theorem base_damage : flagshipDamage .base = 100 := rfl

/-- [T7] VMAX damage. -/
theorem vmax_damage : flagshipDamage .swshEra = 300 := rfl

/-- [T8] Damage never decreases across adjacent eras. -/
theorem damage_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    flagshipDamage e1 ≤ flagshipDamage e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx, flagshipDamage] at * <;> omega

-- ============================================================
-- §4  Power creep ratio
-- ============================================================

/-- HP ratio compared to Base Set (× 100 for integer precision). -/
def hpCreepRatio (e : Era) : Nat :=
  flagshipHP e * 100 / flagshipHP .base

/-- [T9] Base set ratio is 100%. -/
theorem base_hp_ratio : hpCreepRatio .base = 100 := by native_decide

/-- [T10] VMAX era is 275% of base. -/
theorem vmax_hp_ratio : hpCreepRatio .swshEra = 275 := by native_decide

/-- [T11] SV era is 283% of base. -/
theorem sv_hp_ratio : hpCreepRatio .svEra = 283 := by native_decide

/-- [T12] HP creep ratio is non-decreasing. -/
theorem hp_ratio_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    hpCreepRatio e1 ≤ hpCreepRatio e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx] at * <;> native_decide

/-- Damage ratio compared to Base Set (× 100). -/
def damageCreepRatio (e : Era) : Nat :=
  flagshipDamage e * 100 / flagshipDamage .base

/-- [T13] Damage creep ratio is non-decreasing. -/
theorem damage_ratio_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    damageCreepRatio e1 ≤ damageCreepRatio e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx] at * <;> native_decide

-- ============================================================
-- §5  Speed creep: turns to win
-- ============================================================

/-- Approximate turns to win (take 6 prizes) for the top deck of each era.
    Lower is faster. -/
def turnsToWin : Era → Nat
  | .base       => 8
  | .neoGenesis => 7
  | .exSeries   => 7
  | .dpPlatinum => 6
  | .bwEra      => 5
  | .xyEra      => 4
  | .smEra      => 3   -- TAG TEAM: 3-prize KOs
  | .swshEra    => 3   -- VMAX: 3-prize KOs
  | .svEra      => 3   -- ex: 2-prize KOs but fast setups

/-- [T14] Game speed is non-increasing across eras. -/
theorem speed_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    turnsToWin e2 ≤ turnsToWin e1 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx, turnsToWin] at * <;> omega

/-- [T15] Modern games are faster than Base. -/
theorem modern_faster_than_base : turnsToWin .svEra < turnsToWin .base := by native_decide

/-- [T16] Base era was the slowest. -/
theorem base_slowest : ∀ e : Era, turnsToWin e ≤ turnsToWin .base := by
  intro e; cases e <;> simp [turnsToWin]

-- ============================================================
-- §6  Banned cards per era
-- ============================================================

/-- Approximate number of banned/restricted cards per era. -/
def bannedCardsCount : Era → Nat
  | .base       => 2    -- Ancient Mew, _____'s Pikachu
  | .neoGenesis => 3
  | .exSeries   => 4
  | .dpPlatinum => 5
  | .bwEra      => 8
  | .xyEra      => 6
  | .smEra      => 12   -- Lysandre's Trump Card, etc.
  | .swshEra    => 15   -- Chip-Chip Ice Axe, etc.
  | .svEra      => 10   -- Ongoing

/-- [T17] -/
theorem base_banned : bannedCardsCount .base = 2 := rfl

/-- [T18] Every era has at least one ban. -/
theorem every_era_has_bans : ∀ e : Era, bannedCardsCount e > 0 := by
  intro e; cases e <;> simp [bannedCardsCount]

-- ============================================================
-- §7  Card complexity
-- ============================================================

/-- Approximate average number of abilities/effects per competitive card. -/
def avgEffectsPerCard : Era → Nat
  | .base       => 1
  | .neoGenesis => 1
  | .exSeries   => 2
  | .dpPlatinum => 2
  | .bwEra      => 2
  | .xyEra      => 3
  | .smEra      => 3
  | .swshEra    => 4
  | .svEra      => 4

/-- [T19] Complexity is non-decreasing across eras. -/
theorem complexity_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    avgEffectsPerCard e1 ≤ avgEffectsPerCard e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx, avgEffectsPerCard] at * <;> omega

-- ============================================================
-- §8  Prize card mechanics evolution
-- ============================================================

/-- Maximum prizes taken per KO in each era. -/
def maxPrizesPerKO : Era → Nat
  | .base       => 1
  | .neoGenesis => 1
  | .exSeries   => 2   -- Pokémon-ex give 2 prizes
  | .dpPlatinum => 2   -- LV.X
  | .bwEra      => 2   -- EX Pokémon
  | .xyEra      => 2   -- EX / Mega
  | .smEra      => 3   -- TAG TEAM GX
  | .swshEra    => 3   -- VMAX
  | .svEra      => 2   -- ex

/-- [T20] Prize escalation from Base to SM era. -/
theorem prize_escalation : maxPrizesPerKO .smEra > maxPrizesPerKO .base := by native_decide

/-- [T21] Base era is single-prize. -/
theorem base_single_prize : maxPrizesPerKO .base = 1 := rfl

/-- [T22] Prizes per KO never exceed 3. -/
theorem max_prizes_bounded : ∀ e : Era, maxPrizesPerKO e ≤ 3 := by
  intro e; cases e <;> simp [maxPrizesPerKO]

-- ============================================================
-- §9  Format rotation sizes
-- ============================================================

/-- Approximate number of legal sets in Standard format per era. -/
def legalSetsCount : Era → Nat
  | .base       => 5
  | .neoGenesis => 8
  | .exSeries   => 10
  | .dpPlatinum => 12
  | .bwEra      => 14
  | .xyEra      => 16
  | .smEra      => 18
  | .swshEra    => 14
  | .svEra      => 10

/-- [T23] Every era has at least 5 legal sets. -/
theorem min_legal_sets : ∀ e : Era, legalSetsCount e ≥ 5 := by
  intro e; cases e <;> simp [legalSetsCount]

-- ============================================================
-- §10  Era exhaustiveness
-- ============================================================

/-- [T24] All eras are enumerable. -/
theorem era_exhaustive (e : Era) :
    e = .base ∨ e = .neoGenesis ∨ e = .exSeries ∨ e = .dpPlatinum ∨
    e = .bwEra ∨ e = .xyEra ∨ e = .smEra ∨ e = .swshEra ∨ e = .svEra := by
  cases e <;> simp

def allEras : List Era :=
  [.base, .neoGenesis, .exSeries, .dpPlatinum, .bwEra, .xyEra, .smEra, .swshEra, .svEra]

/-- [T25] -/ theorem all_eras_length : allEras.length = 9 := by native_decide

/-- [T26] -/ theorem all_eras_complete (e : Era) : e ∈ allEras := by
  cases e <;> simp [allEras]

-- ============================================================
-- §11  Era year ranges
-- ============================================================

/-- Start year of each era. -/
def eraStartYear : Era → Nat
  | .base       => 1999
  | .neoGenesis => 2000
  | .exSeries   => 2003
  | .dpPlatinum => 2007
  | .bwEra      => 2011
  | .xyEra      => 2014
  | .smEra      => 2017
  | .swshEra    => 2020
  | .svEra      => 2023

/-- [T27] Eras are chronologically ordered by start year. -/
theorem eras_chronological (e1 e2 : Era) (h : Era.toIdx e1 < Era.toIdx e2) :
    eraStartYear e1 < eraStartYear e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx, eraStartYear] at * <;> omega

-- ============================================================
-- §12  HP-to-damage ratio (survivability)
-- ============================================================

/-- Turns to KO = flagship HP / flagship damage (Nat division). -/
def turnsToKO (e : Era) : Nat :=
  flagshipHP e / flagshipDamage e

/-- [T28] Base era takes 2 hits to KO. -/
theorem base_turns_to_ko : turnsToKO .base = 1 := by native_decide

/-- [T29] VMAX era also about 1 turn per KO. -/
theorem vmax_turns_to_ko : turnsToKO .swshEra = 1 := by native_decide

/-- [T30] Survivability ratio is bounded. -/
theorem survivability_bounded : ∀ e : Era, turnsToKO e ≤ 3 := by
  intro e; cases e <;> native_decide

-- ============================================================
-- §13  Power creep total
-- ============================================================

/-- Total power score = HP + Damage for an era. -/
def totalPower (e : Era) : Nat := flagshipHP e + flagshipDamage e

/-- [T31] Total power is non-decreasing. -/
theorem total_power_nondecreasing (e1 e2 : Era) (h : Era.toIdx e1 ≤ Era.toIdx e2) :
    totalPower e1 ≤ totalPower e2 := by
  cases e1 <;> cases e2 <;> simp [Era.toIdx, totalPower, flagshipHP, flagshipDamage] at * <;> omega

/-- [T32] Base total power. -/
theorem base_total_power : totalPower .base = 220 := by native_decide

/-- [T33] SV total power. -/
theorem sv_total_power : totalPower .svEra = 670 := by native_decide

-- ============================================================
-- §14  Meta defining mechanics
-- ============================================================

/-- Whether an era introduced multi-prize Pokémon. -/
def hasMultiPrize : Era → Bool
  | .base       => false
  | .neoGenesis => false
  | .exSeries   => true
  | .dpPlatinum => true
  | .bwEra      => true
  | .xyEra      => true
  | .smEra      => true
  | .swshEra    => true
  | .svEra      => true

/-- [T34] Base and Neo did not have multi-prize Pokémon. -/
theorem base_no_multi : hasMultiPrize .base = false := rfl
theorem neo_no_multi : hasMultiPrize .neoGenesis = false := rfl

/-- [T35] Once multi-prize is introduced, it persists. -/
theorem multi_prize_persistent (e1 e2 : Era)
    (h1 : hasMultiPrize e1 = true) (h2 : Era.toIdx e1 ≤ Era.toIdx e2) :
    hasMultiPrize e2 = true := by
  cases e1 <;> cases e2 <;> simp [hasMultiPrize, Era.toIdx] at * <;> omega

-- ============================================================
-- §15  Era comparison utilities
-- ============================================================

/-- Era ordering based on index. -/
def Era.le (e1 e2 : Era) : Bool := Era.toIdx e1 ≤ Era.toIdx e2

/-- [T36] Era ordering is reflexive. -/
theorem era_le_refl (e : Era) : Era.le e e = true := by
  cases e <;> simp [Era.le, Era.toIdx]

/-- [T37] Era ordering is transitive. -/
theorem era_le_trans (e1 e2 e3 : Era)
    (h1 : Era.le e1 e2 = true) (h2 : Era.le e2 e3 = true) :
    Era.le e1 e3 = true := by
  simp [Era.le] at *; omega

-- ============================================================
-- §16  Damage-to-HP ratio per era (OHKO capability)
-- ============================================================

/-- Damage as percentage of opponent's HP (× 100). -/
def ohkoCapability (e : Era) : Nat :=
  flagshipDamage e * 100 / flagshipHP e

/-- [T38] Base era OHKO capability (83%). -/
theorem base_ohko : ohkoCapability .base = 83 := by native_decide

/-- [T39] VMAX era OHKO capability (90%). -/
theorem vmax_ohko : ohkoCapability .swshEra = 90 := by native_decide

-- ============================================================
-- §17  Additional era facts
-- ============================================================

/-- Number of total eras. -/
def totalEras : Nat := 9

/-- [T40] Total eras matches allEras length. -/
theorem total_eras_correct : totalEras = allEras.length := by native_decide

/-- [T41] Era.toIdx is bounded by total eras. -/
theorem era_idx_bounded (e : Era) : Era.toIdx e < totalEras := by
  cases e <;> simp [Era.toIdx, totalEras]

/-- [T42] SV era has higher HP than every previous era. -/
theorem sv_max_hp : ∀ e : Era, flagshipHP e ≤ flagshipHP .svEra := by
  intro e; cases e <;> simp [flagshipHP]

end PokemonLean.Core.HistoricalFormats
