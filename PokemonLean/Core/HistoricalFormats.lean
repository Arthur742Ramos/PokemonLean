/-
  PokemonLean / Core / HistoricalFormats.lean
  Historical format analysis across Pokemon TCG eras.
  35+ theorems, zero sorry.
-/
set_option linter.unusedVariables false
namespace PokemonLean.Core.HistoricalFormats

-- §1 Era definitions
inductive Era where
  | baseFossil | neo | eCard | exSeries | dp | hgss | bw | xy | sm | swsh | sv
  deriving DecidableEq, Repr, BEq, Inhabited

def Era.toIdx : Era → Nat
  | .baseFossil => 0 | .neo => 1 | .eCard => 2 | .exSeries => 3
  | .dp => 4 | .hgss => 5 | .bw => 6 | .xy => 7
  | .sm => 8 | .swsh => 9 | .sv => 10

def Era.fromIdx : Fin 11 → Era
  | ⟨0,_⟩ => .baseFossil | ⟨1,_⟩ => .neo | ⟨2,_⟩ => .eCard | ⟨3,_⟩ => .exSeries
  | ⟨4,_⟩ => .dp | ⟨5,_⟩ => .hgss | ⟨6,_⟩ => .bw | ⟨7,_⟩ => .xy
  | ⟨8,_⟩ => .sm | ⟨9,_⟩ => .swsh | ⟨10,_⟩ => .sv

theorem era_roundtrip (e : Era) :
    Era.fromIdx ⟨e.toIdx, by cases e <;> simp [Era.toIdx]⟩ = e := by
  cases e <;> rfl

-- §2 Start years
def Era.startYear : Era → Nat
  | .baseFossil => 1999 | .neo => 2000 | .eCard => 2002 | .exSeries => 2003
  | .dp => 2007 | .hgss => 2010 | .bw => 2011 | .xy => 2013
  | .sm => 2017 | .swsh => 2020 | .sv => 2023

theorem chrono_base_neo : Era.startYear .baseFossil < Era.startYear .neo := by native_decide
theorem chrono_neo_ecard : Era.startYear .neo < Era.startYear .eCard := by native_decide
theorem chrono_ecard_ex : Era.startYear .eCard < Era.startYear .exSeries := by native_decide
theorem chrono_ex_dp : Era.startYear .exSeries < Era.startYear .dp := by native_decide
theorem chrono_dp_hgss : Era.startYear .dp < Era.startYear .hgss := by native_decide
theorem chrono_hgss_bw : Era.startYear .hgss < Era.startYear .bw := by native_decide
theorem chrono_bw_xy : Era.startYear .bw < Era.startYear .xy := by native_decide
theorem chrono_xy_sm : Era.startYear .xy < Era.startYear .sm := by native_decide
theorem chrono_sm_swsh : Era.startYear .sm < Era.startYear .swsh := by native_decide
theorem chrono_swsh_sv : Era.startYear .swsh < Era.startYear .sv := by native_decide

-- §3 HP metrics
def Era.avgHP : Era → Nat
  | .baseFossil => 80 | .neo => 90 | .eCard => 100 | .exSeries => 110
  | .dp => 120 | .hgss => 130 | .bw => 140 | .xy => 170
  | .sm => 190 | .swsh => 250 | .sv => 280

def charizardHP : Era → Nat
  | .baseFossil => 120 | .neo => 120 | .eCard => 120 | .exSeries => 160
  | .dp => 150 | .hgss => 140 | .bw => 160 | .xy => 230
  | .sm => 250 | .swsh => 330 | .sv => 330

theorem charizard_base : charizardHP .baseFossil = 120 := rfl
theorem charizard_vmax : charizardHP .swsh = 330 := rfl
theorem charizard_ratio : 330 * 100 / 120 = 275 := by native_decide

theorem hp_mono_01 : Era.avgHP .baseFossil <= Era.avgHP .neo := by native_decide
theorem hp_mono_12 : Era.avgHP .neo <= Era.avgHP .eCard := by native_decide
theorem hp_mono_23 : Era.avgHP .eCard <= Era.avgHP .exSeries := by native_decide
theorem hp_mono_34 : Era.avgHP .exSeries <= Era.avgHP .dp := by native_decide
theorem hp_mono_45 : Era.avgHP .dp <= Era.avgHP .hgss := by native_decide
theorem hp_mono_56 : Era.avgHP .hgss <= Era.avgHP .bw := by native_decide
theorem hp_mono_67 : Era.avgHP .bw <= Era.avgHP .xy := by native_decide
theorem hp_mono_78 : Era.avgHP .xy <= Era.avgHP .sm := by native_decide
theorem hp_mono_89 : Era.avgHP .sm <= Era.avgHP .swsh := by native_decide
theorem hp_mono_9a : Era.avgHP .swsh <= Era.avgHP .sv := by native_decide

-- §4 Damage metrics
def Era.avgDmg : Era → Nat
  | .baseFossil => 60 | .neo => 70 | .eCard => 80 | .exSeries => 100
  | .dp => 110 | .hgss => 120 | .bw => 140 | .xy => 170
  | .sm => 200 | .swsh => 260 | .sv => 280

def charizardDmg : Era → Nat
  | .baseFossil => 100 | .neo => 100 | .eCard => 120 | .exSeries => 200
  | .dp => 150 | .hgss => 150 | .bw => 150 | .xy => 300
  | .sm => 300 | .swsh => 300 | .sv => 330

theorem charizard_dmg_creep : charizardDmg .swsh = 3 * charizardDmg .baseFossil := by native_decide

theorem dmg_mono_01 : Era.avgDmg .baseFossil <= Era.avgDmg .neo := by native_decide
theorem dmg_mono_12 : Era.avgDmg .neo <= Era.avgDmg .eCard := by native_decide
theorem dmg_mono_23 : Era.avgDmg .eCard <= Era.avgDmg .exSeries := by native_decide
theorem dmg_mono_34 : Era.avgDmg .exSeries <= Era.avgDmg .dp := by native_decide
theorem dmg_mono_45 : Era.avgDmg .dp <= Era.avgDmg .hgss := by native_decide
theorem dmg_mono_56 : Era.avgDmg .hgss <= Era.avgDmg .bw := by native_decide
theorem dmg_mono_67 : Era.avgDmg .bw <= Era.avgDmg .xy := by native_decide
theorem dmg_mono_78 : Era.avgDmg .xy <= Era.avgDmg .sm := by native_decide
theorem dmg_mono_89 : Era.avgDmg .sm <= Era.avgDmg .swsh := by native_decide
theorem dmg_mono_9a : Era.avgDmg .swsh <= Era.avgDmg .sv := by native_decide

-- §5 Speed creep
def Era.avgTurns : Era → Nat
  | .baseFossil => 20 | .neo => 18 | .eCard => 17 | .exSeries => 15
  | .dp => 14 | .hgss => 13 | .bw => 12 | .xy => 11
  | .sm => 10 | .swsh => 8 | .sv => 7

theorem turns_mono_01 : Era.avgTurns .neo <= Era.avgTurns .baseFossil := by native_decide
theorem turns_mono_12 : Era.avgTurns .eCard <= Era.avgTurns .neo := by native_decide
theorem turns_mono_23 : Era.avgTurns .exSeries <= Era.avgTurns .eCard := by native_decide
theorem turns_mono_34 : Era.avgTurns .dp <= Era.avgTurns .exSeries := by native_decide
theorem turns_mono_45 : Era.avgTurns .hgss <= Era.avgTurns .dp := by native_decide
theorem turns_mono_56 : Era.avgTurns .bw <= Era.avgTurns .hgss := by native_decide
theorem turns_mono_67 : Era.avgTurns .xy <= Era.avgTurns .bw := by native_decide
theorem turns_mono_78 : Era.avgTurns .sm <= Era.avgTurns .xy := by native_decide
theorem turns_mono_89 : Era.avgTurns .swsh <= Era.avgTurns .sm := by native_decide
theorem turns_mono_9a : Era.avgTurns .sv <= Era.avgTurns .swsh := by native_decide

-- §6 Prize value
def Era.avgPrizeValue : Era → Nat
  | .baseFossil => 1 | .neo => 1 | .eCard => 1 | .exSeries => 1
  | .dp => 1 | .hgss => 1 | .bw => 2 | .xy => 2
  | .sm => 2 | .swsh => 2 | .sv => 2

theorem prize_mono_bw : Era.avgPrizeValue .bw >= Era.avgPrizeValue .hgss := by native_decide
theorem prize_mono_xy : Era.avgPrizeValue .xy >= Era.avgPrizeValue .bw := by native_decide
theorem prize_mono_sm : Era.avgPrizeValue .sm >= Era.avgPrizeValue .xy := by native_decide

-- §7 Power creep ratio
def powerCreepRatio (newV baseV : Nat) : Nat :=
  if baseV = 0 then 0 else newV * 100 / baseV

theorem creep_ratio_self (v : Nat) (h : v > 0) : powerCreepRatio v v = 100 := by
  simp [powerCreepRatio, Nat.ne_of_gt h]
  exact Nat.mul_div_cancel_left 100 h

theorem hp_creep_base_sv : powerCreepRatio (Era.avgHP .sv) (Era.avgHP .baseFossil) = 350 := by
  native_decide

theorem dmg_creep_base_sv : powerCreepRatio (Era.avgDmg .sv) (Era.avgDmg .baseFossil) = 466 := by
  native_decide

-- §8 Banned cards
structure BanEntry where
  cardName : String
  era : Era
  reason : String
  deriving Repr

def bannedCards : List BanEntry :=
  [ BanEntry.mk "Sneasel" .neo "60 damage for 0 energy with full bench"
  , BanEntry.mk "Slowking" .neo "Translation error made ability too powerful"
  , BanEntry.mk "Lysandres Trump Card" .xy "Infinite resources broke design"
  , BanEntry.mk "Forest of Giant Plants" .sm "T1 evolutions too fast"
  , BanEntry.mk "Lt. Surges Strategy" .sm "Multiple supporters per turn"
  , BanEntry.mk "Chip-Chip Ice Axe" .swsh "Softlock with control"
  , BanEntry.mk "Oranguru" .swsh "Infinite loop with control decks" ]

theorem banned_nonempty : bannedCards.length > 0 := by native_decide
theorem banned_count : bannedCards.length = 7 := by native_decide

-- §9 Rotation history
structure RotationEvent where
  year : Nat
  description : String
  newLegalFrom : String
  deriving Repr

def rotationHistory : List RotationEvent :=
  [ RotationEvent.mk 2017 "XY Primal-AO rotated" "BREAKthrough-on"
  , RotationEvent.mk 2018 "BREAKthrough-FC rotated" "BUS-on"
  , RotationEvent.mk 2019 "XY Evo + SM base-CRI rotated" "TEU-on"
  , RotationEvent.mk 2020 "SM UP-LOT rotated" "SSH-on"
  , RotationEvent.mk 2022 "SM TEU-CEC rotated" "BST-on"
  , RotationEvent.mk 2023 "SWSH base-BRS rotated" "SVI-on"
  , RotationEvent.mk 2024 "SWSH ASR-CRZ rotated" "PAL-on" ]

theorem rotation_nonempty : rotationHistory.length > 0 := by native_decide

-- §10 Setup speed
def Era.setupTurns : Era → Nat
  | .baseFossil => 4 | .neo => 3 | .eCard => 3 | .exSeries => 2
  | .dp => 3 | .hgss => 2 | .bw => 2 | .xy => 2
  | .sm => 2 | .swsh => 1 | .sv => 1

theorem setup_faster : Era.setupTurns .swsh < Era.setupTurns .baseFossil := by native_decide

-- §11 Era comparison
def Era.isBefore (a b : Era) : Bool := a.toIdx < b.toIdx
theorem base_before_sv : Era.isBefore .baseFossil .sv = true := by native_decide
theorem sv_not_before_base : Era.isBefore .sv .baseFossil = false := by native_decide

def eraDiff (a b : Era) : Nat :=
  if a.toIdx <= b.toIdx then b.toIdx - a.toIdx else a.toIdx - b.toIdx

theorem base_to_sv_diff : eraDiff .baseFossil .sv = 10 := by native_decide
theorem era_diff_sym (a b : Era) : eraDiff a b = eraDiff b a := by
  simp [eraDiff]; split <;> split <;> omega

-- §12 Format legality
def isExpandedLegal (e : Era) : Bool := e.toIdx >= 6
def isStandardLegal (e : Era) : Bool := e.toIdx >= 10

theorem bw_expanded : isExpandedLegal .bw = true := by native_decide
theorem ex_not_expanded : isExpandedLegal .exSeries = false := by native_decide
theorem sv_standard : isStandardLegal .sv = true := by native_decide
theorem swsh_not_standard : isStandardLegal .swsh = false := by native_decide

theorem standard_implies_expanded (e : Era) :
    isStandardLegal e = true → isExpandedLegal e = true := by
  cases e <;> simp [isStandardLegal, isExpandedLegal, Era.toIdx]

-- §13 Overall monotonicity
theorem hp_monotone_all :
    Era.avgHP .baseFossil <= Era.avgHP .neo ∧
    Era.avgHP .neo <= Era.avgHP .eCard ∧
    Era.avgHP .eCard <= Era.avgHP .exSeries ∧
    Era.avgHP .exSeries <= Era.avgHP .dp ∧
    Era.avgHP .dp <= Era.avgHP .hgss ∧
    Era.avgHP .hgss <= Era.avgHP .bw ∧
    Era.avgHP .bw <= Era.avgHP .xy ∧
    Era.avgHP .xy <= Era.avgHP .sm ∧
    Era.avgHP .sm <= Era.avgHP .swsh ∧
    Era.avgHP .swsh <= Era.avgHP .sv := by
  simp [Era.avgHP]

theorem dmg_monotone_all :
    Era.avgDmg .baseFossil <= Era.avgDmg .neo ∧
    Era.avgDmg .neo <= Era.avgDmg .eCard ∧
    Era.avgDmg .eCard <= Era.avgDmg .exSeries ∧
    Era.avgDmg .exSeries <= Era.avgDmg .dp ∧
    Era.avgDmg .dp <= Era.avgDmg .hgss ∧
    Era.avgDmg .hgss <= Era.avgDmg .bw ∧
    Era.avgDmg .bw <= Era.avgDmg .xy ∧
    Era.avgDmg .xy <= Era.avgDmg .sm ∧
    Era.avgDmg .sm <= Era.avgDmg .swsh ∧
    Era.avgDmg .swsh <= Era.avgDmg .sv := by
  simp [Era.avgDmg]

-- §14 Hits to KO
def hitsToKO (hp dmg : Nat) : Nat :=
  if dmg = 0 then 0 else (hp + dmg - 1) / dmg

theorem base_charizard_2hit : hitsToKO 120 100 = 2 := by native_decide
theorem vmax_charizard_2hit : hitsToKO 330 200 = 2 := by native_decide
theorem ohko_equal : hitsToKO 330 330 = 1 := by native_decide

theorem hits_pos (hp dmg : Nat) (hHP : hp > 0) (hDmg : dmg > 0) :
    hitsToKO hp dmg >= 1 := by
  unfold hitsToKO
  rw [if_neg (by omega)]
  apply Nat.div_pos
  · omega
  · exact hDmg

-- §15 Era lists
def allEras : List Era :=
  [.baseFossil, .neo, .eCard, .exSeries, .dp, .hgss, .bw, .xy, .sm, .swsh, .sv]
theorem all_eras_len : allEras.length = 11 := by native_decide

def totalAvgHP : Nat := allEras.foldl (fun a e => a + e.avgHP) 0
theorem total_hp : totalAvgHP = 1660 := by native_decide

def totalAvgDmg : Nat := allEras.foldl (fun a e => a + e.avgDmg) 0
theorem total_dmg : totalAvgDmg = 1590 := by native_decide

-- §16 Cross-era balance
def Era.hitsToKOAvg (e : Era) : Nat := hitsToKO e.avgHP e.avgDmg
theorem balance_base : Era.hitsToKOAvg .baseFossil = 2 := by native_decide
theorem balance_sv : Era.hitsToKOAvg .sv = 1 := by native_decide

-- §17 Extrema
theorem sv_highest_hp (e : Era) : Era.avgHP e <= Era.avgHP .sv := by
  cases e <;> simp [Era.avgHP]

theorem sv_highest_dmg (e : Era) : Era.avgDmg e <= Era.avgDmg .sv := by
  cases e <;> simp [Era.avgDmg]

theorem base_lowest_hp (e : Era) : Era.avgHP .baseFossil <= Era.avgHP e := by
  cases e <;> simp [Era.avgHP]

theorem base_longest_game (e : Era) : Era.avgTurns e <= Era.avgTurns .baseFossil := by
  cases e <;> simp [Era.avgTurns]

theorem sv_shortest_game (e : Era) : Era.avgTurns .sv <= Era.avgTurns e := by
  cases e <;> simp [Era.avgTurns]

end PokemonLean.Core.HistoricalFormats
