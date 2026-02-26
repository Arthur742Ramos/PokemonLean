import PokemonLean.Basic
import Std.Tactic

namespace PokemonLean.Format

open PokemonLean

-- ============================================================================
-- FORMATS
-- ============================================================================

inductive TCGFormat
  | standard
  | expanded
  | unlimited
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- SETS & RELEASE DATES
-- ============================================================================

structure ReleaseDate where
  year : Nat
  month : Nat
  day : Nat
  deriving Repr, BEq, DecidableEq

def releaseDateCode (date : ReleaseDate) : Nat :=
  date.year * 10000 + date.month * 100 + date.day

def releaseDateBeforeOrOn (left right : ReleaseDate) : Prop :=
  releaseDateCode left ≤ releaseDateCode right

instance (left right : ReleaseDate) : Decidable (releaseDateBeforeOrOn left right) := by
  unfold releaseDateBeforeOrOn
  infer_instance

@[simp] theorem releaseDateCode_mk (year month day : Nat) :
    releaseDateCode { year := year, month := month, day := day } =
      year * 10000 + month * 100 + day := rfl

theorem releaseDateBeforeOrOn_refl (date : ReleaseDate) :
    releaseDateBeforeOrOn date date := by
  simp [releaseDateBeforeOrOn]

theorem releaseDateBeforeOrOn_trans (a b c : ReleaseDate)
    (h₁ : releaseDateBeforeOrOn a b) (h₂ : releaseDateBeforeOrOn b c) :
    releaseDateBeforeOrOn a c := by
  exact Nat.le_trans h₁ h₂

theorem releaseDateBeforeOrOn_antisymm (a b : ReleaseDate)
    (h₁ : releaseDateBeforeOrOn a b) (h₂ : releaseDateBeforeOrOn b a) :
    releaseDateCode a = releaseDateCode b := by
  exact Nat.le_antisymm h₁ h₂

inductive TCGSet
  | baseSet
  | blackWhiteBase
  | boundariesCrossed
  | plasmaStorm
  | xyBase
  | sunMoonBase
  | swordShieldBase
  | brilliantStars
  | silverTempest
  | scarletViolet
  | paldeaEvolved
  | obsidianFlames
  | paradoxRift
  | temporalForces
  | twilightMasquerade
  | stellarCrown
  deriving Repr, BEq, DecidableEq

def setReleaseDate : TCGSet → ReleaseDate
  | .baseSet => { year := 1999, month := 1, day := 9 }
  | .blackWhiteBase => { year := 2011, month := 4, day := 25 }
  | .boundariesCrossed => { year := 2012, month := 11, day := 7 }
  | .plasmaStorm => { year := 2013, month := 2, day := 6 }
  | .xyBase => { year := 2014, month := 2, day := 5 }
  | .sunMoonBase => { year := 2017, month := 2, day := 3 }
  | .swordShieldBase => { year := 2020, month := 2, day := 7 }
  | .brilliantStars => { year := 2022, month := 2, day := 25 }
  | .silverTempest => { year := 2022, month := 11, day := 11 }
  | .scarletViolet => { year := 2023, month := 3, day := 31 }
  | .paldeaEvolved => { year := 2023, month := 6, day := 9 }
  | .obsidianFlames => { year := 2023, month := 8, day := 11 }
  | .paradoxRift => { year := 2023, month := 11, day := 3 }
  | .temporalForces => { year := 2024, month := 3, day := 22 }
  | .twilightMasquerade => { year := 2024, month := 5, day := 24 }
  | .stellarCrown => { year := 2024, month := 9, day := 13 }

@[simp] theorem setReleaseDate_baseSet :
    setReleaseDate .baseSet = { year := 1999, month := 1, day := 9 } := rfl
@[simp] theorem setReleaseDate_blackWhiteBase :
    setReleaseDate .blackWhiteBase = { year := 2011, month := 4, day := 25 } := rfl
@[simp] theorem setReleaseDate_boundariesCrossed :
    setReleaseDate .boundariesCrossed = { year := 2012, month := 11, day := 7 } := rfl
@[simp] theorem setReleaseDate_plasmaStorm :
    setReleaseDate .plasmaStorm = { year := 2013, month := 2, day := 6 } := rfl
@[simp] theorem setReleaseDate_xyBase :
    setReleaseDate .xyBase = { year := 2014, month := 2, day := 5 } := rfl
@[simp] theorem setReleaseDate_sunMoonBase :
    setReleaseDate .sunMoonBase = { year := 2017, month := 2, day := 3 } := rfl
@[simp] theorem setReleaseDate_swordShieldBase :
    setReleaseDate .swordShieldBase = { year := 2020, month := 2, day := 7 } := rfl
@[simp] theorem setReleaseDate_brilliantStars :
    setReleaseDate .brilliantStars = { year := 2022, month := 2, day := 25 } := rfl
@[simp] theorem setReleaseDate_silverTempest :
    setReleaseDate .silverTempest = { year := 2022, month := 11, day := 11 } := rfl
@[simp] theorem setReleaseDate_scarletViolet :
    setReleaseDate .scarletViolet = { year := 2023, month := 3, day := 31 } := rfl
@[simp] theorem setReleaseDate_paldeaEvolved :
    setReleaseDate .paldeaEvolved = { year := 2023, month := 6, day := 9 } := rfl
@[simp] theorem setReleaseDate_obsidianFlames :
    setReleaseDate .obsidianFlames = { year := 2023, month := 8, day := 11 } := rfl
@[simp] theorem setReleaseDate_paradoxRift :
    setReleaseDate .paradoxRift = { year := 2023, month := 11, day := 3 } := rfl
@[simp] theorem setReleaseDate_temporalForces :
    setReleaseDate .temporalForces = { year := 2024, month := 3, day := 22 } := rfl
@[simp] theorem setReleaseDate_twilightMasquerade :
    setReleaseDate .twilightMasquerade = { year := 2024, month := 5, day := 24 } := rfl
@[simp] theorem setReleaseDate_stellarCrown :
    setReleaseDate .stellarCrown = { year := 2024, month := 9, day := 13 } := rfl


-- ============================================================================
-- ERAS
-- ============================================================================

inductive SetEra
  | preBW
  | blackWhite
  | xy
  | sunMoon
  | swordShield
  | scarletViolet
  deriving Repr, BEq, DecidableEq

def setEra : TCGSet → SetEra
  | .baseSet => .preBW
  | .blackWhiteBase => .blackWhite
  | .boundariesCrossed => .blackWhite
  | .plasmaStorm => .blackWhite
  | .xyBase => .xy
  | .sunMoonBase => .sunMoon
  | .swordShieldBase => .swordShield
  | .brilliantStars => .swordShield
  | .silverTempest => .swordShield
  | .scarletViolet => .scarletViolet
  | .paldeaEvolved => .scarletViolet
  | .obsidianFlames => .scarletViolet
  | .paradoxRift => .scarletViolet
  | .temporalForces => .scarletViolet
  | .twilightMasquerade => .scarletViolet
  | .stellarCrown => .scarletViolet

@[simp] theorem setEra_baseSet : setEra .baseSet = .preBW := rfl
@[simp] theorem setEra_blackWhiteBase : setEra .blackWhiteBase = .blackWhite := rfl
@[simp] theorem setEra_xyBase : setEra .xyBase = .xy := rfl
@[simp] theorem setEra_sunMoonBase : setEra .sunMoonBase = .sunMoon := rfl
@[simp] theorem setEra_swordShieldBase : setEra .swordShieldBase = .swordShield := rfl
@[simp] theorem setEra_scarletViolet : setEra .scarletViolet = .scarletViolet := rfl
@[simp] theorem setEra_stellarCrown : setEra .stellarCrown = .scarletViolet := rfl

-- ============================================================================
-- FORMAT SET LEGALITY
-- ============================================================================

def standardCutoff : ReleaseDate := { year := 2023, month := 1, day := 1 }

def recentSet (set : TCGSet) : Bool :=
  decide (releaseDateBeforeOrOn standardCutoff (setReleaseDate set))

def legalSetInStandard : TCGSet → Bool
  | .scarletViolet
  | .paldeaEvolved
  | .obsidianFlames
  | .paradoxRift
  | .temporalForces
  | .twilightMasquerade
  | .stellarCrown => true
  | _ => false

def legalSetInExpanded (set : TCGSet) : Bool :=
  match setEra set with
  | .preBW => false
  | _ => true

def legalSetInUnlimited (_set : TCGSet) : Bool := true

def legalSetInFormat (format : TCGFormat) (set : TCGSet) : Bool :=
  match format with
  | .standard => legalSetInStandard set
  | .expanded => legalSetInExpanded set
  | .unlimited => legalSetInUnlimited set

@[simp] theorem legalSetInStandard_scarletViolet :
    legalSetInStandard .scarletViolet = true := rfl
@[simp] theorem legalSetInStandard_paldeaEvolved :
    legalSetInStandard .paldeaEvolved = true := rfl
@[simp] theorem legalSetInStandard_obsidianFlames :
    legalSetInStandard .obsidianFlames = true := rfl
@[simp] theorem legalSetInStandard_paradoxRift :
    legalSetInStandard .paradoxRift = true := rfl
@[simp] theorem legalSetInStandard_temporalForces :
    legalSetInStandard .temporalForces = true := rfl
@[simp] theorem legalSetInStandard_twilightMasquerade :
    legalSetInStandard .twilightMasquerade = true := rfl
@[simp] theorem legalSetInStandard_stellarCrown :
    legalSetInStandard .stellarCrown = true := rfl
@[simp] theorem legalSetInStandard_baseSet :
    legalSetInStandard .baseSet = false := rfl
@[simp] theorem legalSetInStandard_blackWhiteBase :
    legalSetInStandard .blackWhiteBase = false := rfl
@[simp] theorem legalSetInStandard_swordShieldBase :
    legalSetInStandard .swordShieldBase = false := rfl

@[simp] theorem legalSetInExpanded_baseSet :
    legalSetInExpanded .baseSet = false := rfl
@[simp] theorem legalSetInExpanded_blackWhiteBase :
    legalSetInExpanded .blackWhiteBase = true := rfl
@[simp] theorem legalSetInExpanded_scarletViolet :
    legalSetInExpanded .scarletViolet = true := rfl

@[simp] theorem legalSetInUnlimited_any (set : TCGSet) :
    legalSetInUnlimited set = true := rfl

@[simp] theorem legalSetInFormat_standard (set : TCGSet) :
    legalSetInFormat .standard set = legalSetInStandard set := rfl
@[simp] theorem legalSetInFormat_expanded (set : TCGSet) :
    legalSetInFormat .expanded set = legalSetInExpanded set := rfl
@[simp] theorem legalSetInFormat_unlimited (set : TCGSet) :
    legalSetInFormat .unlimited set = legalSetInUnlimited set := rfl

theorem legalSetInStandard_implies_recent (set : TCGSet)
    (h : legalSetInStandard set = true) :
    recentSet set = true := by
  cases set <;>
    simp [legalSetInStandard, recentSet, standardCutoff, releaseDateBeforeOrOn, releaseDateCode] at h ⊢

theorem legalSetInExpanded_iff_bw_plus (set : TCGSet) :
    legalSetInExpanded set = true ↔ setEra set ≠ .preBW := by
  cases set <;> simp [legalSetInExpanded, setEra]

theorem legalSetInExpanded_of_bw_plus (set : TCGSet)
    (h : setEra set ≠ .preBW) :
    legalSetInExpanded set = true := by
  exact (legalSetInExpanded_iff_bw_plus set).2 h

-- ============================================================================
-- FORMAT RULE DIFFERENCES
-- ============================================================================

def firstPlayerCanAttackTurnOne : TCGFormat → Bool
  | .standard => false
  | .expanded => false
  | .unlimited => true

def gxAllowed : TCGFormat → Bool
  | .standard => false
  | .expanded => true
  | .unlimited => true

def vstarAllowed : TCGFormat → Bool
  | .standard => false
  | .expanded => true
  | .unlimited => true

def turnOneAttackAllowed (format : TCGFormat) (isStartingPlayer : Bool) : Bool :=
  if isStartingPlayer then firstPlayerCanAttackTurnOne format else true

@[simp] theorem firstPlayerCanAttackTurnOne_standard :
    firstPlayerCanAttackTurnOne .standard = false := rfl
@[simp] theorem firstPlayerCanAttackTurnOne_expanded :
    firstPlayerCanAttackTurnOne .expanded = false := rfl
@[simp] theorem firstPlayerCanAttackTurnOne_unlimited :
    firstPlayerCanAttackTurnOne .unlimited = true := rfl

@[simp] theorem gxAllowed_standard : gxAllowed .standard = false := rfl
@[simp] theorem gxAllowed_expanded : gxAllowed .expanded = true := rfl
@[simp] theorem gxAllowed_unlimited : gxAllowed .unlimited = true := rfl

@[simp] theorem vstarAllowed_standard : vstarAllowed .standard = false := rfl
@[simp] theorem vstarAllowed_expanded : vstarAllowed .expanded = true := rfl
@[simp] theorem vstarAllowed_unlimited : vstarAllowed .unlimited = true := rfl

@[simp] theorem turnOneAttackAllowed_second_player (format : TCGFormat) :
    turnOneAttackAllowed format false = true := by
  simp [turnOneAttackAllowed]

@[simp] theorem turnOneAttackAllowed_starting_player (format : TCGFormat) :
    turnOneAttackAllowed format true = firstPlayerCanAttackTurnOne format := by
  simp [turnOneAttackAllowed]


-- ============================================================================
-- BAN LISTS
-- ============================================================================

def bannedCardNames : TCGFormat → List String
  | .standard => []
  | .expanded => ["Lysandre's Trump Card", "Forest of Giant Plants", "Chip-Chip Ice Axe"]
  | .unlimited => []

def isBanned (format : TCGFormat) (name : String) : Bool :=
  (bannedCardNames format).contains name

@[simp] theorem bannedCardNames_standard :
    bannedCardNames .standard = [] := rfl
@[simp] theorem bannedCardNames_expanded :
    bannedCardNames .expanded =
      ["Lysandre's Trump Card", "Forest of Giant Plants", "Chip-Chip Ice Axe"] := rfl
@[simp] theorem bannedCardNames_unlimited :
    bannedCardNames .unlimited = [] := rfl

@[simp] theorem isBanned_standard_any (name : String) :
    isBanned .standard name = false := by
  simp [isBanned, bannedCardNames]

theorem isBanned_expanded_lysandre :
    isBanned .expanded "Lysandre's Trump Card" = true := by
  simp [isBanned, bannedCardNames]

theorem isBanned_expanded_forest :
    isBanned .expanded "Forest of Giant Plants" = true := by
  simp [isBanned, bannedCardNames]

theorem isBanned_expanded_pikachu :
    isBanned .expanded "Pikachu" = false := by
  decide

@[simp] theorem isBanned_unlimited_any (name : String) :
    isBanned .unlimited name = false := by
  simp [isBanned, bannedCardNames]

-- ============================================================================
-- CARD LEGALITY
-- ============================================================================

structure FormatCard where
  card : Card
  set : TCGSet
  isGX : Bool := false
  isVSTAR : Bool := false
  deriving Repr, BEq, DecidableEq

def cardName (card : FormatCard) : String :=
  card.card.name

def passesSetRule (format : TCGFormat) (card : FormatCard) : Bool :=
  legalSetInFormat format card.set

def passesBanRule (format : TCGFormat) (card : FormatCard) : Bool :=
  !(isBanned format (cardName card))

def passesGXRule (format : TCGFormat) (card : FormatCard) : Bool :=
  if card.isGX then gxAllowed format else true

def passesVSTARRule (format : TCGFormat) (card : FormatCard) : Bool :=
  if card.isVSTAR then vstarAllowed format else true

def cardLegalInFormat (format : TCGFormat) (card : FormatCard) : Bool :=
  passesSetRule format card &&
    passesBanRule format card &&
    passesGXRule format card &&
    passesVSTARRule format card

@[simp] theorem passesSetRule_unlimited (card : FormatCard) :
    passesSetRule .unlimited card = true := by
  simp [passesSetRule, legalSetInFormat, legalSetInUnlimited]

theorem passesBanRule_iff_not_banned (format : TCGFormat) (card : FormatCard) :
    passesBanRule format card = true ↔ isBanned format (cardName card) = false := by
  simp [passesBanRule]

theorem passesGXRule_non_gx (format : TCGFormat) (card : FormatCard)
    (h : card.isGX = false) :
    passesGXRule format card = true := by
  simp [passesGXRule, h]

theorem passesVSTARRule_non_vstar (format : TCGFormat) (card : FormatCard)
    (h : card.isVSTAR = false) :
    passesVSTARRule format card = true := by
  simp [passesVSTARRule, h]

theorem passesGXRule_standard_gx (card : FormatCard)
    (h : card.isGX = true) :
    passesGXRule .standard card = false := by
  simp [passesGXRule, h, gxAllowed]

theorem passesVSTARRule_standard_vstar (card : FormatCard)
    (h : card.isVSTAR = true) :
    passesVSTARRule .standard card = false := by
  simp [passesVSTARRule, h, vstarAllowed]

theorem cardLegalInFormat_iff (format : TCGFormat) (card : FormatCard) :
    cardLegalInFormat format card = true ↔
      passesSetRule format card = true ∧
      passesBanRule format card = true ∧
      passesGXRule format card = true ∧
      passesVSTARRule format card = true := by
  simp [cardLegalInFormat, Bool.and_eq_true, and_assoc]

theorem cardLegalInFormat_false_of_banned (format : TCGFormat) (card : FormatCard)
    (h : isBanned format (cardName card) = true) :
    cardLegalInFormat format card = false := by
  simp [cardLegalInFormat, passesBanRule, h]

theorem cardLegalInFormat_false_of_illegal_set (format : TCGFormat) (card : FormatCard)
    (h : legalSetInFormat format card.set = false) :
    cardLegalInFormat format card = false := by
  simp [cardLegalInFormat, passesSetRule, h]

theorem cardLegalInFormat_true_of_rules (format : TCGFormat) (card : FormatCard)
    (hSet : passesSetRule format card = true)
    (hBan : passesBanRule format card = true)
    (hGX : passesGXRule format card = true)
    (hVSTAR : passesVSTARRule format card = true) :
    cardLegalInFormat format card = true := by
  simp [cardLegalInFormat, hSet, hBan, hGX, hVSTAR]

theorem cardLegalInUnlimited_iff (card : FormatCard) :
    cardLegalInFormat .unlimited card = true ↔
      passesBanRule .unlimited card = true ∧
      passesGXRule .unlimited card = true ∧
      passesVSTARRule .unlimited card = true := by
  simp [cardLegalInFormat, passesSetRule_unlimited, Bool.and_eq_true, and_assoc]

theorem cardLegalInExpanded_gx_card_iff (card : FormatCard)
    (hGXCard : card.isGX = true) :
    passesGXRule .expanded card = true := by
  simp [passesGXRule, hGXCard, gxAllowed]

theorem cardLegalInExpanded_vstar_card_iff (card : FormatCard)
    (hVSTARCard : card.isVSTAR = true) :
    passesVSTARRule .expanded card = true := by
  simp [passesVSTARRule, hVSTARCard, vstarAllowed]

-- ============================================================================
-- STANDARD ROTATION
-- ============================================================================

def rotateStandard (oldStandard newStandard : List TCGSet) : List TCGSet :=
  oldStandard.filter (fun set => !(newStandard.contains set))

def standardSets2025 : List TCGSet :=
  [.scarletViolet, .paldeaEvolved, .obsidianFlames, .paradoxRift, .temporalForces, .twilightMasquerade]

def standardSets2026 : List TCGSet :=
  [.obsidianFlames, .paradoxRift, .temporalForces, .twilightMasquerade, .stellarCrown]

def setsLeavingStandardIn2026 : List TCGSet :=
  rotateStandard standardSets2025 standardSets2026

@[simp] theorem rotateStandard_nil_left (newStandard : List TCGSet) :
    rotateStandard [] newStandard = [] := by
  simp [rotateStandard]

@[simp] theorem rotateStandard_nil_right (oldStandard : List TCGSet) :
    rotateStandard oldStandard [] = oldStandard := by
  simp [rotateStandard]

theorem setsLeavingStandardIn2026_value :
    setsLeavingStandardIn2026 = [.scarletViolet, .paldeaEvolved] := by
  decide

theorem scarletViolet_leaves_in_2026 :
    .scarletViolet ∈ setsLeavingStandardIn2026 := by
  simp [setsLeavingStandardIn2026_value]

theorem paldeaEvolved_leaves_in_2026 :
    .paldeaEvolved ∈ setsLeavingStandardIn2026 := by
  simp [setsLeavingStandardIn2026_value]

theorem paradoxRift_does_not_leave_in_2026 :
    .paradoxRift ∉ setsLeavingStandardIn2026 := by
  simp [setsLeavingStandardIn2026_value]

-- ============================================================================
-- SAMPLE LEGALITY CHECKS
-- ============================================================================

def sampleAttack : Attack :=
  { name := "Sample", baseDamage := 10, effects := [] }

def sampleSVCard : FormatCard :=
  { card :=
      { name := "Sample SV",
        hp := 120,
        energyType := .fire,
        attacks := [sampleAttack] },
    set := .obsidianFlames }

def sampleGXCard : FormatCard :=
  { card :=
      { name := "Sample GX",
        hp := 190,
        energyType := .psychic,
        attacks := [sampleAttack] },
    set := .sunMoonBase,
    isGX := true }

def sampleVSTARCard : FormatCard :=
  { card :=
      { name := "Sample VSTAR",
        hp := 280,
        energyType := .colorless,
        attacks := [sampleAttack] },
    set := .brilliantStars,
    isVSTAR := true }

theorem sampleSVCard_standard_legal :
    cardLegalInFormat .standard sampleSVCard = true := by
  decide

theorem sampleGXCard_standard_illegal :
    cardLegalInFormat .standard sampleGXCard = false := by
  decide

theorem sampleGXCard_expanded_legal :
    cardLegalInFormat .expanded sampleGXCard = true := by
  decide

theorem sampleVSTARCard_standard_illegal :
    cardLegalInFormat .standard sampleVSTARCard = false := by
  decide

theorem sampleVSTARCard_expanded_legal :
    cardLegalInFormat .expanded sampleVSTARCard = true := by
  decide

theorem sampleVSTARCard_unlimited_legal :
    cardLegalInFormat .unlimited sampleVSTARCard = true := by
  decide

end PokemonLean.Format
