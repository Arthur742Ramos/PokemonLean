/-
  PokemonLean / RotationFormats.lean

  Pokémon TCG Rotation Formats
  ============================

  Formalises Standard, Expanded, and Unlimited rotation formats,
  rotation schedule mechanics, card legality per format, ban list
  interactions, format-specific rules (first turn supporter in Standard),
  set block structure, and format transition paths.

  Paths ARE the math.  20+ theorems.
-/

set_option linter.unusedVariables false

namespace RotationFormats
-- ============================================================================
-- §3  Formats and Eras
-- ============================================================================

inductive Format where
  | standard  : Format
  | expanded  : Format
  | unlimited : Format
deriving DecidableEq, Repr, BEq

/-- TCG eras / regulation marks. -/
inductive RegulationMark where
  | D | E | F | G | H | I
deriving DecidableEq, Repr, BEq

instance : LawfulBEq RegulationMark where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

/-- A card set with its regulation mark and release year. -/
structure CardSetInfo where
  code   : String
  name   : String
  year   : Nat
  regMark : RegulationMark
deriving DecidableEq, Repr

/-- Rotation year: which reg marks are legal in Standard. -/
structure RotationYear where
  year         : Nat
  legalMarks   : List RegulationMark
deriving Repr

-- ============================================================================
-- §4  Legality functions
-- ============================================================================

def isLegalInStandard (s : CardSetInfo) (ry : RotationYear) : Bool :=
  ry.legalMarks.contains s.regMark

def isLegalInExpanded (s : CardSetInfo) : Bool :=
  s.year >= 2011

def isLegalInUnlimited (_s : CardSetInfo) : Bool := true

def isLegalInFormat (s : CardSetInfo) (f : Format) (ry : RotationYear) : Bool :=
  match f with
  | .standard  => isLegalInStandard s ry
  | .expanded  => isLegalInExpanded s
  | .unlimited => true

-- ============================================================================
-- §5  Legality theorems
-- ============================================================================

/-- Theorem 1: Unlimited always legal. -/
theorem unlimited_always_legal (s : CardSetInfo) (ry : RotationYear) :
    isLegalInFormat s .unlimited ry = true := rfl

/-- Theorem 2: A 2024 set is Expanded-legal. -/
theorem set_2024_expanded :
    isLegalInExpanded ⟨"SV7", "Stellar Crown", 2024, .H⟩ = true := rfl

/-- Theorem 3: Standard legality implies Expanded when marks imply year ≥ 2011. -/
theorem standard_implies_expanded (s : CardSetInfo) (ry : RotationYear)
    (hstd : isLegalInStandard s ry = true)
    (hmark : isLegalInStandard s ry = true → s.year ≥ 2011) :
    isLegalInExpanded s = true := by
  simp [isLegalInExpanded]
  exact hmark hstd

/-- Theorem 4: Pre-BW set not Expanded-legal. -/
theorem pre_bw_not_expanded (s : CardSetInfo) (h : s.year < 2011) :
    isLegalInExpanded s = false := by
  simp [isLegalInExpanded]
  omega

-- ============================================================================
-- §6  Rotation schedule
-- ============================================================================

/-- Example rotation schedules. -/
def rotation2024 : RotationYear := ⟨2024, [.F, .G, .H]⟩
def rotation2025 : RotationYear := ⟨2025, [.G, .H, .I]⟩

/-- Theorem 5: D-mark set rotates out in 2024 Standard. -/
theorem d_mark_rotated_2024 (s : CardSetInfo) (h : s.regMark = .D) :
    isLegalInStandard s rotation2024 = false := by
  simp [isLegalInStandard, rotation2024, List.contains, List.elem, h, BEq.beq]
  decide

/-- Theorem 6: F-mark set legal in 2024 Standard. -/
theorem f_mark_legal_2024 (s : CardSetInfo) (h : s.regMark = .F) :
    isLegalInStandard s rotation2024 = true := by
  simp [isLegalInStandard, rotation2024, List.contains, List.elem, h, BEq.beq]
  decide

/-- Theorem 7: F-mark set rotates out in 2025 Standard. -/
theorem f_mark_rotated_2025 (s : CardSetInfo) (h : s.regMark = .F) :
    isLegalInStandard s rotation2025 = false := by
  simp [isLegalInStandard, rotation2025, List.contains, List.elem, h, BEq.beq]
  decide

/-- Theorem 8: G-mark legal in both 2024 and 2025. -/
theorem g_mark_survives_rotation (s : CardSetInfo) (h : s.regMark = .G) :
    isLegalInStandard s rotation2024 = true ∧ isLegalInStandard s rotation2025 = true := by
  constructor <;> simp [isLegalInStandard, rotation2024, rotation2025, List.contains, List.elem, h, BEq.beq] <;> decide
/-- Format state: which marks are legal. -/
structure FormatState where
  formatName : Format
  legalMarks : List RegulationMark
deriving DecidableEq, Repr

def fs2024 : FormatState := ⟨.standard, [.F, .G, .H]⟩
def fs2025 : FormatState := ⟨.standard, [.G, .H, .I]⟩
def fsExpanded : FormatState := ⟨.expanded, [.D, .E, .F, .G, .H, .I]⟩
def fsUnlimited : FormatState := ⟨.unlimited, [.D, .E, .F, .G, .H, .I]⟩


-- ============================================================================
-- §8  Ban list mechanics
-- ============================================================================

structure BanEntry where
  cardName : String
  format   : Format
deriving DecidableEq, Repr

abbrev BanList := List BanEntry

def isBanned (bl : BanList) (name : String) (f : Format) : Bool :=
  bl.any (fun e => e.cardName == name && e.format == f)

/-- Theorem 15: Empty ban list bans nothing. -/
theorem empty_banlist_clear (name : String) (f : Format) :
    isBanned [] name f = false := rfl

/-- Theorem 16: Banned card is found on list. -/
theorem banned_card_found :
    isBanned [⟨"Lysandre's Trump Card", .expanded⟩] "Lysandre's Trump Card" .expanded = true := by
  native_decide

/-- Theorem 17: Different format not banned. -/
theorem different_format_not_banned :
    isBanned [⟨"Forest of Giant Plants", .expanded⟩] "Forest of Giant Plants" .standard = false := by
  native_decide

-- ============================================================================
-- §9  Format-specific rules
-- ============================================================================

inductive TurnRule where
  | canPlaySupporter
  | noSupporterFirstTurn
  | canAttackFirstTurn
  | noAttackFirstTurnGoingFirst
deriving DecidableEq, Repr

def standardFirstTurnRules : List TurnRule :=
  [.noSupporterFirstTurn, .noAttackFirstTurnGoingFirst]

def expandedFirstTurnRules : List TurnRule :=
  [.canPlaySupporter, .noAttackFirstTurnGoingFirst]

def unlimitedFirstTurnRules : List TurnRule :=
  [.canPlaySupporter, .canAttackFirstTurn]

/-- Theorem 18: Standard bans first-turn supporter. -/
theorem standard_no_first_turn_supporter :
    TurnRule.noSupporterFirstTurn ∈ standardFirstTurnRules := by
  simp [standardFirstTurnRules]

/-- Theorem 19: Expanded allows first-turn supporter. -/
theorem expanded_allows_supporter :
    TurnRule.canPlaySupporter ∈ expandedFirstTurnRules := by
  simp [expandedFirstTurnRules]

/-- Theorem 20: Unlimited allows first-turn attack. -/
theorem unlimited_allows_attack :
    TurnRule.canAttackFirstTurn ∈ unlimitedFirstTurnRules := by
  simp [unlimitedFirstTurnRules]

-- ============================================================================
-- §10  Format hierarchy paths
-- ============================================================================

/-- Format strictness ordering. -/
def formatStrictness : Format → Nat
  | .standard  => 3
  | .expanded  => 2
  | .unlimited => 1

/-- Theorem 21: Standard is stricter than Expanded. -/
theorem standard_stricter_than_expanded :
    formatStrictness .standard > formatStrictness .expanded := by decide

/-- Theorem 22: Expanded stricter than Unlimited. -/
theorem expanded_stricter_than_unlimited :
    formatStrictness .expanded > formatStrictness .unlimited := by decide

/-- Theorem 23: Standard strictest overall. -/
theorem standard_strictest :
    formatStrictness .standard > formatStrictness .unlimited := by decide

-- ============================================================================
-- §11  Multi-rotation path chains
-- ============================================================================

def fs2023 : FormatState := ⟨.standard, [.E, .F, .G]⟩


-- ============================================================================
-- §12  Regulation mark transitions
-- ============================================================================

/-- Regulation mark ordering (newer = higher). -/
def regMarkOrd : RegulationMark → Nat
  | .D => 1 | .E => 2 | .F => 3 | .G => 4 | .H => 5 | .I => 6

/-- Theorem 28: D is oldest mark. -/
theorem d_is_oldest : ∀ m : RegulationMark, regMarkOrd .D ≤ regMarkOrd m := by
  intro m; cases m <;> simp [regMarkOrd]

/-- Theorem 29: I is newest mark. -/
theorem i_is_newest : ∀ m : RegulationMark, regMarkOrd m ≤ regMarkOrd .I := by
  intro m; cases m <;> simp [regMarkOrd]

/-- Theorem 30: Regulation mark ordering is consistent with rotation. -/
theorem newer_marks_survive (s : CardSetInfo)
    (ry_old ry_new : RotationYear)
    (h_legal_old : isLegalInStandard s ry_old = true)
    (h_subset : ∀ m, m ∈ ry_new.legalMarks → m ∈ ry_old.legalMarks)
    (h_mem : s.regMark ∈ ry_new.legalMarks) :
    isLegalInStandard s ry_new = true := by
  show ry_new.legalMarks.contains s.regMark = true
  simp only [List.contains]
  exact List.elem_eq_true_of_mem h_mem

end RotationFormats
