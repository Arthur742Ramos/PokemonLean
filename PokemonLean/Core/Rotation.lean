/-
  PokemonLean / Core / Rotation.lean

  Set rotation and format legality system for the Pokémon TCG.
  =============================================================

  Models:
    - Regulation marks A through H (printed on cards since Sword & Shield)
    - Standard format: only recent regulation marks legal (e.g., E–H for 2024)
    - Expanded format: Black & White onward (BW through current)
    - Unlimited format: every card ever printed
    - Ban list: specific cards banned from formats
    - Annual rotation: oldest marks rotate out of Standard
    - Format hierarchy: Standard ⊂ Expanded ⊂ Unlimited

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  40+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.Rotation

-- ============================================================
-- §1  Regulation Marks
-- ============================================================

/-- Regulation marks printed on modern Pokémon TCG cards (Sword & Shield era onward).
    Pre-mark cards are grouped by era. -/
inductive RegulationMark where
  | preModern   -- cards before Black & White (Base Set through HGSS)
  | bwXy        -- Black & White and XY era cards
  | sunMoon     -- Sun & Moon era cards
  | A | B | C | D | E | F | G | H
deriving DecidableEq, Repr, BEq, Inhabited

/-- Chronological ordering for regulation marks. -/
def RegulationMark.toNat : RegulationMark → Nat
  | .preModern => 0
  | .bwXy      => 1
  | .sunMoon   => 2
  | .A         => 3
  | .B         => 4
  | .C         => 5
  | .D         => 6
  | .E         => 7
  | .F         => 8
  | .G         => 9
  | .H         => 10

def RegulationMark.le (a b : RegulationMark) : Bool := a.toNat ≤ b.toNat
def RegulationMark.lt (a b : RegulationMark) : Bool := a.toNat < b.toNat
def RegulationMark.ge (a b : RegulationMark) : Bool := a.toNat ≥ b.toNat

theorem regMark_toNat_injective (a b : RegulationMark)
    (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp [RegulationMark.toNat] at h <;> rfl

-- ============================================================
-- §2  Formats
-- ============================================================

/-- TCG competitive play formats. -/
inductive Format where
  | standard
  | expanded
  | unlimited
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §3  Card Representation
-- ============================================================

/-- A card entry for format legality checking. -/
structure RotationCard where
  name           : String
  setCode        : String
  regMark        : RegulationMark
  bannedFormats  : List Format   -- formats in which this card is explicitly banned
deriving Repr, Inhabited

-- ============================================================
-- §4  Rotation Configuration
-- ============================================================

/-- A rotation configuration specifies the oldest legal regulation mark
    for Standard, and the oldest for Expanded. -/
structure RotationConfig where
  standardOldest  : RegulationMark   -- oldest mark legal in Standard
  expandedOldest  : RegulationMark   -- oldest mark legal in Expanded
  newestMark      : RegulationMark   -- the most recently released mark
deriving Repr, Inhabited

/-- The 2024 season rotation: Standard is E–H, Expanded is bwXy onward. -/
def season2024 : RotationConfig :=
  { standardOldest := .E
    expandedOldest := .bwXy
    newestMark     := .H }

/-- The 2023 season rotation: Standard is D–G, Expanded is bwXy onward. -/
def season2023 : RotationConfig :=
  { standardOldest := .D
    expandedOldest := .bwXy
    newestMark     := .G }

-- ============================================================
-- §5  Legality Predicates
-- ============================================================

/-- Is a regulation mark within the range [oldest, newest]? -/
def markInRange (oldest newest mark : RegulationMark) : Bool :=
  oldest.toNat ≤ mark.toNat && mark.toNat ≤ newest.toNat

/-- Is a card banned in a given format? -/
def isBannedIn (card : RotationCard) (fmt : Format) : Bool :=
  card.bannedFormats.contains fmt

/-- Standard-legal: mark in [standardOldest, newest] and not banned. -/
def isStandardLegal (cfg : RotationConfig) (card : RotationCard) : Bool :=
  markInRange cfg.standardOldest cfg.newestMark card.regMark && !isBannedIn card .standard

/-- Expanded-legal: mark in [expandedOldest, newest] and not banned. -/
def isExpandedLegal (cfg : RotationConfig) (card : RotationCard) : Bool :=
  markInRange cfg.expandedOldest cfg.newestMark card.regMark && !isBannedIn card .expanded

/-- Unlimited-legal: every card is legal unless banned in unlimited. -/
def isUnlimitedLegal (card : RotationCard) : Bool :=
  !isBannedIn card .unlimited

/-- Master legality checker. -/
def isLegalIn (cfg : RotationConfig) (card : RotationCard) (fmt : Format) : Bool :=
  match fmt with
  | .standard  => isStandardLegal cfg card
  | .expanded  => isExpandedLegal cfg card
  | .unlimited => isUnlimitedLegal card

-- ============================================================
-- §6  Rotation Operations
-- ============================================================

/-- Rotate Standard by advancing the oldest legal mark by 1 step. -/
def advanceMark (m : RegulationMark) : RegulationMark :=
  match m with
  | .preModern => .bwXy
  | .bwXy      => .sunMoon
  | .sunMoon   => .A
  | .A         => .B
  | .B         => .C
  | .C         => .D
  | .D         => .E
  | .E         => .F
  | .F         => .G
  | .G         => .H
  | .H         => .H   -- cannot advance past newest known mark

/-- Perform annual rotation: advance standardOldest, add new mark. -/
def rotateStandard (cfg : RotationConfig) (newMark : RegulationMark) : RotationConfig :=
  { cfg with
    standardOldest := advanceMark cfg.standardOldest
    newestMark     := newMark }

-- ============================================================
-- §7  Example Cards
-- ============================================================

def charizardExSV : RotationCard :=
  { name := "Charizard ex", setCode := "SVI", regMark := .G, bannedFormats := [] }

def lysandresTrumpCard : RotationCard :=
  { name := "Lysandre's Trump Card", setCode := "PHF", regMark := .bwXy,
    bannedFormats := [.standard, .expanded] }

def shayminsEX : RotationCard :=
  { name := "Shaymin-EX", setCode := "ROS", regMark := .bwXy, bannedFormats := [] }

def arceusDPT : RotationCard :=
  { name := "Arceus", setCode := "AR", regMark := .preModern, bannedFormats := [] }

def lugiaStar : RotationCard :=
  { name := "Lugia VSTAR", setCode := "SIT", regMark := .F, bannedFormats := [] }

def forestSealStone : RotationCard :=
  { name := "Forest Seal Stone", setCode := "SIT", regMark := .F, bannedFormats := [] }

def markE_card : RotationCard :=
  { name := "Mew VMAX", setCode := "FST", regMark := .E, bannedFormats := [] }

def markD_card : RotationCard :=
  { name := "Crobat V", setCode := "DAA", regMark := .D, bannedFormats := [] }

-- ============================================================
-- §8  Theorems — Format Hierarchy
-- ============================================================

/-- advanceMark always produces a mark ≥ input. -/
theorem advanceMark_ge (m : RegulationMark) : m.toNat ≤ (advanceMark m).toNat := by
  cases m <;> simp [advanceMark, RegulationMark.toNat]

/-- If expandedOldest ≤ standardOldest, then Standard ⊂ Expanded:
    any card legal in Standard is also in Expanded's mark range. -/
theorem standard_subset_expanded_marks
    (cfg : RotationConfig)
    (card : RotationCard)
    (horder : cfg.expandedOldest.toNat ≤ cfg.standardOldest.toNat)
    (hstd : markInRange cfg.standardOldest cfg.newestMark card.regMark = true) :
    markInRange cfg.expandedOldest cfg.newestMark card.regMark = true := by
  simp [markInRange] at *
  omega

/-- Unlimited accepts every card (when not banned). -/
theorem unlimited_accepts_all (card : RotationCard)
    (h : card.bannedFormats = []) : isUnlimitedLegal card = true := by
  unfold isUnlimitedLegal isBannedIn
  rw [h]
  rfl

/-- Standard legal → Expanded legal, given proper config and no expanded ban. -/
theorem standard_implies_expanded
    (cfg : RotationConfig)
    (card : RotationCard)
    (horder : cfg.expandedOldest.toNat ≤ cfg.standardOldest.toNat)
    (hstd : isStandardLegal cfg card = true)
    (hnotBannedExp : isBannedIn card .expanded = false) :
    isExpandedLegal cfg card = true := by
  unfold isStandardLegal at hstd
  unfold isExpandedLegal
  have hstdAnd := Bool.and_eq_true_iff.mp hstd
  have hrange := hstdAnd.1
  unfold markInRange at hrange ⊢
  rw [Bool.and_eq_true_iff]
  constructor
  · rw [Bool.and_eq_true_iff] at hrange ⊢
    constructor
    · simp only [decide_eq_true_eq] at hrange ⊢; omega
    · exact hrange.2
  · simp [hnotBannedExp]

/-- Expanded legal → Unlimited legal, given no unlimited ban. -/
theorem expanded_implies_unlimited
    (cfg : RotationConfig)
    (card : RotationCard)
    (hexp : isExpandedLegal cfg card = true)
    (hnotBannedUnl : isBannedIn card .unlimited = false) :
    isUnlimitedLegal card = true := by
  unfold isUnlimitedLegal
  simp [hnotBannedUnl]

-- ============================================================
-- §9  Theorems — Banned Cards
-- ============================================================

/-- A card banned in Standard cannot be Standard-legal. -/
theorem banned_not_standard (cfg : RotationConfig) (card : RotationCard)
    (h : isBannedIn card .standard = true) :
    isStandardLegal cfg card = false := by
  unfold isStandardLegal
  simp [h]

/-- A card banned in Expanded cannot be Expanded-legal. -/
theorem banned_not_expanded (cfg : RotationConfig) (card : RotationCard)
    (h : isBannedIn card .expanded = true) :
    isExpandedLegal cfg card = false := by
  unfold isExpandedLegal
  simp [h]

/-- A card banned in Unlimited cannot be Unlimited-legal. -/
theorem banned_not_unlimited (card : RotationCard)
    (h : isBannedIn card .unlimited = true) :
    isUnlimitedLegal card = false := by
  unfold isUnlimitedLegal
  simp [h]

/-- Lysandre's Trump Card is banned in both Standard and Expanded. -/
theorem lysandres_banned_standard :
    isStandardLegal season2024 lysandresTrumpCard = false := by native_decide

theorem lysandres_banned_expanded :
    isExpandedLegal season2024 lysandresTrumpCard = false := by native_decide

-- ============================================================
-- §10  Theorems — Regulation Mark Determines Legality
-- ============================================================

/-- A card whose mark is below Standard's oldest is not Standard-legal. -/
theorem old_mark_not_standard (cfg : RotationConfig) (card : RotationCard)
    (h : card.regMark.toNat < cfg.standardOldest.toNat) :
    isStandardLegal cfg card = false := by
  simp only [isStandardLegal, markInRange]
  have : ¬ (cfg.standardOldest.toNat ≤ card.regMark.toNat) := by omega
  simp [this]

/-- A card whose mark is above the newest is not Standard-legal. -/
theorem future_mark_not_standard (cfg : RotationConfig) (card : RotationCard)
    (h : cfg.newestMark.toNat < card.regMark.toNat) :
    isStandardLegal cfg card = false := by
  simp only [isStandardLegal, markInRange]
  have : ¬ (card.regMark.toNat ≤ cfg.newestMark.toNat) := by omega
  simp [this]

/-- Mark in range and not banned ↔ Standard legal. -/
theorem standard_legal_iff (cfg : RotationConfig) (card : RotationCard) :
    isStandardLegal cfg card = true ↔
    (markInRange cfg.standardOldest cfg.newestMark card.regMark = true ∧
     isBannedIn card .standard = false) := by
  unfold isStandardLegal
  constructor
  · intro h
    have hab := Bool.and_eq_true_iff.mp h
    constructor
    · exact hab.1
    · cases hb : isBannedIn card Format.standard
      · rfl
      · simp [hb] at hab
  · intro ⟨h1, h2⟩
    rw [Bool.and_eq_true_iff]
    exact ⟨h1, by simp [h2]⟩

-- ============================================================
-- §11  Theorems — Rotation Operations
-- ============================================================

/-- After rotation, the new standardOldest is advanced. -/
theorem rotate_advances_oldest (cfg : RotationConfig) (nm : RegulationMark) :
    (rotateStandard cfg nm).standardOldest = advanceMark cfg.standardOldest := by
  simp [rotateStandard]

/-- After rotation, the newest mark is updated. -/
theorem rotate_updates_newest (cfg : RotationConfig) (nm : RegulationMark) :
    (rotateStandard cfg nm).newestMark = nm := by
  simp [rotateStandard]

/-- Rotation preserves the expanded oldest. -/
theorem rotate_preserves_expanded (cfg : RotationConfig) (nm : RegulationMark) :
    (rotateStandard cfg nm).expandedOldest = cfg.expandedOldest := by
  simp [rotateStandard]

/-- After rotation, a card with the old standardOldest mark is no longer Standard
    (assuming the advanced mark is strictly greater). -/
theorem rotation_removes_oldest_mark (cfg : RotationConfig) (card : RotationCard) (nm : RegulationMark)
    (hmark : card.regMark = cfg.standardOldest)
    (hadv : cfg.standardOldest.toNat < (advanceMark cfg.standardOldest).toNat)
    (hnm : nm.toNat ≥ (advanceMark cfg.standardOldest).toNat) :
    isStandardLegal (rotateStandard cfg nm) card = false := by
  have h1 : card.regMark.toNat < (rotateStandard cfg nm).standardOldest.toNat := by
    simp [rotateStandard]
    rw [hmark]
    exact hadv
  exact old_mark_not_standard (rotateStandard cfg nm) card h1

/-- Rotation preserves format hierarchy: expandedOldest still ≤ new standardOldest
    when the original hierarchy held and advanceMark advances. -/
theorem rotation_preserves_hierarchy (cfg : RotationConfig) (nm : RegulationMark)
    (horder : cfg.expandedOldest.toNat ≤ cfg.standardOldest.toNat) :
    (rotateStandard cfg nm).expandedOldest.toNat ≤
    (rotateStandard cfg nm).standardOldest.toNat := by
  simp [rotateStandard]
  have := advanceMark_ge cfg.standardOldest
  omega

-- ============================================================
-- §12  Concrete Scenario Proofs
-- ============================================================

/-- Charizard ex (mark G) is Standard-legal in 2024. -/
theorem charizard_standard_2024 :
    isStandardLegal season2024 charizardExSV = true := by native_decide

/-- Charizard ex is Expanded-legal in 2024. -/
theorem charizard_expanded_2024 :
    isExpandedLegal season2024 charizardExSV = true := by native_decide

/-- Charizard ex is Unlimited-legal. -/
theorem charizard_unlimited :
    isUnlimitedLegal charizardExSV = true := by native_decide

/-- Shaymin-EX (bwXy) is not Standard in 2024. -/
theorem shaymin_not_standard_2024 :
    isStandardLegal season2024 shayminsEX = false := by native_decide

/-- Shaymin-EX is Expanded-legal in 2024. -/
theorem shaymin_expanded_2024 :
    isExpandedLegal season2024 shayminsEX = true := by native_decide

/-- Arceus (preModern) is not Expanded-legal. -/
theorem arceus_not_expanded :
    isExpandedLegal season2024 arceusDPT = false := by native_decide

/-- Arceus is Unlimited-legal. -/
theorem arceus_unlimited :
    isUnlimitedLegal arceusDPT = true := by native_decide

/-- Mew VMAX (mark E) was Standard-legal in 2024. -/
theorem mew_vmax_standard_2024 :
    isStandardLegal season2024 markE_card = true := by native_decide

/-- Crobat V (mark D) is not Standard-legal in 2024 (rotated out). -/
theorem crobat_not_standard_2024 :
    isStandardLegal season2024 markD_card = false := by native_decide

/-- Crobat V (mark D) was Standard-legal in 2023. -/
theorem crobat_standard_2023 :
    isStandardLegal season2023 markD_card = true := by native_decide

-- ============================================================
-- §13  New Set Addition
-- ============================================================

/-- Adding a new set card with a mark in range keeps it legal. -/
theorem new_set_standard_legal (cfg : RotationConfig) (card : RotationCard)
    (hge : cfg.standardOldest.toNat ≤ card.regMark.toNat)
    (hle : card.regMark.toNat ≤ cfg.newestMark.toNat)
    (hnotBanned : isBannedIn card .standard = false) :
    isStandardLegal cfg card = true := by
  simp only [isStandardLegal, markInRange]
  simp [hge, hle, hnotBanned]

theorem new_set_expanded_legal (cfg : RotationConfig) (card : RotationCard)
    (hge : cfg.expandedOldest.toNat ≤ card.regMark.toNat)
    (hle : card.regMark.toNat ≤ cfg.newestMark.toNat)
    (hnotBanned : isBannedIn card .expanded = false) :
    isExpandedLegal cfg card = true := by
  simp only [isExpandedLegal, markInRange]
  simp [hge, hle, hnotBanned]

theorem new_set_unlimited_legal (card : RotationCard)
    (hnotBanned : isBannedIn card .unlimited = false) :
    isUnlimitedLegal card = true := by
  unfold isUnlimitedLegal
  simp [hnotBanned]

-- ============================================================
-- §14  Mark Ordering Theorems
-- ============================================================

theorem mark_le_refl (m : RegulationMark) : m.le m = true := by
  simp [RegulationMark.le]

theorem mark_le_trans (a b c : RegulationMark)
    (h1 : a.le b = true) (h2 : b.le c = true) : a.le c = true := by
  simp [RegulationMark.le] at *
  omega

theorem mark_lt_irrefl (m : RegulationMark) : m.lt m = false := by
  simp [RegulationMark.lt]

theorem mark_A_lt_H : RegulationMark.A.lt .H = true := by native_decide

theorem mark_E_le_H : RegulationMark.E.le .H = true := by native_decide

-- ============================================================
-- §15  Ban List Set Operations
-- ============================================================

/-- Filtering a card pool by a format yields only legal cards. -/
def filterLegal (cfg : RotationConfig) (fmt : Format) (cards : List RotationCard) : List RotationCard :=
  cards.filter (fun c => isLegalIn cfg c fmt)

/-- Every card in the filtered list is legal. -/
theorem filterLegal_all_legal (cfg : RotationConfig) (fmt : Format) (cards : List RotationCard)
    (card : RotationCard)
    (h : card ∈ filterLegal cfg fmt cards) :
    isLegalIn cfg card fmt = true := by
  simp [filterLegal, List.mem_filter] at h
  exact h.2

/-- The filtered Standard list is a subset of the filtered Expanded list,
    when the config has the standard hierarchy and cards aren't banned in Expanded. -/
theorem standard_filter_subset_expanded
    (cfg : RotationConfig) (cards : List RotationCard)
    (horder : cfg.expandedOldest.toNat ≤ cfg.standardOldest.toNat)
    (hnoExpBan : ∀ c ∈ cards, isBannedIn c .expanded = false) :
    ∀ c ∈ filterLegal cfg .standard cards, c ∈ filterLegal cfg .expanded cards := by
  intro c hc
  simp [filterLegal, List.mem_filter] at hc ⊢
  constructor
  · exact hc.1
  · simp [isLegalIn] at hc ⊢
    exact standard_implies_expanded cfg c horder hc.2 (hnoExpBan c hc.1)

-- ============================================================
-- §16  Additional Properties
-- ============================================================

/-- isLegalIn dispatches correctly for standard. -/
theorem isLegalIn_standard (cfg : RotationConfig) (card : RotationCard) :
    isLegalIn cfg card .standard = isStandardLegal cfg card := by
  simp [isLegalIn]

/-- isLegalIn dispatches correctly for expanded. -/
theorem isLegalIn_expanded (cfg : RotationConfig) (card : RotationCard) :
    isLegalIn cfg card .expanded = isExpandedLegal cfg card := by
  simp [isLegalIn]

/-- isLegalIn dispatches correctly for unlimited. -/
theorem isLegalIn_unlimited (cfg : RotationConfig) (card : RotationCard) :
    isLegalIn cfg card .unlimited = isUnlimitedLegal card := by
  simp [isLegalIn]

/-- Two cards with the same reg mark have the same mark range check. -/
theorem same_mark_same_range (c1 c2 : RotationCard) (oldest newest : RegulationMark)
    (h : c1.regMark = c2.regMark) :
    markInRange oldest newest c1.regMark = markInRange oldest newest c2.regMark := by
  simp [markInRange, h]

/-- Forest Seal Stone (mark F) is Standard-legal in 2024. -/
theorem forest_seal_stone_standard :
    isStandardLegal season2024 forestSealStone = true := by native_decide

/-- Lugia VSTAR (mark F) is Standard-legal in 2024. -/
theorem lugia_vstar_standard :
    isStandardLegal season2024 lugiaStar = true := by native_decide

/-- A card not banned anywhere is Unlimited-legal. -/
theorem unbanned_always_unlimited (card : RotationCard)
    (h : card.bannedFormats = []) : isUnlimitedLegal card = true := by
  unfold isUnlimitedLegal isBannedIn
  rw [h]
  rfl

/-- advanceMark is idempotent on the maximum mark H. -/
theorem advanceMark_H : advanceMark .H = .H := by rfl

/-- advanceMark D = E. -/
theorem advanceMark_D : advanceMark .D = .E := by rfl

/-- advanceMark E = F. -/
theorem advanceMark_E : advanceMark .E = .F := by rfl

end PokemonLean.Core.Rotation
