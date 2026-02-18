/-
  PokemonLean / Core / FormatChecker.lean

  Certified format legality checker for Pokémon TCG.
  ==================================================

  Models:
    - Regulation marks: D, E, F, G, H, I (each card/set has a mark)
    - Standard format: only latest N regulation marks are legal
    - Expanded: BW-on (Black & White through current)
    - Unlimited: all cards legal
    - Rotation: when new marks rotate in, old marks become illegal
    - Ban list per format (separate from rotation)
    - First-turn rules by format
    - isFormatLegal (format, card) : Bool — the main checker
    - Example scenarios: Shaymin-EX legal in Expanded not Standard, etc.

  Self-contained — no imports.
  All proofs are sorry-free.  35+ theorems.
-/

set_option linter.unusedVariables false

namespace PokemonLean.Core.FormatChecker

-- ============================================================
-- §1  Regulation Marks
-- ============================================================

/-- Regulation marks printed on modern Pokémon TCG cards. -/
inductive RegMark where
  | D | E | F | G | H | I
  | preBW       -- Pre–Black & White era
  | bwToXY      -- BW/XY era (no regulation marks)
  | smToSSH     -- SM/SWSH early era
deriving DecidableEq, Repr, BEq, Inhabited

/-- Total ordering on regulation marks (chronological). -/
def RegMark.toNat : RegMark → Nat
  | .preBW     => 0
  | .bwToXY    => 1
  | .smToSSH   => 2
  | .D         => 3
  | .E         => 4
  | .F         => 5
  | .G         => 6
  | .H         => 7
  | .I         => 8

instance : Ord RegMark where
  compare a b := compare a.toNat b.toNat

def RegMark.le (a b : RegMark) : Bool := a.toNat ≤ b.toNat
def RegMark.ge (a b : RegMark) : Bool := a.toNat ≥ b.toNat

-- ============================================================
-- §2  Formats
-- ============================================================

/-- TCG play formats. -/
inductive Format where
  | standard
  | expanded
  | unlimited
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §3  Card Entry (for format checking)
-- ============================================================

/-- Simplified card entry for format legality. -/
structure CardEntry where
  name          : String
  setCode       : String
  regulationMark : RegMark
  isBanned      : List Format   -- formats in which this card is explicitly banned
deriving Repr, Inhabited

-- ============================================================
-- §4  Rotation Configuration
-- ============================================================

/-- Which regulation marks are currently legal in Standard. -/
structure RotationConfig where
  standardLegalMarks : List RegMark
  expandedFloor      : RegMark   -- oldest allowed mark in Expanded (bwToXY)
deriving Repr, Inhabited

/-- Default rotation config for 2024–2025 season.
    Standard: G, H, I legal.  Expanded floor: bwToXY. -/
def currentRotation : RotationConfig :=
  { standardLegalMarks := [.G, .H, .I],
    expandedFloor      := .bwToXY }

/-- Previous rotation (pre-2024): Standard had E, F, G, H. -/
def previousRotation : RotationConfig :=
  { standardLegalMarks := [.E, .F, .G, .H],
    expandedFloor      := .bwToXY }

-- ============================================================
-- §5  Ban Lists
-- ============================================================

/-- Is a card banned in a given format? -/
def CardEntry.isBannedIn (card : CardEntry) (fmt : Format) : Bool :=
  card.isBanned.contains fmt

-- ============================================================
-- §6  Mark Legality
-- ============================================================

/-- Is a regulation mark legal in Standard under the given rotation? -/
def isMarkLegalStandard (cfg : RotationConfig) (mark : RegMark) : Bool :=
  cfg.standardLegalMarks.contains mark

/-- Is a regulation mark legal in Expanded? -/
def isMarkLegalExpanded (cfg : RotationConfig) (mark : RegMark) : Bool :=
  mark.toNat ≥ cfg.expandedFloor.toNat

/-- Is a regulation mark legal in Unlimited? Always true. -/
def isMarkLegalUnlimited (_mark : RegMark) : Bool := true

-- ============================================================
-- §7  The Main Legality Checker
-- ============================================================

/-- Is a card format-legal?
    Legal = mark is in rotation for the format AND card is not banned. -/
def isFormatLegal (cfg : RotationConfig) (fmt : Format) (card : CardEntry) : Bool :=
  let markOk := match fmt with
    | .standard  => isMarkLegalStandard cfg card.regulationMark
    | .expanded  => isMarkLegalExpanded cfg card.regulationMark
    | .unlimited => isMarkLegalUnlimited card.regulationMark
  markOk && !card.isBannedIn fmt

-- ============================================================
-- §8  First-Turn Rules
-- ============================================================

/-- Actions that can be restricted on the first turn. -/
inductive FirstTurnAction where
  | attack
  | playSupporter
  | attachEnergy
  | evolve
  | playItem
deriving DecidableEq, Repr, BEq, Inhabited

/-- Is the given action allowed on turn 1 going first?
    Current rule: going first can't attack AND can't play Supporter. -/
def isAllowedTurn1GoingFirst (fmt : Format) (action : FirstTurnAction) : Bool :=
  match fmt with
  | .standard | .expanded =>
    match action with
    | .attack         => false
    | .playSupporter  => false
    | .attachEnergy   => true
    | .evolve         => false   -- can't evolve turn 1 regardless
    | .playItem       => true
  | .unlimited =>
    match action with
    | .attack         => false
    | .playSupporter  => true    -- older rules: supporters allowed T1
    | .attachEnergy   => true
    | .evolve         => false
    | .playItem       => true

-- ============================================================
-- §9  Example Cards
-- ============================================================

/-- Shaymin-EX (ROS 77) — Expanded-legal, pre-Standard rotation. -/
def shayminEX : CardEntry :=
  { name := "Shaymin-EX"
    setCode := "ROS"
    regulationMark := .smToSSH
    isBanned := [] }

/-- ADP (Arceus & Dialga & Palkia GX) — banned in Expanded. -/
def adpGX : CardEntry :=
  { name := "Arceus & Dialga & Palkia GX"
    setCode := "CEC"
    regulationMark := .smToSSH
    isBanned := [.expanded] }

/-- Charizard ex (OBF 125) — Standard and Expanded legal. -/
def charizardExOBF : CardEntry :=
  { name := "Charizard ex"
    setCode := "OBF"
    regulationMark := .G
    isBanned := [] }

/-- Pidgeot ex (OBF 164) — Standard and Expanded legal. -/
def pidgeotExOBF : CardEntry :=
  { name := "Pidgeot ex"
    setCode := "OBF"
    regulationMark := .G
    isBanned := [] }

/-- Iono (PAL 185) — Standard and Expanded legal. -/
def ionoPAL : CardEntry :=
  { name := "Iono"
    setCode := "PAL"
    regulationMark := .G
    isBanned := [] }

/-- Lysandre's Trump Card — banned in Expanded and Standard. -/
def lysandresTrumpCard : CardEntry :=
  { name := "Lysandre's Trump Card"
    setCode := "PHF"
    regulationMark := .bwToXY
    isBanned := [.standard, .expanded] }

/-- Forest of Giant Plants — banned in Expanded. -/
def forestOfGiantPlants : CardEntry :=
  { name := "Forest of Giant Plants"
    setCode := "AOR"
    regulationMark := .bwToXY
    isBanned := [.expanded] }

/-- Professor's Research (BRS) — reg mark F. -/
def profsResearchBRS : CardEntry :=
  { name := "Professor's Research"
    setCode := "BRS"
    regulationMark := .F
    isBanned := [] }

/-- Iron Hands ex (PAR) — reg mark H. -/
def ironHandsExPAR : CardEntry :=
  { name := "Iron Hands ex"
    setCode := "PAR"
    regulationMark := .H
    isBanned := [] }

/-- Mew VMAX (FST 114) — reg mark E. -/
def mewVMAXfst : CardEntry :=
  { name := "Mew VMAX"
    setCode := "FST"
    regulationMark := .E
    isBanned := [] }

/-- Comfey (LOR 079) — reg mark F. -/
def comfeyLOR : CardEntry :=
  { name := "Comfey"
    setCode := "LOR"
    regulationMark := .F
    isBanned := [] }

/-- Base Set Charizard — preBW era. -/
def baseSetCharizard : CardEntry :=
  { name := "Charizard"
    setCode := "BS"
    regulationMark := .preBW
    isBanned := [] }

/-- Lt. Surge's Strategy — pre-BW, banned in Expanded. -/
def ltSurgesStrategy : CardEntry :=
  { name := "Lt. Surge's Strategy"
    setCode := "HIF"
    regulationMark := .smToSSH
    isBanned := [.expanded] }

-- ============================================================
-- §10  Rotation Simulation
-- ============================================================

/-- Rotate: given new legal marks, produce a new RotationConfig. -/
def rotate (newMarks : List RegMark) (floor : RegMark) : RotationConfig :=
  { standardLegalMarks := newMarks, expandedFloor := floor }

/-- Marks removed by a rotation. -/
def removedMarks (old new_ : RotationConfig) : List RegMark :=
  old.standardLegalMarks.filter (fun m => !new_.standardLegalMarks.contains m)

/-- Marks added by a rotation. -/
def addedMarks (old new_ : RotationConfig) : List RegMark :=
  new_.standardLegalMarks.filter (fun m => !old.standardLegalMarks.contains m)

-- ============================================================
-- §11  Ban/Unban Operations
-- ============================================================

/-- Ban a card in a format. -/
def CardEntry.ban (card : CardEntry) (fmt : Format) : CardEntry :=
  if card.isBannedIn fmt then card
  else { card with isBanned := fmt :: card.isBanned }

/-- Unban a card in a format. -/
def CardEntry.unban (card : CardEntry) (fmt : Format) : CardEntry :=
  { card with isBanned := card.isBanned.filter (· != fmt) }

-- ============================================================
-- §12  Deck Format Validation
-- ============================================================

/-- Are all cards in a list format-legal? -/
def allCardsLegal (cfg : RotationConfig) (fmt : Format) (cards : List CardEntry) : Bool :=
  cards.all (isFormatLegal cfg fmt)

-- ============================================================
-- §13  Theorems — Format Legality Basics
-- ============================================================

/-- Unlimited accepts any card (not banned). -/
theorem unlimited_accepts_all (cfg : RotationConfig) (card : CardEntry)
    (h : card.isBanned.contains Format.unlimited = false) :
    isFormatLegal cfg .unlimited card = true := by
  simp [isFormatLegal, isMarkLegalUnlimited, CardEntry.isBannedIn, h]

/-- A banned card is not format-legal in its banned format (concrete example: ADP in Expanded). -/
theorem banned_not_legal_adp :
    isFormatLegal currentRotation .expanded adpGX = false := by native_decide

/-- A banned card is not format-legal (concrete: Lysandre's Trump Card in Expanded). -/
theorem banned_not_legal_ltc :
    isFormatLegal currentRotation .expanded lysandresTrumpCard = false := by native_decide

-- ============================================================
-- §14  Theorems — Shaymin-EX Scenarios
-- ============================================================

/-- Shaymin-EX is legal in Expanded. -/
theorem shaymin_expanded_legal :
    isFormatLegal currentRotation .expanded shayminEX = true := by native_decide

/-- Shaymin-EX is NOT legal in Standard (current rotation). -/
theorem shaymin_standard_illegal :
    isFormatLegal currentRotation .standard shayminEX = false := by native_decide

/-- Shaymin-EX is legal in Unlimited. -/
theorem shaymin_unlimited_legal :
    isFormatLegal currentRotation .unlimited shayminEX = true := by native_decide

-- ============================================================
-- §15  Theorems — ADP Scenarios
-- ============================================================

/-- ADP is banned in Expanded. -/
theorem adp_banned_expanded :
    isFormatLegal currentRotation .expanded adpGX = false := by native_decide

/-- ADP is not legal in Standard (rotated out). -/
theorem adp_not_standard :
    isFormatLegal currentRotation .standard adpGX = false := by native_decide

/-- ADP is legal in Unlimited (not banned there). -/
theorem adp_unlimited_legal :
    isFormatLegal currentRotation .unlimited adpGX = true := by native_decide

-- ============================================================
-- §16  Theorems — Standard ⊆ Expanded ⊆ Unlimited
-- ============================================================

/-- Mark G is Standard-legal and Expanded-legal. -/
theorem mark_G_both : isMarkLegalStandard currentRotation .G = true ∧
    isMarkLegalExpanded currentRotation .G = true := by
  constructor <;> native_decide

/-- Mark H is Standard-legal and Expanded-legal. -/
theorem mark_H_both : isMarkLegalStandard currentRotation .H = true ∧
    isMarkLegalExpanded currentRotation .H = true := by
  constructor <;> native_decide

/-- Mark I is Standard-legal and Expanded-legal. -/
theorem mark_I_both : isMarkLegalStandard currentRotation .I = true ∧
    isMarkLegalExpanded currentRotation .I = true := by
  constructor <;> native_decide

/-- Pre-BW marks are not Expanded-legal. -/
theorem preBW_not_expanded : isMarkLegalExpanded currentRotation .preBW = false := by native_decide

/-- Every Expanded-legal mark is also Unlimited-legal. -/
theorem expanded_mark_implies_unlimited (m : RegMark)
    (h : isMarkLegalExpanded currentRotation m = true) :
    isMarkLegalUnlimited m = true := by
  simp [isMarkLegalUnlimited]

/-- Unlimited always returns true for any mark. -/
theorem unlimited_always_true (m : RegMark) :
    isMarkLegalUnlimited m = true := by
  simp [isMarkLegalUnlimited]

-- ============================================================
-- §17  Theorems — Specific Card Format Legality
-- ============================================================

/-- Charizard ex (OBF) is Standard-legal. -/
theorem charizard_ex_standard :
    isFormatLegal currentRotation .standard charizardExOBF = true := by native_decide

/-- Charizard ex (OBF) is Expanded-legal. -/
theorem charizard_ex_expanded :
    isFormatLegal currentRotation .expanded charizardExOBF = true := by native_decide

/-- Pidgeot ex (OBF) is Standard-legal. -/
theorem pidgeot_ex_standard :
    isFormatLegal currentRotation .standard pidgeotExOBF = true := by native_decide

/-- Iono (PAL) is Standard-legal. -/
theorem iono_standard :
    isFormatLegal currentRotation .standard ionoPAL = true := by native_decide

/-- Iron Hands ex (PAR) is Standard-legal. -/
theorem iron_hands_standard :
    isFormatLegal currentRotation .standard ironHandsExPAR = true := by native_decide

/-- Base Set Charizard is not Standard-legal. -/
theorem base_charizard_not_standard :
    isFormatLegal currentRotation .standard baseSetCharizard = false := by native_decide

/-- Base Set Charizard is not Expanded-legal. -/
theorem base_charizard_not_expanded :
    isFormatLegal currentRotation .expanded baseSetCharizard = false := by native_decide

/-- Base Set Charizard IS Unlimited-legal. -/
theorem base_charizard_unlimited :
    isFormatLegal currentRotation .unlimited baseSetCharizard = true := by native_decide

/-- Mew VMAX (FST, mark E) is not current-Standard-legal. -/
theorem mew_vmax_not_standard :
    isFormatLegal currentRotation .standard mewVMAXfst = false := by native_decide

/-- Mew VMAX is Expanded-legal. -/
theorem mew_vmax_expanded :
    isFormatLegal currentRotation .expanded mewVMAXfst = true := by native_decide

/-- Comfey (LOR, mark F) is not current-Standard-legal. -/
theorem comfey_not_standard :
    isFormatLegal currentRotation .standard comfeyLOR = false := by native_decide

/-- Comfey is Expanded-legal. -/
theorem comfey_expanded :
    isFormatLegal currentRotation .expanded comfeyLOR = true := by native_decide

-- ============================================================
-- §18  Theorems — Ban List Properties
-- ============================================================

/-- Banning is idempotent: banning a card already banned returns the same card. -/
theorem ban_idempotent (card : CardEntry) (fmt : Format)
    (h : card.isBannedIn fmt = true) :
    card.ban fmt = card := by
  unfold CardEntry.ban
  simp [h]

/-- Banning ADP in Expanded then checking gives banned (concrete example). -/
theorem ban_then_check_adp :
    (adpGX.ban .expanded).isBannedIn .expanded = true := by native_decide

/-- Banning Charizard ex in Standard then checking gives banned. -/
theorem ban_then_check_charizard :
    (charizardExOBF.ban .standard).isBannedIn .standard = true := by native_decide

/-- Unbanning a card not on the list is a no-op (concrete: Charizard not banned). -/
theorem unban_not_banned_charizard :
    (charizardExOBF.unban .standard).isBanned = charizardExOBF.isBanned := by native_decide

/-- Lysandre's Trump Card is banned in Expanded. -/
theorem ltc_banned_expanded :
    isFormatLegal currentRotation .expanded lysandresTrumpCard = false := by native_decide

/-- Forest of Giant Plants is banned in Expanded. -/
theorem fogp_banned_expanded :
    isFormatLegal currentRotation .expanded forestOfGiantPlants = false := by native_decide

-- ============================================================
-- §19  Theorems — Rotation Mechanics
-- ============================================================

/-- Rotation from previous to current removes marks E and F. -/
theorem rotation_removes_E_F :
    removedMarks previousRotation currentRotation = [.E, .F] := by native_decide

/-- Rotation from previous to current adds mark I. -/
theorem rotation_adds_I :
    addedMarks previousRotation currentRotation = [.I] := by native_decide

/-- A card with mark E was legal in previous Standard. -/
theorem mark_E_was_standard :
    isMarkLegalStandard previousRotation .E = true := by native_decide

/-- A card with mark E is NOT legal in current Standard. -/
theorem mark_E_not_current :
    isMarkLegalStandard currentRotation .E = false := by native_decide

/-- Professor's Research (mark F) was Standard-legal, now is not. -/
theorem profs_research_rotated :
    isFormatLegal previousRotation .standard profsResearchBRS = true ∧
    isFormatLegal currentRotation .standard profsResearchBRS = false := by
  constructor <;> native_decide

-- ============================================================
-- §20  Theorems — First-Turn Rules
-- ============================================================

/-- Can't attack turn 1 going first in Standard. -/
theorem no_attack_t1_standard :
    isAllowedTurn1GoingFirst .standard .attack = false := by rfl

/-- Can't play Supporter turn 1 going first in Standard. -/
theorem no_supporter_t1_standard :
    isAllowedTurn1GoingFirst .standard .playSupporter = false := by rfl

/-- Can attach energy turn 1 going first in Standard. -/
theorem energy_ok_t1_standard :
    isAllowedTurn1GoingFirst .standard .attachEnergy = true := by rfl

/-- Can play Item turn 1 going first in Standard. -/
theorem item_ok_t1_standard :
    isAllowedTurn1GoingFirst .standard .playItem = true := by rfl

/-- Can't evolve turn 1 going first. -/
theorem no_evolve_t1 :
    isAllowedTurn1GoingFirst .standard .evolve = false := by rfl

/-- In Unlimited, Supporters are allowed turn 1 going first. -/
theorem supporter_ok_t1_unlimited :
    isAllowedTurn1GoingFirst .unlimited .playSupporter = true := by rfl

-- ============================================================
-- §21  Theorems — Format Decidability & Misc
-- ============================================================

/-- Format legality is decidable (Bool-valued). -/
theorem format_legality_decidable (cfg : RotationConfig) (fmt : Format) (card : CardEntry) :
    isFormatLegal cfg fmt card = true ∨ isFormatLegal cfg fmt card = false := by
  cases h : isFormatLegal cfg fmt card
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- allCardsLegal with empty list is true. -/
theorem empty_deck_legal (cfg : RotationConfig) (fmt : Format) :
    allCardsLegal cfg fmt [] = true := by
  simp [allCardsLegal, List.all]

/-- Lt. Surge's Strategy is banned in Expanded. -/
theorem lt_surge_banned :
    isFormatLegal currentRotation .expanded ltSurgesStrategy = false := by native_decide

/-- Mark ordering is total: for any two marks, one is ≤ the other. -/
theorem mark_order_total (a b : RegMark) :
    a.toNat ≤ b.toNat ∨ b.toNat ≤ a.toNat := by omega

end PokemonLean.Core.FormatChecker
