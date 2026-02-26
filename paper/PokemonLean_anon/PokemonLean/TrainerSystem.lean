import PokemonLean.Basic

namespace PokemonLean.TrainerSystem

open PokemonLean

-- ============================================================================
-- TRAINER CARD KINDS
-- ============================================================================

inductive TrainerKind
  | supporter
  | item
  | tool
  | stadium
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- SPECIFIC TRAINER CARDS
-- ============================================================================

inductive TrainerName
  | professorsResearch
  | bossOrders
  | rareCandy
  | switch
  | nestBall
  | ultraBall
  | levelBall
  | toolScrapper
  | fieldBlower
  | guzma
  | marnie
  | judge
  | cynthia
  | N
  | choiceBelt
  | floatStone
  | muscleband
  | pathToThePeak
  | collapsedStadium
  | templeOfSinnoh
  | customItem (name : String)
  | customSupporter (name : String)
  | customTool (name : String)
  | customStadium (name : String)
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- TRAINER EFFECT TYPES
-- ============================================================================

inductive TrainerEffect
  | drawCards (count : Nat)
  | discardAndDraw (discard draw : Nat)
  | switchOwnActive
  | switchOpponentActive
  | searchBasic
  | searchAny
  | skipEvolution
  | removeTool
  | replaceStadium
  | shuffleHandDraw (count : Nat)
  | healActive (amount : Nat)
  | boostDamage (amount : Nat)
  | reduceRetreatCost (amount : Nat)
  | noEffect
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- TRAINER CARD STRUCTURE
-- ============================================================================

structure TrainerCardDef where
  name : TrainerName
  kind : TrainerKind
  effect : TrainerEffect
  deriving Repr, BEq, DecidableEq

-- ============================================================================
-- STANDARD CARD DEFINITIONS
-- ============================================================================

def professorsResearch : TrainerCardDef :=
  { name := .professorsResearch, kind := .supporter, effect := .drawCards 7 }

def bossOrders : TrainerCardDef :=
  { name := .bossOrders, kind := .supporter, effect := .switchOpponentActive }

def rareCandy : TrainerCardDef :=
  { name := .rareCandy, kind := .item, effect := .skipEvolution }

def switchCard : TrainerCardDef :=
  { name := .switch, kind := .item, effect := .switchOwnActive }

def nestBall : TrainerCardDef :=
  { name := .nestBall, kind := .item, effect := .searchBasic }

def ultraBall : TrainerCardDef :=
  { name := .ultraBall, kind := .item, effect := .discardAndDraw 2 1 }

def toolScrapper : TrainerCardDef :=
  { name := .toolScrapper, kind := .item, effect := .removeTool }

def choiceBelt : TrainerCardDef :=
  { name := .choiceBelt, kind := .tool, effect := .boostDamage 30 }

def floatStone : TrainerCardDef :=
  { name := .floatStone, kind := .tool, effect := .reduceRetreatCost 100 }

def muscleBand : TrainerCardDef :=
  { name := .muscleband, kind := .tool, effect := .boostDamage 20 }

def pathToThePeak : TrainerCardDef :=
  { name := .pathToThePeak, kind := .stadium, effect := .noEffect }

def collapsedStadium : TrainerCardDef :=
  { name := .collapsedStadium, kind := .stadium, effect := .noEffect }

def marnie : TrainerCardDef :=
  { name := .marnie, kind := .supporter, effect := .shuffleHandDraw 5 }

def judge : TrainerCardDef :=
  { name := .judge, kind := .supporter, effect := .shuffleHandDraw 4 }

-- ============================================================================
-- KIND PREDICATES
-- ============================================================================

def isSupporter (tc : TrainerCardDef) : Bool :=
  match tc.kind with
  | .supporter => true
  | _ => false

def isItem (tc : TrainerCardDef) : Bool :=
  match tc.kind with
  | .item => true
  | _ => false

def isTool (tc : TrainerCardDef) : Bool :=
  match tc.kind with
  | .tool => true
  | _ => false

def isStadium (tc : TrainerCardDef) : Bool :=
  match tc.kind with
  | .stadium => true
  | _ => false

-- ============================================================================
-- SUPPORTER LOCK (max 1 per turn)
-- ============================================================================

structure TurnState where
  supporterPlayed : Bool := false
  itemsLocked : Bool := false
  stadiumInPlay : Option TrainerCardDef := none
  toolsAttached : List (TrainerCardDef × Nat) := []  -- tool × benchIndex
  deriving Repr, BEq, DecidableEq

def canPlaySupporter (ts : TurnState) : Bool :=
  !ts.supporterPlayed

def playSupporterUpdate (ts : TurnState) : TurnState :=
  { ts with supporterPlayed := true }

-- ============================================================================
-- ITEM LOCK (Vileplume / Gothitelle)
-- ============================================================================

def canPlayItem (ts : TurnState) : Bool :=
  !ts.itemsLocked

def lockItems (ts : TurnState) : TurnState :=
  { ts with itemsLocked := true }

def unlockItems (ts : TurnState) : TurnState :=
  { ts with itemsLocked := false }

-- ============================================================================
-- TOOL MECHANICS (max 1 per Pokemon)
-- ============================================================================

def hasToolAt (ts : TurnState) (benchIndex : Nat) : Bool :=
  ts.toolsAttached.any (fun (_, idx) => idx == benchIndex)

def canAttachTool (ts : TurnState) (benchIndex : Nat) : Bool :=
  !hasToolAt ts benchIndex

def attachTool (ts : TurnState) (tool : TrainerCardDef) (benchIndex : Nat) : Option TurnState :=
  if canAttachTool ts benchIndex then
    some { ts with toolsAttached := (tool, benchIndex) :: ts.toolsAttached }
  else
    none

def removeToolAt (ts : TurnState) (benchIndex : Nat) : TurnState :=
  { ts with toolsAttached := ts.toolsAttached.filter (fun (_, idx) => idx != benchIndex) }

-- ============================================================================
-- STADIUM MECHANICS (1 in play, replaced by new)
-- ============================================================================

def playStadium (ts : TurnState) (stadium : TrainerCardDef) : TurnState :=
  { ts with stadiumInPlay := some stadium }

def removeStadium (ts : TurnState) : TurnState :=
  { ts with stadiumInPlay := none }

def stadiumActive (ts : TurnState) : Bool :=
  ts.stadiumInPlay.isSome

-- ============================================================================
-- CARD LEGALITY
-- ============================================================================

def canPlayCard (ts : TurnState) (tc : TrainerCardDef) (benchIndex : Nat) : Bool :=
  match tc.kind with
  | .supporter => canPlaySupporter ts
  | .item => canPlayItem ts
  | .tool => canPlayItem ts && canAttachTool ts benchIndex
  | .stadium => canPlayItem ts

-- ============================================================================
-- COUNTING HELPERS
-- ============================================================================

def countSupporters : List TrainerCardDef → Nat
  | [] => 0
  | t :: rest => (if isSupporter t then 1 else 0) + countSupporters rest

def countItems : List TrainerCardDef → Nat
  | [] => 0
  | t :: rest => (if isItem t then 1 else 0) + countItems rest

def countTools : List TrainerCardDef → Nat
  | [] => 0
  | t :: rest => (if isTool t then 1 else 0) + countTools rest

def countStadiums : List TrainerCardDef → Nat
  | [] => 0
  | t :: rest => (if isStadium t then 1 else 0) + countStadiums rest

-- ============================================================================
-- TURN RESET
-- ============================================================================

def resetTurnState (ts : TurnState) : TurnState :=
  { ts with supporterPlayed := false }

-- ============================================================================
-- THEOREMS (30+)
-- ============================================================================

-- 1. Professor's Research is a supporter

-- 2. Boss's Orders is a supporter

-- 3. Rare Candy is an item

-- 4. Switch is an item

-- 5. Choice Belt is a tool

-- 6. Path to the Peak is a stadium

-- 7. Fresh turn allows supporter

-- 8. After supporter, can't play another

-- 9. Item lock blocks items

-- 10. Unlocking re-enables items

-- 11. Can't attach second tool to same slot
theorem no_double_tool (ts : TurnState) (tool1 : TrainerCardDef) (idx : Nat) (ts' : TurnState) :
    attachTool ts tool1 idx = some ts' →
    canAttachTool ts' idx = false := by
  intro h
  unfold attachTool at h
  by_cases hCan : canAttachTool ts idx
  · simp [hCan] at h
    cases h
    simp [canAttachTool, hasToolAt, List.any_cons, beq_self_eq_true]
  · simp [hCan] at h

-- 12. Playing stadium replaces old

-- 13. Remove stadium clears it

-- 14. Stadium active after play

-- 15. No stadium after remove

-- 16. Reset enables supporter again

-- 17. Reset preserves item lock

-- 18. Reset preserves stadium

-- 19. Reset preserves tools

-- 20. Supporter count ≤ length
theorem countSupporters_le_length (ts : List TrainerCardDef) :
    countSupporters ts ≤ ts.length := by
  induction ts with
  | nil => simp [countSupporters]
  | cons t rest ih => simp [countSupporters]; split <;> omega

-- 21. Item count ≤ length
theorem countItems_le_length (ts : List TrainerCardDef) :
    countItems ts ≤ ts.length := by
  induction ts with
  | nil => simp [countItems]
  | cons t rest ih => simp [countItems]; split <;> omega

-- 22. Tool count ≤ length
theorem countTools_le_length (ts : List TrainerCardDef) :
    countTools ts ≤ ts.length := by
  induction ts with
  | nil => simp [countTools]
  | cons t rest ih => simp [countTools]; split <;> omega

-- 23. Stadium count ≤ length
theorem countStadiums_le_length (ts : List TrainerCardDef) :
    countStadiums ts ≤ ts.length := by
  induction ts with
  | nil => simp [countStadiums]
  | cons t rest ih => simp [countStadiums]; split <;> omega

-- 24. Empty list has zero supporters

-- 25. Empty list has zero items

-- 26. Professor's Research draws 7

-- 27. Boss's Orders switches opponent

-- 28. Marnie shuffles and draws 5

-- 29. Judge shuffles and draws 4

-- 30. Choice Belt boosts 30

-- 31. Muscle Band boosts 20

-- 32. Float Stone reduces retreat

-- 33. Card kind is exclusive (supporter is not item)
theorem supporter_not_item (tc : TrainerCardDef) (h : isSupporter tc = true) :
    isItem tc = false := by
  cases hk : tc.kind <;> simp [isSupporter, hk] at h <;> simp [isItem, hk]

-- 34. Card kind is exclusive (item is not supporter)
theorem item_not_supporter (tc : TrainerCardDef) (h : isItem tc = true) :
    isSupporter tc = false := by
  cases hk : tc.kind <;> simp [isItem, hk] at h <;> simp [isSupporter, hk]

-- 35. Tool is not stadium
theorem tool_not_stadium (tc : TrainerCardDef) (h : isTool tc = true) :
    isStadium tc = false := by
  cases hk : tc.kind <;> simp [isTool, hk] at h <;> simp [isStadium, hk]

-- 36. Each card has exactly one kind
theorem kind_exclusive (tc : TrainerCardDef) :
    (isSupporter tc = true ∧ isItem tc = false ∧ isTool tc = false ∧ isStadium tc = false) ∨
    (isSupporter tc = false ∧ isItem tc = true ∧ isTool tc = false ∧ isStadium tc = false) ∨
    (isSupporter tc = false ∧ isItem tc = false ∧ isTool tc = true ∧ isStadium tc = false) ∨
    (isSupporter tc = false ∧ isItem tc = false ∧ isTool tc = false ∧ isStadium tc = true) := by
  cases hk : tc.kind <;> simp [isSupporter, isItem, isTool, isStadium, hk]

-- 37. Locked items means supporter-only play
theorem locked_items_supporter_only (ts : TurnState) (tc : TrainerCardDef)
    (hLocked : ts.itemsLocked = true) (hItem : isItem tc = true) (idx : Nat) :
    canPlayCard ts tc idx = false := by
  cases hKind : tc.kind <;> simp [isItem, hKind] at hItem <;> simp [canPlayCard, canPlayItem, hLocked, hKind]

-- 38. Remove tool then attach succeeds
theorem remove_then_attach_aux (tools : List (TrainerCardDef × Nat)) (idx : Nat) :
    (tools.filter (fun x => x.2 != idx)).any (fun x => x.2 == idx) = false := by
  induction tools with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.filter]
      by_cases hEq : p.2 = idx
      · -- filtered out
        have hNe : (p.2 != idx) = false := by
          simp [bne_iff_ne, hEq]
        simp [hNe, ih]
      · -- kept
        have hNe : (p.2 != idx) = true := by
          simp [bne_iff_ne, hEq]
        simp only [hNe, ite_true, List.any]
        have hBeq : (p.2 == idx) = false := by
          simp [beq_iff_eq, hEq]
        simp [hBeq, ih]

theorem remove_then_attach (ts : TurnState) (_tool : TrainerCardDef) (idx : Nat) :
    canAttachTool (removeToolAt ts idx) idx = true := by
  simp only [canAttachTool, hasToolAt, removeToolAt, Bool.not_eq_true']
  exact remove_then_attach_aux ts.toolsAttached idx

-- 39. Attach tool increases tool count
theorem attach_tool_increases (ts ts' : TurnState) (tool : TrainerCardDef) (idx : Nat)
    (h : attachTool ts tool idx = some ts') :
    ts'.toolsAttached.length = ts.toolsAttached.length + 1 := by
  unfold attachTool at h
  by_cases hCan : canAttachTool ts idx
  · simp [hCan] at h
    cases h; simp
  · simp [hCan] at h

-- 40. Lock then unlock is identity for itemsLocked

end PokemonLean.TrainerSystem
