/-
  PokemonLean / VUnionMechanics.lean

  V-UNION card mechanics for the Pokémon TCG:
  - Combining 2-4 V-UNION pieces from the discard pile
  - Cannot play on first turn or going-first turn
  - V-UNION counts as V for prize rules (2 prizes)
  - V-UNION can use any attack from its assembled pieces
  - Lost Zone interaction (pieces sent to Lost Zone can't be used)

-/

namespace VUnionMechanics
-- ============================================================================
-- §2  V-UNION types
-- ============================================================================

/-- V-UNION piece identifier (each piece is a separate card). -/
inductive PieceId where
  | piece1 | piece2 | piece3 | piece4
deriving DecidableEq, Repr, BEq

/-- An attack from a V-UNION piece. -/
structure VUnionAttack where
  name       : String
  damage     : Nat
  energyCost : Nat
deriving DecidableEq, Repr, BEq

/-- A V-UNION piece card. -/
structure VUnionPiece where
  pieceId   : PieceId
  pokeName  : String
  attacks   : List VUnionAttack
deriving DecidableEq, Repr, BEq

/-- Where a piece can be. -/
inductive PieceLocation where
  | deck     : PieceLocation
  | hand     : PieceLocation
  | discard  : PieceLocation
  | lostZone : PieceLocation
  | assembled : PieceLocation  -- part of an assembled V-UNION
deriving DecidableEq, Repr, BEq

/-- Turn phase relevant to V-UNION. -/
inductive TurnPhase where
  | firstTurnGoingFirst  : TurnPhase   -- can't play V-UNION
  | firstTurnGoingSecond : TurnPhase   -- can't play V-UNION
  | normalTurn           : TurnPhase   -- can play V-UNION
deriving DecidableEq, Repr, BEq

/-- Whether V-UNION can be played this turn. -/
def canPlayVUnion : TurnPhase → Bool
  | TurnPhase.firstTurnGoingFirst  => false
  | TurnPhase.firstTurnGoingSecond => false
  | TurnPhase.normalTurn           => true

/-- Prize count when a V-UNION is knocked out (counts as V). -/
def vunionPrizeCount : Nat := 2

-- ============================================================================
-- §3  Game state for V-UNION
-- ============================================================================

structure VUnionGameState where
  turnPhase       : TurnPhase
  piecesInDiscard : List PieceId
  piecesInLost    : List PieceId
  assembled       : Bool
  activeHP        : Nat
  availableAttacks : List VUnionAttack
  prizesRemaining : Nat
  opponentPrizes  : Nat
  turnNumber      : Nat
deriving DecidableEq, Repr, BEq

def VUnionGameState.initial : VUnionGameState :=
  { turnPhase := TurnPhase.firstTurnGoingFirst
  , piecesInDiscard := []
  , piecesInLost := []
  , assembled := false
  , activeHP := 0
  , availableAttacks := []
  , prizesRemaining := 6
  , opponentPrizes := 6
  , turnNumber := 1 }

-- ============================================================================
-- §4  Piece management steps
-- ============================================================================

/-- Check if we have enough pieces in discard for assembly. -/
def hasEnoughPieces (s : VUnionGameState) : Bool :=
  s.piecesInDiscard.length ≥ 2

/-- Theorem 2: Having 2 pieces in discard is sufficient. -/
theorem two_pieces_enough :
    hasEnoughPieces { VUnionGameState.initial with
      piecesInDiscard := [PieceId.piece1, PieceId.piece2] } = true := by
  native_decide

/-- Theorem 3: Having 0 pieces is not enough. -/
theorem zero_pieces_not_enough :
    hasEnoughPieces VUnionGameState.initial = false := by
  native_decide

-- ============================================================================
-- §5  Turn restriction — can't play on first turn
-- ============================================================================

/-- Theorem 4: Can't play V-UNION going first on turn 1. -/
theorem cant_play_going_first :
    canPlayVUnion TurnPhase.firstTurnGoingFirst = false := by
  native_decide

/-- Theorem 5: Can't play V-UNION going second on turn 1. -/
theorem cant_play_going_second :
    canPlayVUnion TurnPhase.firstTurnGoingSecond = false := by
  native_decide

/-- Theorem 6: Can play V-UNION on normal turns. -/
theorem can_play_normal :
    canPlayVUnion TurnPhase.normalTurn = true := by
  native_decide

-- ============================================================================
-- §6  Assembly process as multi-step path
-- ============================================================================

/-- State labels for the assembly process. -/
inductive AssemblyPhase where
  | noDiscard        : AssemblyPhase   -- no pieces in discard yet
  | oneInDiscard     : AssemblyPhase   -- 1 piece discarded
  | twoInDiscard     : AssemblyPhase   -- 2 pieces discarded (minimum)
  | threeInDiscard   : AssemblyPhase   -- 3 pieces discarded
  | fourInDiscard    : AssemblyPhase   -- all 4 discarded
  | assembled        : AssemblyPhase   -- V-UNION assembled on bench
  | promoted         : AssemblyPhase   -- V-UNION promoted to active
deriving DecidableEq, Repr, BEq


-- ============================================================================
-- §7  Prize rules — V-UNION counts as V
-- ============================================================================

/-- Theorem 13: V-UNION knockout gives opponent 2 prizes. -/
theorem vunion_prize_is_two : vunionPrizeCount = 2 := by
  rfl

/-- Battle state labels. -/
inductive BattlePhase where
  | active       : BattlePhase  -- V-UNION is active
  | damaged      : BattlePhase  -- took damage
  | knockedOut   : BattlePhase  -- KO'd
  | prizesTaken  : BattlePhase  -- opponent takes 2 prizes
deriving DecidableEq, Repr, BEq


-- ============================================================================
-- §8  Lost Zone interaction
-- ============================================================================

/-- Lost Zone state labels. -/
inductive LostZonePhase where
  | inDiscard    : LostZonePhase   -- piece is in discard
  | sentToLost   : LostZonePhase   -- piece sent to Lost Zone
  | unrecoverable : LostZonePhase  -- confirmed unrecoverable
deriving DecidableEq, Repr, BEq


-- ============================================================================
-- §9  Attack selection from assembled pieces
-- ============================================================================

/-- Attack selection state. -/
inductive AttackPhase where
  | selectAttack    : AttackPhase
  | energyChecked   : AttackPhase
  | attackDeclared  : AttackPhase
  | damageApplied   : AttackPhase
deriving DecidableEq, Repr, BEq


-- ============================================================================
-- §10  Path composition and coherence
-- ============================================================================


end VUnionMechanics
