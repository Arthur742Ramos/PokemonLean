/-
  PokemonLean / GXMechanics.lean

  GX attack mechanics for the Pokémon TCG:
  - Once-per-game GX attack usage and GX marker
  - Tag Team GX cards (extra effect with bonus energy)
  - Prize penalty: 2 for regular GX, 3 for Tag Team GX
  - GX attack declaration, resolution, and state transitions

-/

namespace GXMechanics
-- ============================================================================
-- §2  GX types and structures
-- ============================================================================

/-- Whether a player has used their GX attack this game. -/
inductive GXMarker : Type where
  | unused : GXMarker
  | used   : GXMarker
deriving Repr, DecidableEq, BEq

/-- Pokémon-GX subtype. -/
inductive GXSubtype : Type where
  | regularGX : GXSubtype
  | tagTeamGX : GXSubtype
deriving Repr, DecidableEq, BEq

/-- Prize penalty for knocking out a GX Pokémon. -/
def gxPrizePenalty : GXSubtype → Nat
  | .regularGX => 2
  | .tagTeamGX => 3

/-- Energy types (simplified). -/
inductive EnergyType : Type where
  | fire | water | grass | lightning | psychic | fighting
  | darkness | metal | fairy | colorless
deriving Repr, DecidableEq, BEq

/-- A GX attack definition. -/
structure GXAttack where
  name       : String
  baseDamage : Nat
  energyCost : List EnergyType
deriving Repr, DecidableEq

/-- Tag Team bonus: extra effect triggered when extra energy attached. -/
structure TagTeamBonus where
  extraEnergyCost : List EnergyType
  bonusDamage     : Nat
deriving Repr, DecidableEq

/-- A GX Pokémon card. -/
structure GXCard where
  name      : String
  hp        : Nat
  subtype   : GXSubtype
  gxAttack  : GXAttack
  tagBonus  : Option TagTeamBonus
deriving Repr, DecidableEq

-- ============================================================================
-- §3  Game state
-- ============================================================================

/-- Simplified game state relevant to GX mechanics. -/
structure GXGameState where
  gxMarker        : GXMarker
  activeHP        : Nat
  opponentHP      : Nat
  attachedEnergy  : List EnergyType
  prizesRemaining : Nat
  opponentPrizes  : Nat
deriving Repr, DecidableEq

/-- Initial game state. -/
def GXGameState.initial (myHP oppHP : Nat) : GXGameState :=
  { gxMarker := .unused, activeHP := myHP, opponentHP := oppHP,
    attachedEnergy := [], prizesRemaining := 6, opponentPrizes := 6 }

-- ============================================================================
-- §4  Energy checking
-- ============================================================================

/-- Check if attached energy satisfies a cost (simplified: count-based). -/
def hasEnoughEnergy (attached : List EnergyType) (cost : List EnergyType) : Bool :=
  cost.length ≤ attached.length

/-- Check if a Tag Team bonus is affordable. -/
def canPayBonus (attached : List EnergyType) (atk : GXAttack)
    (bonus : TagTeamBonus) : Bool :=
  (atk.energyCost.length + bonus.extraEnergyCost.length) ≤ attached.length

-- ============================================================================
-- §5  GX attack legality
-- ============================================================================

/-- A GX attack is legal if the marker is unused and energy suffices. -/
def gxAttackLegal (gs : GXGameState) (card : GXCard) : Bool :=
  gs.gxMarker == .unused && hasEnoughEnergy gs.attachedEnergy card.gxAttack.energyCost

/-- Theorem 1 – GX attack is illegal if marker is already used. -/
theorem gxAttack_illegal_if_used (gs : GXGameState) (card : GXCard)
    (h : gs.gxMarker = .used) : gxAttackLegal gs card = false := by
  unfold gxAttackLegal
  rw [h]
  rfl

/-- Theorem 2 – GX marker unused means the BEq check passes. -/
theorem gxMarker_unused_beq : (GXMarker.unused == GXMarker.unused) = true := by
  native_decide

-- ============================================================================
-- §6  GX attack resolution
-- ============================================================================

/-- Apply a GX attack: deal damage, flip the marker to used. -/
def resolveGXAttack (gs : GXGameState) (card : GXCard) : GXGameState :=
  { gs with
    gxMarker := .used
    opponentHP := gs.opponentHP - card.gxAttack.baseDamage }

/-- Apply a Tag Team GX attack with bonus (if affordable). -/
def resolveTagTeamGX (gs : GXGameState) (card : GXCard) : GXGameState :=
  let bonusDmg := match card.tagBonus with
    | some b => if canPayBonus gs.attachedEnergy card.gxAttack b then b.bonusDamage else 0
    | none => 0
  { gs with
    gxMarker := .used
    opponentHP := gs.opponentHP - (card.gxAttack.baseDamage + bonusDmg) }

/-- Theorem 3 – After resolving a GX attack, the marker is used. -/
theorem resolveGXAttack_marks_used (gs : GXGameState) (card : GXCard) :
    (resolveGXAttack gs card).gxMarker = .used := by
  simp [resolveGXAttack]

/-- Theorem 4 – After resolving a Tag Team GX attack, the marker is used. -/
theorem resolveTagTeamGX_marks_used (gs : GXGameState) (card : GXCard) :
    (resolveTagTeamGX gs card).gxMarker = .used := by
  simp [resolveTagTeamGX]

/-- Theorem 5 – GX attack resolution doesn't change own HP. -/
theorem resolveGXAttack_preserves_hp (gs : GXGameState) (card : GXCard) :
    (resolveGXAttack gs card).activeHP = gs.activeHP := by
  simp [resolveGXAttack]

/-- Theorem 6 – GX attack resolution doesn't change prizes. -/
theorem resolveGXAttack_preserves_prizes (gs : GXGameState) (card : GXCard) :
    (resolveGXAttack gs card).prizesRemaining = gs.prizesRemaining := by
  simp [resolveGXAttack]

-- ============================================================================
-- §7  Prize penalty theorems
-- ============================================================================

/-- Theorem 7 – Regular GX gives 2 prizes. -/
theorem regularGX_prize_penalty : gxPrizePenalty .regularGX = 2 := rfl

/-- Theorem 8 – Tag Team GX gives 3 prizes. -/
theorem tagTeamGX_prize_penalty : gxPrizePenalty .tagTeamGX = 3 := rfl

/-- Theorem 9 – Tag Team always gives more prizes than regular GX. -/
theorem tagTeam_more_prizes :
    gxPrizePenalty .tagTeamGX > gxPrizePenalty .regularGX := by
  native_decide

/-- Take prizes after a KO. -/
def takePrizesOnKO (gs : GXGameState) (subtype : GXSubtype) : GXGameState :=
  { gs with opponentPrizes := gs.opponentPrizes - gxPrizePenalty subtype }

/-- Theorem 10 – Taking prizes after KO'ing a regular GX reduces by 2. -/
theorem takePrizes_regularGX (gs : GXGameState) (_h : gs.opponentPrizes ≥ 2) :
    (takePrizesOnKO gs .regularGX).opponentPrizes = gs.opponentPrizes - 2 := by
  simp [takePrizesOnKO, gxPrizePenalty]

/-- Theorem 11 – Taking prizes after KO'ing a Tag Team GX reduces by 3. -/
theorem takePrizes_tagTeamGX (gs : GXGameState) (_h : gs.opponentPrizes ≥ 3) :
    (takePrizesOnKO gs .tagTeamGX).opponentPrizes = gs.opponentPrizes - 3 := by
  simp [takePrizesOnKO, gxPrizePenalty]

-- ============================================================================
-- §8  Path-based GX attack workflow
-- ==========================================================================
-- §10  Concrete GX cards
-- ============================================================================

/-- Tapu Lele-GX: a regular GX. -/
def tapuLeleGX : GXCard :=
  { name := "Tapu Lele-GX"
    hp := 170
    subtype := .regularGX
    gxAttack := { name := "Tapu Cure GX", baseDamage := 0, energyCost := [.psychic] }
    tagBonus := none }

/-- Pikachu & Zekrom-GX: a Tag Team GX. -/
def pikaZekGX : GXCard :=
  { name := "Pikachu & Zekrom-GX"
    hp := 240
    subtype := .tagTeamGX
    gxAttack := { name := "Tag Bolt GX", baseDamage := 200,
                   energyCost := [.lightning, .lightning, .lightning] }
    tagBonus := some { extraEnergyCost := [.lightning, .lightning, .lightning],
                       bonusDamage := 170 } }

/-- Theorem 16 – Tapu Lele is a regular GX. -/
theorem tapuLele_is_regularGX : tapuLeleGX.subtype = .regularGX := rfl

/-- Theorem 17 – PikaZek is a Tag Team GX. -/
theorem pikaZek_is_tagTeam : pikaZekGX.subtype = .tagTeamGX := rfl

/-- Theorem 18 – PikaZek has 240 HP. -/
theorem pikaZek_hp : pikaZekGX.hp = 240 := rfl

/-- Theorem 19 – PikaZek KO gives 3 prizes. -/
theorem pikaZek_prizes : gxPrizePenalty pikaZekGX.subtype = 3 := rfl

/-- Theorem 20 – Tapu Lele KO gives 2 prizes. -/
theorem tapuLele_prizes : gxPrizePenalty tapuLeleGX.subtype = 2 := rfl

-- ============================================================================
-- §11  GX marker idempotence and coherence
-- ============================================================================

/-- Resolving GX attack twice gives same marker state (idempotent on marker). -/
theorem resolveGXAttack_marker_idempotent (gs : GXGameState) (c1 c2 : GXCard) :
    (resolveGXAttack (resolveGXAttack gs c1) c2).gxMarker = .used := by
  simp [resolveGXAttack]

/-- Theorem 21 – Cannot legally use GX attack after already resolving one. -/
theorem gxAttack_illegal_after_resolve (gs : GXGameState) (c1 c2 : GXCard) :
    gxAttackLegal (resolveGXAttack gs c1) c2 = false := by
  unfold gxAttackLegal resolveGXAttack
  rfl

/-- Theorem 22 – Initial game state has unused GX marker. -/
theorem initial_gx_unused (hp1 hp2 : Nat) :
    (GXGameState.initial hp1 hp2).gxMarker = .unused := by
  simp [GXGameState.initial]

/-- Theorem 23 – Initial game state has 6 prizes for each player. -/
theorem initial_prizes (hp1 hp2 : Nat) :
    (GXGameState.initial hp1 hp2).prizesRemaining = 6 ∧
    (GXGameState.initial hp1 hp2).opponentPrizes = 6 := by
  simp [GXGameState.initial]

-- ============================================================================
-- §12  Symm paths: undoing a GX attack (hypothetical rewind)
-- ============================================================================


end GXMechanics
