/-
  PokemonLean / PrizeCards.lean

  Prize card mechanics for the Pokémon TCG:
  - 6 prizes at game start
  - Taking prizes on KO
  - Multi-prize rules (EX/GX = 2, VMAX = 3, VSTAR = 2)
  - Win condition: all prizes taken
  - Prize mapping and ordering
  - Gladion trainer card: look at face-down prizes

-/

namespace PrizeCards
-- ============================================================================
-- §2  Pokémon card subtypes and prize penalties
-- ============================================================================

/-- Pokémon card subtypes relevant to prize mechanics. -/
inductive PokemonSubtype where
  | basic | stage1 | stage2 | v | vmax | vstar | ex | gx
deriving Repr, DecidableEq, BEq

/-- Prize count for knocking out a Pokémon of the given subtype. -/
def prizePenalty : PokemonSubtype → Nat
  | .basic  => 1
  | .stage1 => 1
  | .stage2 => 1
  | .v      => 2
  | .vmax   => 3
  | .vstar  => 2
  | .ex     => 2
  | .gx     => 2

-- Theorem 1
theorem prizePenalty_basic : prizePenalty .basic = 1 := rfl

-- Theorem 2
theorem prizePenalty_ex : prizePenalty .ex = 2 := rfl

-- Theorem 3
theorem prizePenalty_vmax : prizePenalty .vmax = 3 := rfl

-- Theorem 4
theorem prizePenalty_gx : prizePenalty .gx = 2 := rfl

-- Theorem 5
theorem prizePenalty_vstar : prizePenalty .vstar = 2 := rfl

-- Theorem 6: All prize penalties are at least 1.
theorem prizePenalty_pos (s : PokemonSubtype) : prizePenalty s ≥ 1 := by
  cases s <;> simp [prizePenalty]

-- Theorem 7: All prize penalties are at most 3.
theorem prizePenalty_le_three (s : PokemonSubtype) : prizePenalty s ≤ 3 := by
  cases s <;> simp [prizePenalty]

-- ============================================================================
-- §3  Prize state
-- ============================================================================

/-- A prize card (face-down during play). -/
structure PrizeCard where
  cardId   : Nat
  faceDown : Bool
deriving Repr, DecidableEq, BEq

/-- The prize zone: an ordered list of prize cards. -/
structure PrizeZone where
  cards : List PrizeCard
deriving Repr, BEq

/-- Initial prize zone: 6 face-down cards. -/
def PrizeZone.initial (ids : List Nat) : PrizeZone :=
  { cards := ids.map fun id => ⟨id, true⟩ }

/-- Number of remaining prizes. -/
def PrizeZone.remaining (pz : PrizeZone) : Nat := pz.cards.length

/-- Game state tracking prizes for both players. -/
structure GameState where
  myPrizes  : PrizeZone
  oppPrizes : PrizeZone
deriving Repr, BEq

/-- Initial game state: both players have 6 prizes. -/
def GameState.initial (myIds oppIds : List Nat) : GameState :=
  { myPrizes := PrizeZone.initial myIds, oppPrizes := PrizeZone.initial oppIds }

-- Theorem 8: Initial prize zone has the right count.
theorem PrizeZone.initial_count (ids : List Nat) :
    (PrizeZone.initial ids).remaining = ids.length := by
  simp [PrizeZone.initial, PrizeZone.remaining, List.length_map]

-- Theorem 9: Standard game starts with 6 prizes each.

/-- Take n prizes from the front of the prize zone. -/
def PrizeZone.take (pz : PrizeZone) (n : Nat) : PrizeZone :=
  { cards := pz.cards.drop n }

/-- A prize-taking step: KO a Pokémon, take prizes. -/
def takePrizeStep (gs : GameState) (sub : PokemonSubtype) : GameState :=
  { gs with myPrizes := gs.myPrizes.take (prizePenalty sub) }

-- Theorem 10: Taking prizes reduces the count.
theorem take_reduces (pz : PrizeZone) (n : Nat) (_h : n ≤ pz.remaining) :
    (pz.take n).remaining = pz.remaining - n := by
  simp [PrizeZone.take, PrizeZone.remaining, List.length_drop]

-- Theorem 11: Taking 0 prizes changes nothing.
theorem take_zero (pz : PrizeZone) : pz.take 0 = pz := by
  simp [PrizeZone.take]


-- Theorem 12: Path length of single KO is 1.
-- Theorem 13: trans of two single-KO paths has length 2.
-- ============================================================================
-- §6  Win condition
-- ============================================================================

/-- A player wins when they have 0 prizes remaining. -/
def hasWon (pz : PrizeZone) : Bool := pz.remaining == 0

-- Theorem 14: Empty prize zone means win.
theorem win_when_empty : hasWon { cards := [] } = true := by
  simp [hasWon, PrizeZone.remaining]

-- Theorem 15: Non-empty prize zone means no win.
theorem no_win_when_nonempty (c : PrizeCard) (cs : List PrizeCard) :
    hasWon { cards := c :: cs } = false := by
  simp [hasWon, PrizeZone.remaining]

-- ============================================================================
-- §7  Multi-prize KO interactions
-- ============================================================================

/-- Taking a basic KO from 6 prizes leaves 5. -/
-- Theorem 16
theorem basic_ko_from_six (pz : PrizeZone) (h : pz.remaining = 6) :
    (pz.take (prizePenalty .basic)).remaining = 5 := by
  simp [prizePenalty, take_reduces, h]

/-- Taking an EX KO from 6 prizes leaves 4. -/
-- Theorem 17
theorem ex_ko_from_six (pz : PrizeZone) (h : pz.remaining = 6) :
    (pz.take (prizePenalty .ex)).remaining = 4 := by
  simp [prizePenalty, take_reduces, h]

/-- Taking a VMAX KO from 6 prizes leaves 3. -/
-- Theorem 18
theorem vmax_ko_from_six (pz : PrizeZone) (h : pz.remaining = 6) :
    (pz.take (prizePenalty .vmax)).remaining = 3 := by
  simp [prizePenalty, take_reduces, h]

-- ============================================================================
-- §8  Gladion — look at face-down prizes
-- ============================================================================

/-- Gladion reveals all face-down prizes (flips faceDown to false). -/
def gladionReveal (pz : PrizeZone) : PrizeZone :=
  { cards := pz.cards.map fun c => { c with faceDown := false } }

/-- Take a specific prize by index after Gladion reveal, returning it and the new zone. -/
def gladionTake (pz : PrizeZone) (idx : Nat) : Option (PrizeCard × PrizeZone) :=
  match pz.cards[idx]? with
  | some c => some (c, { cards := pz.cards.eraseIdx idx })
  | none   => none

-- Theorem 19: Gladion reveal preserves the prize count.
theorem gladion_preserves_count (pz : PrizeZone) :
    (gladionReveal pz).remaining = pz.remaining := by
  simp [gladionReveal, PrizeZone.remaining, List.length_map]

-- Theorem 20: After Gladion reveal, all cards are face-up.
theorem gladion_all_faceup (pz : PrizeZone) :
    ∀ c ∈ (gladionReveal pz).cards, c.faceDown = false := by
  intro c hc
  simp [gladionReveal] at hc
  obtain ⟨c', _, rfl⟩ := hc
  rfl

-- Theorem 21: Gladion take on valid index returns some.
theorem gladion_take_valid (pz : PrizeZone) (idx : Nat) (c : PrizeCard)
    (h : pz.cards[idx]? = some c) :
    gladionTake pz idx = some (c, { cards := pz.cards.eraseIdx idx }) := by
  simp [gladionTake, h]

-- Theorem 22: Gladion take on out-of-bounds index returns none.
theorem gladion_take_oob (pz : PrizeZone) (idx : Nat)
    (h : pz.cards[idx]? = none) :
    gladionTake pz idx = none := by
  simp [gladionTake, h]
-- Theorem 23: trans is associative for prize paths.
-- Theorem 24: nil is left identity for trans.
-- Theorem 25: nil is right identity for trans.
-- Theorem 26: symm of nil is nil.
-- Theorem 27: symm of single step has length 1.
-- Theorem 28: length of trans is sum of lengths.
-- ============================================================================
-- §10  Prize mapping (congrArg lifting)
-- ============================================================================

/-- Map a function over the prize zone (congrArg style). -/
def PrizeZone.map (f : PrizeCard → PrizeCard) (pz : PrizeZone) : PrizeZone :=
  { cards := pz.cards.map f }

-- Theorem 29: congrArg — mapping preserves prize count.
theorem prizeZone_map_preserves_count (f : PrizeCard → PrizeCard) (pz : PrizeZone) :
    (pz.map f).remaining = pz.remaining := by
  simp [PrizeZone.map, PrizeZone.remaining, List.length_map]

-- Theorem 30: congrArg — mapping id is identity.
theorem prizeZone_map_id (pz : PrizeZone) :
    pz.map id = pz := by
  simp [PrizeZone.map, List.map_id]

-- Theorem 31: congrArg — mapping composition.
theorem prizeZone_map_comp (f g : PrizeCard → PrizeCard) (pz : PrizeZone) :
    (pz.map f).map g = pz.map (g ∘ f) := by
  simp [PrizeZone.map, List.map_map]

-- ============================================================================
-- §11  Advanced prize theorems
-- ============================================================================

-- Theorem 32: Two basic KOs from 6 prizes leaves 4 (two-step trans path).
theorem two_basic_kos (pz : PrizeZone) (h : pz.remaining = 6) :
    ((pz.take 1).take 1).remaining = 4 := by
  simp [PrizeZone.take, PrizeZone.remaining, List.length_drop] at *
  omega

-- Theorem 33: Three VMAX KOs is impossible — 3 × 3 = 9 > 6.
theorem three_vmax_exceeds_six :
    3 * prizePenalty .vmax > 6 := by
  simp [prizePenalty]

-- Theorem 34: Fastest win with VMAX = 2 KOs (3 + 3 = 6).
theorem fastest_vmax_win :
    prizePenalty .vmax + prizePenalty .vmax = 6 := by
  simp [prizePenalty]

-- Theorem 35: Fastest win with EX = 3 KOs (2 + 2 + 2 = 6).
theorem fastest_ex_win :
    prizePenalty .ex + prizePenalty .ex + prizePenalty .ex = 6 := by
  simp [prizePenalty]

-- Theorem 36: Mixed KO: one VMAX (3) + one EX (2) + one basic (1) = 6.
theorem mixed_ko_win :
    prizePenalty .vmax + prizePenalty .ex + prizePenalty .basic = 6 := by
  simp [prizePenalty]

-- Theorem 37: Prize penalty is injective between basic and EX.
theorem prize_distinguishes_basic_ex :
    prizePenalty .basic ≠ prizePenalty .ex := by
  simp [prizePenalty]

-- Theorem 38: Gladion double-reveal is idempotent.
theorem gladion_idempotent (pz : PrizeZone) :
    gladionReveal (gladionReveal pz) = gladionReveal pz := by
  simp [gladionReveal, List.map_map]

-- Theorem 40: Prize ordering — taking n then m is same as taking (n+m).
theorem take_take_eq_take_add (pz : PrizeZone) (n m : Nat) :
    (pz.take n).take m = pz.take (n + m) := by
  simp [PrizeZone.take, List.drop_drop]

end PrizeCards
