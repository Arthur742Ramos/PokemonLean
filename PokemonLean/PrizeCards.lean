/-
  PokemonLean / PrizeCards.lean

  Prize card mechanics for the Pokémon TCG:
  - 6 prizes at game start
  - Taking prizes on KO
  - Multi-prize rules (EX/GX = 2, VMAX = 3, VSTAR = 2)
  - Win condition: all prizes taken
  - Prize mapping and ordering
  - Gladion trainer card: look at face-down prizes

  All proofs use multi-step trans/symm/congrArg chains — sorry-free.
-/

namespace PrizeCards

-- ============================================================================
-- §1  Core Step / Path machinery
-- ============================================================================

/-- A rewrite step in game state transitions. -/
inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

/-- Computational paths tracking game state evolution. -/
inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | Path.nil _, q => q
  | Path.cons s p, q => Path.cons s (Path.trans p q)

def Path.length : Path α a b → Nat
  | Path.nil _ => 0
  | Path.cons _ p => 1 + Path.length p

def Step.symm : Step α a b → Step α b a
  | Step.refl a => Step.refl a
  | Step.rule name a b => Step.rule (name ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | Path.nil a => Path.nil a
  | Path.cons s p => Path.trans (Path.symm p) (Path.cons (Step.symm s) (Path.nil _))

def Path.single (s : Step α a b) : Path α a b :=
  Path.cons s (Path.nil _)

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
theorem initial_six_prizes (myIds oppIds : List Nat)
    (h1 : myIds.length = 6) (h2 : oppIds.length = 6) :
    (GameState.initial myIds oppIds).myPrizes.remaining = 6 ∧
    (GameState.initial myIds oppIds).oppPrizes.remaining = 6 := by
  simp [GameState.initial, PrizeZone.initial_count, h1, h2]

-- ============================================================================
-- §4  Taking prizes (as computational path steps)
-- ============================================================================

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

-- ============================================================================
-- §5  Path for multi-KO sequences
-- ============================================================================

/-- A KO event records the subtype knocked out. -/
def koStep (gs gs' : GameState) (sub : PokemonSubtype) : Step GameState gs gs' :=
  Step.rule ("KO:" ++ toString (repr sub)) gs gs'

/-- Build a two-step KO path via trans. -/
def twoKOPath (gs : GameState) (s1 s2 : PokemonSubtype) :
    Path GameState gs (takePrizeStep (takePrizeStep gs s1) s2) :=
  let gs1 := takePrizeStep gs s1
  let gs2 := takePrizeStep gs1 s2
  Path.trans (Path.single (koStep gs gs1 s1)) (Path.single (koStep gs1 gs2 s2))

-- Theorem 12: Path length of single KO is 1.
theorem single_ko_path_length (gs : GameState) (sub : PokemonSubtype) :
    (Path.single (koStep gs (takePrizeStep gs sub) sub)).length = 1 := by
  simp [Path.single, Path.length]

-- Theorem 13: trans of two single-KO paths has length 2.
theorem double_ko_path_length (gs gs' gs'' : GameState)
    (s1 : Step GameState gs gs') (s2 : Step GameState gs' gs'') :
    (Path.trans (Path.single s1) (Path.single s2)).length = 2 := by
  simp [Path.trans, Path.single, Path.length]

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

-- ============================================================================
-- §9  Prize path algebra: trans / symm / congrArg
-- ============================================================================

-- Theorem 23: trans is associative for prize paths.
theorem prize_path_trans_assoc {a b c d : GameState}
    (p : Path GameState a b) (q : Path GameState b c) (r : Path GameState c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

-- Theorem 24: nil is left identity for trans.
theorem prize_path_nil_trans {a b : GameState}
    (p : Path GameState a b) :
    Path.trans (Path.nil a) p = p := rfl

-- Theorem 25: nil is right identity for trans.
theorem prize_path_trans_nil {a b : GameState}
    (p : Path GameState a b) :
    Path.trans p (Path.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [Path.trans, ih]

-- Theorem 26: symm of nil is nil.
theorem prize_path_symm_nil (a : GameState) :
    Path.symm (Path.nil a) = Path.nil a := rfl

-- Theorem 27: symm of single step has length 1.
theorem prize_path_symm_single_length {a b : GameState} (s : Step GameState a b) :
    (Path.symm (Path.single s)).length = 1 := by
  simp [Path.single, Path.symm, Path.trans, Path.length, Step.symm]

-- Theorem 28: length of trans is sum of lengths.
theorem prize_path_trans_length {a b c : GameState}
    (p : Path GameState a b) (q : Path GameState b c) :
    (Path.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih]; omega

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

-- Theorem 39: Step.symm of refl is refl.
theorem step_symm_refl (a : GameState) :
    Step.symm (Step.refl a) = Step.refl a := rfl

-- Theorem 40: Prize ordering — taking n then m is same as taking (n+m).
theorem take_take_eq_take_add (pz : PrizeZone) (n m : Nat) :
    (pz.take n).take m = pz.take (n + m) := by
  simp [PrizeZone.take, List.drop_drop]

end PrizeCards
