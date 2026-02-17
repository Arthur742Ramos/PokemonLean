/-
  PokemonLean / PrizeMapping.lean

  Prize card mechanics for the Pokémon TCG:
  - 6 prizes at game start
  - Multi-prize rules (EX/GX → 2, VMAX/Tag Team → 3)
  - Prize mapping strategy
  - N supporter (hand = prizes remaining)
  - Prize trade analysis, comeback mechanics

-/

namespace PrizeMapping
-- ============================================================================
-- §2  Prize Card Types
-- ============================================================================

/-- Card categories that affect prize count. -/
inductive CardCategory where
  | basic      : CardCategory   -- Regular Basic/Stage 1/Stage 2
  | exCard     : CardCategory   -- EX card (2 prizes)
  | gxCard     : CardCategory   -- GX card (2 prizes)
  | vCard      : CardCategory   -- V card (2 prizes)
  | vStar      : CardCategory   -- V-STAR (2 prizes)
  | vMax       : CardCategory   -- VMAX (3 prizes)
  | tagTeam    : CardCategory   -- Tag Team GX (3 prizes)
  | vUnion     : CardCategory   -- V-UNION (2 prizes)
deriving DecidableEq, Repr, BEq

/-- Prizes given up when a card is knocked out. -/
def prizesOnKO : CardCategory → Nat
  | .basic    => 1
  | .exCard   => 2
  | .gxCard   => 2
  | .vCard    => 2
  | .vStar    => 2
  | .vMax     => 3
  | .tagTeam  => 3
  | .vUnion   => 2

-- ============================================================================
-- §3  Game State
-- ============================================================================

structure PrizeState where
  myPrizes     : Nat    -- Prizes I still need to take
  oppPrizes    : Nat    -- Prizes opponent still needs to take
  myHand       : Nat    -- Cards in my hand
  oppHand      : Nat    -- Cards in opponent's hand
  turnNumber   : Nat
deriving DecidableEq, Repr, BEq

def PrizeState.initial : PrizeState :=
  { myPrizes := 6, oppPrizes := 6, myHand := 7, oppHand := 7, turnNumber := 1 }

-- ============================================================================
-- §4  Core Prize Theorems
-- ============================================================================

/-- Theorem 1: All categories give at least 1 prize. -/
theorem prizes_at_least_one (c : CardCategory) : prizesOnKO c ≥ 1 := by
  cases c <;> simp [prizesOnKO]

/-- Theorem 2: VMAX gives exactly 3 prizes. -/
theorem vmax_gives_three : prizesOnKO CardCategory.vMax = 3 := by rfl

/-- Theorem 3: Tag Team gives exactly 3 prizes. -/
theorem tag_team_gives_three : prizesOnKO CardCategory.tagTeam = 3 := by rfl

/-- Theorem 4: EX gives exactly 2 prizes. -/
theorem ex_gives_two : prizesOnKO CardCategory.exCard = 2 := by rfl

/-- Theorem 5: Basic gives exactly 1 prize. -/
theorem basic_gives_one : prizesOnKO CardCategory.basic = 1 := by rfl

/-- Theorem 6: No category gives more than 3 prizes. -/
theorem prizes_at_most_three (c : CardCategory) : prizesOnKO c ≤ 3 := by
  cases c <;> simp [prizesOnKO]

/-- Theorem 7: Multi-prize cards give ≥ 2. -/
theorem multi_prize_ge_two (c : CardCategory) (h : c ≠ .basic) : prizesOnKO c ≥ 2 := by
  cases c <;> simp [prizesOnKO] <;> contradiction

-- ============================================================================
-- §5  Prize KO Paths
-- ============================================================================

-- §7  Win Condition Analysis
-- ============================================================================

/-- Win condition: take all 6 prizes. -/
def winByPrizes (s : PrizeState) : Prop := s.myPrizes = 0

/-- Theorem 11: KOing two VMAXs from 6 prizes = win (3+3=6). -/
theorem two_vmax_ko_wins :
    let s := PrizeState.initial
    let s1 := { s with myPrizes := s.myPrizes - prizesOnKO .vMax }
    let s2 := { s1 with myPrizes := s1.myPrizes - prizesOnKO .vMax }
    winByPrizes s2 := by
  simp [PrizeState.initial, prizesOnKO, winByPrizes]

/-- Theorem 12: KOing three EX/GX from 6 prizes = win (2+2+2=6). -/
theorem three_ex_ko_wins :
    let s := PrizeState.initial
    let s1 := { s with myPrizes := s.myPrizes - prizesOnKO .exCard }
    let s2 := { s1 with myPrizes := s1.myPrizes - prizesOnKO .exCard }
    let s3 := { s2 with myPrizes := s2.myPrizes - prizesOnKO .exCard }
    winByPrizes s3 := by
  simp [PrizeState.initial, prizesOnKO, winByPrizes]

/-- Theorem 13: KOing six basics from 6 prizes = win. -/
theorem six_basic_ko_wins :
    let s0 := PrizeState.initial
    let s1 := { s0 with myPrizes := s0.myPrizes - 1 }
    let s2 := { s1 with myPrizes := s1.myPrizes - 1 }
    let s3 := { s2 with myPrizes := s2.myPrizes - 1 }
    let s4 := { s3 with myPrizes := s3.myPrizes - 1 }
    let s5 := { s4 with myPrizes := s4.myPrizes - 1 }
    let s6 := { s5 with myPrizes := s5.myPrizes - 1 }
    winByPrizes s6 := by
  simp [PrizeState.initial, winByPrizes]

-- ============================================================================
-- §8  N Supporter: Hand = Prizes Remaining
-- ============================================================================

/-- Theorem 15: N when opponent has 1 prize leaves them with 1 card. -/
theorem n_on_opponent_one_prize :
    let s : PrizeState := { myPrizes := 4, oppPrizes := 1, myHand := 3, oppHand := 5, turnNumber := 10 }
    let result := { s with myHand := s.myPrizes, oppHand := s.oppPrizes }
    result.oppHand = 1 := by rfl

/-- Theorem 16: N when behind (more prizes) gives you more cards. -/
theorem n_gives_more_when_behind (s : PrizeState) (h : s.myPrizes > s.oppPrizes) :
    let result := { s with myHand := s.myPrizes, oppHand := s.oppPrizes }
    result.myHand > result.oppHand := h

-- ============================================================================
-- §9  Prize Trade Analysis
-- ============================================================================

/-- Theorem 18: Favorable trade = I take more prizes than opponent. -/
theorem favorable_trade (myKO oppKO : CardCategory)
    (h : prizesOnKO myKO > prizesOnKO oppKO) :
    prizesOnKO myKO > prizesOnKO oppKO := h

/-- Theorem 19: KOing VMAX while losing basic is +2 prize advantage. -/
theorem vmax_vs_basic_advantage :
    prizesOnKO CardCategory.vMax - prizesOnKO CardCategory.basic = 2 := by rfl

-- ============================================================================
-- §10  Comeback Mechanics
-- ============================================================================


-- ============================================================================
-- §11  Prize Mapping Strategy
-- ============================================================================

/-- A prize map: sequence of planned KOs to win. -/
structure PrizeMap where
  targets : List CardCategory
  totalPrizes : Nat
  total_eq : totalPrizes = (targets.map prizesOnKO).foldl (· + ·) 0

/-- Theorem 21: Empty prize map gives 0 prizes. -/
theorem empty_prize_map_zero : (⟨[], 0, rfl⟩ : PrizeMap).totalPrizes = 0 := rfl

/-- Theorem 22: Two VMAX prize map gives 6. -/
theorem two_vmax_map_six :
    (⟨[.vMax, .vMax], 6, rfl⟩ : PrizeMap).totalPrizes = 6 := rfl

/-- Theorem 23: Three EX prize map gives 6. -/
theorem three_ex_map_six :
    (⟨[.exCard, .exCard, .exCard], 6, rfl⟩ : PrizeMap).totalPrizes = 6 := rfl

-- ============================================================================
-- §12  Full Game Win Path
-- ============================================================================


end PrizeMapping
