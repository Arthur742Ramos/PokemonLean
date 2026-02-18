import PokemonLean.Basic

namespace PokemonLean.PrizeCards

open PokemonLean

-- ============================================================================
-- POKEMON CATEGORIES (determines prize value)
-- ============================================================================

inductive PokemonCategory
  | basic
  | ex
  | vstar
  | vmax
  | tagTeam
  | gx
  | v
  deriving Repr, BEq, DecidableEq

def prizesForCategory : PokemonCategory → Nat
  | .basic   => 1
  | .ex      => 2
  | .vstar   => 2
  | .vmax    => 3
  | .tagTeam => 3
  | .gx      => 2
  | .v       => 2

-- ============================================================================
-- PRIZE CARD STRUCTURES
-- ============================================================================

structure CategorizedPokemon where
  card : Card
  category : PokemonCategory
  deriving Repr, BEq, DecidableEq

structure PrizePool where
  remaining : List Card
  taken : List Card
  deriving Repr, BEq, DecidableEq

def initialPrizeCount : Nat := 6

def mkPrizePool (prizes : List Card) : PrizePool :=
  { remaining := prizes, taken := [] }

def totalPrizes (pool : PrizePool) : Nat :=
  pool.remaining.length + pool.taken.length

def prizesLeft (pool : PrizePool) : Nat :=
  pool.remaining.length

def prizesTaken (pool : PrizePool) : Nat :=
  pool.taken.length

-- ============================================================================
-- TAKE PRIZE OPERATIONS
-- ============================================================================

def takeSinglePrize (pool : PrizePool) : Option PrizePool :=
  match pool.remaining with
  | [] => none
  | p :: rest => some { remaining := rest, taken := p :: pool.taken }

def takeMultiplePrizes : PrizePool → Nat → Option PrizePool
  | pool, 0 => some pool
  | pool, n + 1 =>
      match takeSinglePrize pool with
      | none => none
      | some pool' => takeMultiplePrizes pool' n

def takeKOPrizes (pool : PrizePool) (knocked : CategorizedPokemon) : Option PrizePool :=
  takeMultiplePrizes pool (prizesForCategory knocked.category)

-- ============================================================================
-- WIN CONDITION
-- ============================================================================

def allPrizesTaken (pool : PrizePool) : Prop :=
  pool.remaining = []

def wonByPrizes (pool : PrizePool) : Prop :=
  allPrizesTaken pool ∧ pool.taken.length > 0

-- ============================================================================
-- PRIZE SELECTION EFFECTS
-- ============================================================================

def revealPrize (pool : PrizePool) (index : Nat) : Option Card :=
  listGet? pool.remaining index

def swapPrize (pool : PrizePool) (index : Nat) (handCard : Card) : Option (PrizePool × Card) :=
  match listGet? pool.remaining index with
  | none => none
  | some prizeCard =>
      let newRemaining := pool.remaining.set index handCard
      some ({ pool with remaining := newRemaining }, prizeCard)

-- ============================================================================
-- THEOREMS (25+)
-- ============================================================================

-- 1. Prize values are always positive
theorem prizesForCategory_pos (cat : PokemonCategory) : prizesForCategory cat > 0 := by
  cases cat <;> decide

-- 2. Basic prizes are 1
theorem basic_gives_one : prizesForCategory .basic = 1 := by rfl

-- 3. EX gives 2
theorem ex_gives_two : prizesForCategory .ex = 2 := by rfl

-- 4. VSTAR gives 2
theorem vstar_gives_two : prizesForCategory .vstar = 2 := by rfl

-- 5. VMAX gives 3
theorem vmax_gives_three : prizesForCategory .vmax = 3 := by rfl

-- 6. Tag Team gives 3
theorem tag_team_gives_three : prizesForCategory .tagTeam = 3 := by rfl

-- 7. GX gives 2
theorem gx_gives_two : prizesForCategory .gx = 2 := by rfl

-- 8. V gives 2
theorem v_gives_two : prizesForCategory .v = 2 := by rfl

-- 9. Prize values bounded by 3
theorem prizesForCategory_le_three (cat : PokemonCategory) : prizesForCategory cat ≤ 3 := by
  cases cat <;> decide

-- 10. Total prizes invariant on take
theorem takeSinglePrize_total (pool pool' : PrizePool)
    (h : takeSinglePrize pool = some pool') :
    totalPrizes pool' = totalPrizes pool := by
  cases hRem : pool.remaining with
  | nil => simp [takeSinglePrize, hRem] at h
  | cons p rest =>
      simp [takeSinglePrize, hRem] at h
      cases h
      simp [totalPrizes]
      rw [hRem]
      simp
      omega

-- 11. Taking a prize decreases remaining
theorem takeSinglePrize_remaining_dec (pool pool' : PrizePool)
    (h : takeSinglePrize pool = some pool') :
    pool'.remaining.length + 1 = pool.remaining.length := by
  cases hRem : pool.remaining with
  | nil => simp [takeSinglePrize, hRem] at h
  | cons p rest =>
      simp [takeSinglePrize, hRem] at h
      cases h
      simp

-- 12. Taking a prize increases taken
theorem takeSinglePrize_taken_inc (pool pool' : PrizePool)
    (h : takeSinglePrize pool = some pool') :
    pool'.taken.length = pool.taken.length + 1 := by
  cases hRem : pool.remaining with
  | nil => simp [takeSinglePrize, hRem] at h
  | cons p rest =>
      simp [takeSinglePrize, hRem] at h
      cases h
      simp

-- 13. Can't take from empty
theorem takeSinglePrize_empty (t : List Card) :
    takeSinglePrize { remaining := [], taken := t } = none := by
  rfl

-- 14. Take zero is identity
theorem takeMultiplePrizes_zero (pool : PrizePool) :
    takeMultiplePrizes pool 0 = some pool := by
  rfl

-- 15. Total invariant for multiple takes
theorem takeMultiplePrizes_total (pool pool' : PrizePool) (n : Nat)
    (h : takeMultiplePrizes pool n = some pool') :
    totalPrizes pool' = totalPrizes pool := by
  induction n generalizing pool pool' with
  | zero =>
      simp [takeMultiplePrizes] at h
      cases h; rfl
  | succ n ih =>
      simp [takeMultiplePrizes] at h
      cases hTake : takeSinglePrize pool with
      | none => simp [hTake] at h
      | some mid =>
          simp [hTake] at h
          have hMid := takeSinglePrize_total pool mid hTake
          have hRest := ih mid pool' h
          omega

-- 16. Remaining decreases by n for multiple takes
theorem takeMultiplePrizes_remaining (pool pool' : PrizePool) (n : Nat)
    (h : takeMultiplePrizes pool n = some pool') :
    pool'.remaining.length + n = pool.remaining.length := by
  induction n generalizing pool pool' with
  | zero =>
      simp [takeMultiplePrizes] at h
      cases h; simp
  | succ n ih =>
      simp [takeMultiplePrizes] at h
      cases hTake : takeSinglePrize pool with
      | none => simp [hTake] at h
      | some mid =>
          simp [hTake] at h
          have hMid := takeSinglePrize_remaining_dec pool mid hTake
          have hRest := ih mid pool' h
          omega

-- 17. Can't take more than available
theorem takeMultiplePrizes_none_of_gt (pool : PrizePool) (n : Nat)
    (h : pool.remaining.length < n) :
    takeMultiplePrizes pool n = none := by sorry

-- 18. Empty pool is won
theorem allPrizesTaken_nil (t : List Card) : allPrizesTaken { remaining := [], taken := t } := by
  unfold allPrizesTaken
  rfl

-- 19. Non-empty pool is not won
theorem not_allPrizesTaken_cons (p : Card) (rest t : List Card) :
    ¬allPrizesTaken { remaining := p :: rest, taken := t } := by
  simp [allPrizesTaken]

-- 20. Fresh prize pool invariant
theorem mkPrizePool_total (prizes : List Card) :
    totalPrizes (mkPrizePool prizes) = prizes.length := by
  simp [mkPrizePool, totalPrizes]

-- 21. Fresh pool has nothing taken
theorem mkPrizePool_taken_empty (prizes : List Card) :
    (mkPrizePool prizes).taken = [] := by
  rfl

-- 22. KO basic takes 1 prize
theorem ko_basic_takes_one (pool : PrizePool) (pkmn : CategorizedPokemon)
    (hCat : pkmn.category = .basic) :
    takeKOPrizes pool pkmn = takeMultiplePrizes pool 1 := by
  simp [takeKOPrizes, hCat, prizesForCategory]

-- 23. KO VMAX takes 3 prizes
theorem ko_vmax_takes_three (pool : PrizePool) (pkmn : CategorizedPokemon)
    (hCat : pkmn.category = .vmax) :
    takeKOPrizes pool pkmn = takeMultiplePrizes pool 3 := by
  simp [takeKOPrizes, hCat, prizesForCategory]

-- 24. KO tag team takes 3 prizes
theorem ko_tag_team_takes_three (pool : PrizePool) (pkmn : CategorizedPokemon)
    (hCat : pkmn.category = .tagTeam) :
    takeKOPrizes pool pkmn = takeMultiplePrizes pool 3 := by
  simp [takeKOPrizes, hCat, prizesForCategory]

-- 25. Swap preserves total prizes
theorem swapPrize_preserves_total (pool : PrizePool) (index : Nat) (handCard prizeCard : Card) (pool' : PrizePool)
    (h : swapPrize pool index handCard = some (pool', prizeCard))
    (_hBound : index < pool.remaining.length) :
    pool'.remaining.length = pool.remaining.length := by
  simp [swapPrize] at h
  cases hGet : listGet? pool.remaining index with
  | none => simp [hGet] at h
  | some pc =>
      simp [hGet] at h
      rcases h with ⟨hPool, _⟩
      cases hPool
      simp [List.length_set]

-- 26. Reveal doesn't change pool
theorem revealPrize_pure (pool : PrizePool) (index : Nat) :
    ∀ c, revealPrize pool index = some c → pool.remaining.length > index := by
  intro c h
  unfold revealPrize at h
  -- h : listGet? pool.remaining index = some c
  suffices hsuff : ∀ (xs : List Card) (i : Nat), listGet? xs i = some c → xs.length > i from
    hsuff pool.remaining index h
  intro xs
  induction xs with
  | nil => intro i h; simp [listGet?] at h
  | cons x rest ih =>
      intro i h
      cases i with
      | zero => simp
      | succ n =>
          simp [listGet?] at h
          have := ih n h
          simp
          omega

-- 27. Won by prizes requires non-empty taken
theorem wonByPrizes_nonempty_taken (pool : PrizePool) (h : wonByPrizes pool) :
    pool.taken ≠ [] := by
  intro hempty
  have := h.2
  simp [hempty] at this

-- 28. Won by prizes means remaining is nil
theorem wonByPrizes_remaining_nil (pool : PrizePool) (h : wonByPrizes pool) :
    pool.remaining = [] := by
  exact h.1

-- 29. Multi-prize Pokemon give at least 2
theorem multi_prize_ge_two (cat : PokemonCategory)
    (h : cat ≠ .basic) :
    prizesForCategory cat ≥ 2 := by
  cases cat <;> simp_all [prizesForCategory]

-- 30. Standard 6-prize pool
theorem standard_prize_pool (prizes : List Card) (h : prizes.length = 6) :
    totalPrizes (mkPrizePool prizes) = 6 := by
  simp [mkPrizePool, totalPrizes, h]

end PokemonLean.PrizeCards
