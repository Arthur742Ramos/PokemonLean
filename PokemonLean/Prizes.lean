import PokemonLean.Basic

namespace PokemonLean.Prizes

open PokemonLean

inductive PrizeTier
  | single
  | double
  | triple
  deriving Repr, BEq, DecidableEq

def prizeTierValue : PrizeTier → Nat
  | .single => 1
  | .double => 2
  | .triple => 3

theorem prizeTierValue_pos (tier : PrizeTier) : prizeTierValue tier > 0 := by
  cases tier <;> decide

theorem prizeTierValue_le_three (tier : PrizeTier) : prizeTierValue tier ≤ 3 := by
  cases tier <;> decide

structure PrizeCard where
  card : Card
  tier : PrizeTier := .single
  deriving Repr, BEq, DecidableEq

def prizeCardValue (pc : PrizeCard) : Nat :=
  prizeTierValue pc.tier

def prizeCount (prizes : List PrizeCard) : Nat :=
  prizes.length

def prizeValueTotal (prizes : List PrizeCard) : Nat :=
  (prizes.map prizeCardValue).sum

theorem prizeCount_nil : prizeCount [] = 0 := by
  rfl

theorem prizeValueTotal_nil : prizeValueTotal [] = 0 := by
  rfl

theorem prizeValueTotal_cons (pc : PrizeCard) (rest : List PrizeCard) :
    prizeValueTotal (pc :: rest) = prizeCardValue pc + prizeValueTotal rest := by
  simp [prizeValueTotal]

theorem prizeValueTotal_nonneg (prizes : List PrizeCard) :
    0 ≤ prizeValueTotal prizes := by
  simp [prizeValueTotal]

theorem prizeValueTotal_ge_count (prizes : List PrizeCard) :
    prizeCount prizes ≤ prizeValueTotal prizes := by
  induction prizes with
  | nil => simp [prizeCount, prizeValueTotal]
  | cons pc rest ih =>
      have hPos : 1 ≤ prizeCardValue pc := by
        have ht : prizeTierValue pc.tier > 0 := prizeTierValue_pos pc.tier
        have : 1 ≤ prizeTierValue pc.tier := Nat.succ_le_of_lt ht
        simpa [prizeCardValue] using this
      have h1 : rest.length + 1 ≤ prizeValueTotal rest + 1 := Nat.succ_le_succ ih
      have h2 : prizeValueTotal rest + 1 ≤ prizeValueTotal rest + prizeCardValue pc :=
        Nat.add_le_add_left hPos _
      have h3 : rest.length + 1 ≤ prizeValueTotal rest + prizeCardValue pc := Nat.le_trans h1 h2
      -- rewrite the total for `pc :: rest`
      simpa [prizeCount, prizeValueTotal_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h3

theorem prizeValueTotal_le_three_mul (prizes : List PrizeCard) :
    prizeValueTotal prizes ≤ 3 * prizeCount prizes := by
  induction prizes with
  | nil => simp [prizeValueTotal, prizeCount]
  | cons pc rest ih =>
      have hpc : prizeCardValue pc ≤ 3 := by
        simpa [prizeCardValue] using prizeTierValue_le_three pc.tier
      calc
        prizeValueTotal (pc :: rest)
            = prizeCardValue pc + prizeValueTotal rest := by
                simp [prizeValueTotal]
        _ ≤ 3 + prizeValueTotal rest := by
                exact Nat.add_le_add_right hpc _
        _ ≤ 3 + (3 * prizeCount rest) := by
                exact Nat.add_le_add_left ih _
        _ = 3 * prizeCount (pc :: rest) := by
                simp [prizeCount, Nat.mul_add, Nat.add_comm]

def takePrizeCard (attacker defender : PlayerState) : PlayerState × PlayerState :=
  takePrize attacker defender

def takePrizeCards (attacker defender : PlayerState) : Nat → PlayerState × PlayerState
  | 0 => (attacker, defender)
  | n + 1 =>
      let (attacker', defender') := takePrize attacker defender
      takePrizeCards attacker' defender' n

theorem takePrizeCards_zero (attacker defender : PlayerState) :
    takePrizeCards attacker defender 0 = (attacker, defender) := by
  rfl

theorem takePrizeCards_succ (attacker defender : PlayerState) (n : Nat) :
    takePrizeCards attacker defender (n + 1) =
      let (attacker', defender') := takePrize attacker defender
      takePrizeCards attacker' defender' n := by
  rfl

theorem takePrizeCards_prizes_length_le (attacker defender : PlayerState) (n : Nat) :
    (takePrizeCards attacker defender n).2.prizes.length ≤ defender.prizes.length := by
  induction n generalizing attacker defender with
  | zero =>
      simp [takePrizeCards]
  | succ n ih =>
      cases hPrizes : defender.prizes with
      | nil =>
          -- `takePrize` is a no-op when defender has no prizes
          have hIH := ih (attacker := attacker) (defender := defender)
          simpa [takePrizeCards, takePrize, hPrizes] using hIH
      | cons prize rest =>
          -- one prize is removed, so the recursive bound strengthens to the original bound
          have hRec :
              (takePrizeCards { attacker with hand := prize :: attacker.hand }
                    { defender with prizes := rest } n).2.prizes.length ≤ rest.length :=
            ih (attacker := { attacker with hand := prize :: attacker.hand })
               (defender := { defender with prizes := rest })
          have hRec' :
              (takePrizeCards { attacker with hand := prize :: attacker.hand }
                    { defender with prizes := rest } n).2.prizes.length ≤ rest.length + 1 :=
            Nat.le_trans hRec (Nat.le_succ _)
          simpa [takePrizeCards, takePrize, hPrizes] using hRec'

theorem takePrizeCards_attacker_prizes_eq (attacker defender : PlayerState) (n : Nat) :
    (takePrizeCards attacker defender n).1.prizes = attacker.prizes := by
  induction n generalizing attacker defender with
  | zero =>
      simp [takePrizeCards]
  | succ n ih =>
      cases hPrizes : defender.prizes with
      | nil =>
          simp [takePrizeCards, takePrize, hPrizes, ih]
      | cons prize rest =>
          simp [takePrizeCards, takePrize, hPrizes, ih]

theorem takePrizeCards_bench_eq (attacker defender : PlayerState) (n : Nat) :
    (takePrizeCards attacker defender n).1.bench = attacker.bench ∧
      (takePrizeCards attacker defender n).2.bench = defender.bench := by
  induction n generalizing attacker defender with
  | zero =>
      simp [takePrizeCards]
  | succ n ih =>
      cases hPrizes : defender.prizes with
      | nil =>
          simp [takePrizeCards, takePrize, hPrizes, ih]
      | cons prize rest =>
          simp [takePrizeCards, takePrize, hPrizes, ih]

theorem takePrizeCards_total_cards (attacker defender : PlayerState) (n : Nat) :
    playerCardCount (takePrizeCards attacker defender n).1 +
      playerCardCount (takePrizeCards attacker defender n).2 =
      playerCardCount attacker + playerCardCount defender := by
  induction n generalizing attacker defender with
  | zero =>
      simp [takePrizeCards]
  | succ n ih =>
      cases hPrizes : defender.prizes with
      | nil =>
          -- `takePrize` is a no-op
          have hIH := ih (attacker := attacker) (defender := defender)
          simpa [takePrizeCards, takePrize, hPrizes] using hIH
      | cons prize rest =>
          let attacker' : PlayerState := { attacker with hand := prize :: attacker.hand }
          let defender' : PlayerState := { defender with prizes := rest }
          have hIH := ih (attacker := attacker') (defender := defender')
          have hTake' : playerCardCount attacker' + playerCardCount defender' =
              playerCardCount attacker + playerCardCount defender := by
            -- specialize the one-step conservation lemma
            simpa [attacker', defender', takePrize, hPrizes] using (takePrize_preserves_total_cards attacker defender)
          -- unfold one step and chain equalities
          simpa [takePrizeCards, attacker', defender', takePrize, hPrizes] using
            (Eq.trans hIH hTake')

def takePrizeTier (attacker defender : PlayerState) (tier : PrizeTier) : PlayerState × PlayerState :=
  takePrizeCards attacker defender (prizeTierValue tier)

theorem takePrizeTier_prizes_length_le (attacker defender : PlayerState) (tier : PrizeTier) :
    (takePrizeTier attacker defender tier).2.prizes.length ≤ defender.prizes.length := by
  exact takePrizeCards_prizes_length_le attacker defender (prizeTierValue tier)

theorem takePrizeTier_attacker_prizes_eq (attacker defender : PlayerState) (tier : PrizeTier) :
    (takePrizeTier attacker defender tier).1.prizes = attacker.prizes := by
  exact takePrizeCards_attacker_prizes_eq attacker defender (prizeTierValue tier)

def prizesRemaining (state : GameState) (player : PlayerId) : Nat :=
  (getPlayerState state player).prizes.length

def opponentPrizes (state : GameState) (player : PlayerId) : Nat :=
  (getPlayerState state (otherPlayer player)).prizes.length

def prizesEmpty (state : GameState) (player : PlayerId) : Prop :=
  opponentPrizes state player = 0

theorem prizesEmpty_iff (state : GameState) (player : PlayerId) :
    prizesEmpty state player ↔ (getPlayerState state (otherPlayer player)).prizes = [] := by
  cases h : (getPlayerState state (otherPlayer player)).prizes with
  | nil =>
      simp [prizesEmpty, opponentPrizes, h]
  | cons prize rest =>
      simp [prizesEmpty, opponentPrizes, h]

def prizeWin (state : GameState) (player : PlayerId) : Prop :=
  (getPlayerState state (otherPlayer player)).prizes = []

theorem prizeWin_iff (state : GameState) (player : PlayerId) :
    prizeWin state player ↔ prizesEmpty state player := by
  unfold prizeWin prizesEmpty opponentPrizes
  cases h : (getPlayerState state (otherPlayer player)).prizes with
  | nil =>
      simp
  | cons prize rest =>
      simp

theorem prizeWin_implies_hasWon (state : GameState) (player : PlayerId) :
    prizeWin state player → hasWon state player := by
  intro hWin
  unfold prizeWin at hWin
  unfold hasWon
  -- opponent prizes are empty, so length is 0
  simp [hWin]

def knockoutWin (state : GameState) (player : PlayerId) : Prop :=
  (getPlayerState state (otherPlayer player)).active = none

theorem knockoutWin_iff (state : GameState) (player : PlayerId) :
    knockoutWin state player ↔ (getPlayerState state (otherPlayer player)).active = none := by
  unfold knockoutWin
  rfl

def deckOutWin (state : GameState) (player : PlayerId) : Prop :=
  (getPlayerState state (otherPlayer player)).deck = []

theorem deckOutWin_iff (state : GameState) (player : PlayerId) :
    deckOutWin state player ↔ (getPlayerState state (otherPlayer player)).deck = [] := by
  unfold deckOutWin
  rfl

inductive WinReason
  | prizes
  | knockout
  | deckOut
  deriving Repr, BEq, DecidableEq

def hasWonBy (state : GameState) (player : PlayerId) : WinReason → Prop
  | .prizes => prizeWin state player
  | .knockout => knockoutWin state player
  | .deckOut => deckOutWin state player

def hasWonExtended (state : GameState) (player : PlayerId) : Prop :=
  ∃ reason, hasWonBy state player reason

theorem hasWonExtended_of_prizes (state : GameState) (player : PlayerId) :
    prizeWin state player → hasWonExtended state player := by
  intro h
  exact ⟨.prizes, h⟩

theorem hasWonExtended_of_knockout (state : GameState) (player : PlayerId) :
    knockoutWin state player → hasWonExtended state player := by
  intro h
  exact ⟨.knockout, h⟩

theorem hasWonExtended_of_deckOut (state : GameState) (player : PlayerId) :
    deckOutWin state player → hasWonExtended state player := by
  intro h
  exact ⟨.deckOut, h⟩

theorem hasWonExtended_cases (state : GameState) (player : PlayerId) :
    hasWonExtended state player →
      prizeWin state player ∨ knockoutWin state player ∨ deckOutWin state player := by
  intro h
  rcases h with ⟨reason, hReason⟩
  cases reason with
  | prizes => exact Or.inl hReason
  | knockout => exact Or.inr (Or.inl hReason)
  | deckOut => exact Or.inr (Or.inr hReason)

def winByEither (state : GameState) (player : PlayerId) : Prop :=
  prizeWin state player ∨ knockoutWin state player

theorem winByEither_implies_hasWonExtended (state : GameState) (player : PlayerId) :
    winByEither state player → hasWonExtended state player := by
  intro h
  cases h with
  | inl hPrize =>
      exact hasWonExtended_of_prizes state player hPrize
  | inr hKO =>
      exact hasWonExtended_of_knockout state player hKO

def prizeProgress (state : GameState) (player : PlayerId) : Nat :=
  standardPrizeCount - (getPlayerState state (otherPlayer player)).prizes.length

theorem prizeProgress_le_standard (state : GameState) (player : PlayerId) :
    prizeProgress state player ≤ standardPrizeCount := by
  simp [prizeProgress]

theorem prizeProgress_zero_iff (state : GameState) (player : PlayerId) :
    prizeProgress state player = 0 ↔
      standardPrizeCount ≤ (getPlayerState state (otherPlayer player)).prizes.length := by
  unfold prizeProgress
  exact Nat.sub_eq_zero_iff_le

def prizeDelta (before after : GameState) (player : PlayerId) : Int :=
  Int.ofNat (prizeProgress after player) - Int.ofNat (prizeProgress before player)

theorem prizeDelta_self (state : GameState) (player : PlayerId) :
    prizeDelta state state player = 0 := by
  simp [prizeDelta]

theorem prizeDelta_nonneg_of_progress (before after : GameState) (player : PlayerId)
    (h : prizeProgress before player ≤ prizeProgress after player) :
    0 ≤ prizeDelta before after player := by
  unfold prizeDelta
  have hNat : (Int.ofNat (prizeProgress before player)) ≤
      (Int.ofNat (prizeProgress after player)) := by
    exact Int.ofNat_le.mpr h
  simpa using (Int.sub_nonneg.mpr hNat)

theorem prizeProgress_zero_of_full (state : GameState) (player : PlayerId)
    (h : (getPlayerState state (otherPlayer player)).prizes.length = standardPrizeCount) :
    prizeProgress state player = 0 := by
  unfold prizeProgress
  simp [h]

end PokemonLean.Prizes
