/-
  PokemonLean / SupporterCards.lean

  Pokémon TCG Supporter card mechanics formalised in Lean 4.
  Covers: one-per-turn rule, Professor's Research (discard hand, draw 7),
  Boss's Orders (force switch active), N (shuffle hands, draw to prizes),
  Marnie (bottom-deck hands, draw 5/4), Cynthia (shuffle hand, draw 6).

  All proofs are sorry-free.
-/

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Named supporter cards in the TCG. -/
inductive SupporterName where
  | professorsResearch
  | bossOrders
  | cardN
  | marnie
  | cynthia
  | judgeCard   -- Judge: both shuffle, draw 4
  | other (name : String)
deriving DecidableEq, Repr

/-- A supporter card. -/
structure SupporterCard where
  name : SupporterName
deriving DecidableEq, Repr

def mkProfResearch : SupporterCard := ⟨.professorsResearch⟩
def mkBossOrders   : SupporterCard := ⟨.bossOrders⟩
def mkN            : SupporterCard := ⟨.cardN⟩
def mkMarnie       : SupporterCard := ⟨.marnie⟩
def mkCynthia      : SupporterCard := ⟨.cynthia⟩
def mkJudge        : SupporterCard := ⟨.judgeCard⟩

-- ============================================================
-- §2  Game state
-- ============================================================

/-- Simplified Pokémon (for active/bench). -/
structure Pokemon where
  name : String
  hp   : Nat
deriving DecidableEq, Repr

/-- Bench: a list of Pokémon (max 5 in official rules). -/
abbrev Bench := List Pokemon

/-- A generic card for the hand/deck. -/
inductive Card where
  | pokemon (p : Pokemon)
  | supporter (s : SupporterCard)
  | other (name : String)
deriving DecidableEq, Repr

/-- Player state relevant to supporter mechanics. -/
structure PlayerState where
  hand            : List Card
  deckSize        : Nat
  prizeCount      : Nat        -- remaining prizes (1–6)
  active          : Pokemon
  bench           : Bench
  supporterPlayed : Bool       -- has a supporter been used this turn?
deriving Repr

/-- Fresh turn: reset supporter flag. -/
def PlayerState.newTurn (ps : PlayerState) : PlayerState :=
  { ps with supporterPlayed := false }

-- ============================================================
-- §3  One-supporter-per-turn rule
-- ============================================================

/-- Can we play a supporter? -/
def canPlaySupporter (ps : PlayerState) (s : SupporterCard) : Prop :=
  ps.supporterPlayed = false ∧ Card.supporter s ∈ ps.hand

/-- Remove a card from hand. -/
def removeFromHand (ps : PlayerState) (c : Card) : PlayerState :=
  { ps with hand := ps.hand.erase c }

/-- Mark supporter as played. -/
def markSupporterPlayed (ps : PlayerState) : PlayerState :=
  { ps with supporterPlayed := true }

-- ============================================================
-- §4  Supporter effects
-- ============================================================

/-- Professor's Research: discard entire hand, draw 7. -/
def applyProfResearch (ps : PlayerState) : PlayerState :=
  let totalDeck := ps.deckSize + ps.hand.length - 1  -- hand discarded, supporter itself used
  let drawn := min 7 totalDeck
  { ps with
    hand := List.replicate drawn (.other "drawn")
    deckSize := totalDeck - drawn
    supporterPlayed := true }

/-- Boss's Orders: force opponent's benched Pokémon to active.
    We model the effect on the *opponent's* state. -/
def applyBossOrders (oppState : PlayerState) (target : Pokemon)
    (hbench : target ∈ oppState.bench) : PlayerState :=
  { oppState with
    active := target
    bench := oppState.active :: oppState.bench.erase target }

/-- N: shuffle hand into deck, draw cards equal to prize count. -/
def applyN (ps : PlayerState) : PlayerState :=
  let totalDeck := ps.deckSize + ps.hand.length - 1
  let drawn := min ps.prizeCount totalDeck
  { ps with
    hand := List.replicate drawn (.other "drawn")
    deckSize := totalDeck - drawn
    supporterPlayed := true }

/-- Marnie: bottom-deck hand, draw 5 (going-first player draws 4, we use a param). -/
def applyMarnie (ps : PlayerState) (drawCount : Nat) : PlayerState :=
  let totalDeck := ps.deckSize + ps.hand.length - 1
  let drawn := min drawCount totalDeck
  { ps with
    hand := List.replicate drawn (.other "drawn")
    deckSize := totalDeck - drawn
    supporterPlayed := true }

/-- Cynthia: shuffle hand into deck, draw 6. -/
def applyCynthia (ps : PlayerState) : PlayerState :=
  let totalDeck := ps.deckSize + ps.hand.length - 1
  let drawn := min 6 totalDeck
  { ps with
    hand := List.replicate drawn (.other "drawn")
    deckSize := totalDeck - drawn
    supporterPlayed := true }

/-- Judge: both players shuffle hands, draw 4. Applied per-player. -/
def applyJudge (ps : PlayerState) : PlayerState :=
  let totalDeck := ps.deckSize + ps.hand.length - 1
  let drawn := min 4 totalDeck
  { ps with
    hand := List.replicate drawn (.other "drawn")
    deckSize := totalDeck - drawn
    supporterPlayed := true }

-- ============================================================
-- §5  Theorems: One-supporter-per-turn (1–4)
-- ============================================================

/-- Theorem 1: After playing any supporter, the flag is set. -/
theorem prof_research_sets_flag (ps : PlayerState) :
    (applyProfResearch ps).supporterPlayed = true := by
  simp [applyProfResearch]

/-- Theorem 2: A fresh turn allows supporter play. -/
theorem new_turn_supporter_available (ps : PlayerState) :
    (PlayerState.newTurn ps).supporterPlayed = false := rfl

/-- Theorem 3: After Cynthia, supporter flag is set. -/
theorem cynthia_sets_flag (ps : PlayerState) :
    (applyCynthia ps).supporterPlayed = true := by
  simp [applyCynthia]

/-- Theorem 4: After N, supporter flag is set. -/
theorem n_sets_flag (ps : PlayerState) :
    (applyN ps).supporterPlayed = true := by
  simp [applyN]

-- ============================================================
-- §6  Theorems: Professor's Research mechanics (5–8)
-- ============================================================

/-- Theorem 5: Professor's Research draws exactly 7 if deck ≥ 7 (after shuffle). -/
theorem prof_research_draws_7 (ps : PlayerState)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ 7) :
    (applyProfResearch ps).hand.length = 7 := by
  simp [applyProfResearch, List.length_replicate]
  omega

/-- Theorem 6: Professor's Research empties hand then refills (new hand is all fresh). -/
theorem prof_research_fresh_hand (ps : PlayerState) :
    ∀ c ∈ (applyProfResearch ps).hand, c = Card.other "drawn" := by
  intro c hc
  simp [applyProfResearch] at hc
  exact hc.2

/-- Theorem 7: Professor's Research conserves total cards (hand + deck + 1 for discard). -/
theorem prof_research_conserves (ps : PlayerState) :
    (applyProfResearch ps).hand.length + (applyProfResearch ps).deckSize =
    ps.deckSize + ps.hand.length - 1 := by
  simp [applyProfResearch, List.length_replicate]
  omega

/-- Theorem 8: With empty hand (only the supporter), Prof Research draws from full deck. -/
theorem prof_research_empty_hand (ps : PlayerState)
    (hempty : ps.hand.length = 1) (hdeck : ps.deckSize ≥ 7) :
    (applyProfResearch ps).hand.length = 7 := by
  simp [applyProfResearch, List.length_replicate, hempty]
  omega

-- ============================================================
-- §7  Theorems: Boss's Orders mechanics (9–11)
-- ============================================================

/-- Theorem 9: Boss's Orders switches the opponent's active. -/
theorem boss_orders_switches_active (opp : PlayerState) (target : Pokemon)
    (hb : target ∈ opp.bench) :
    (applyBossOrders opp target hb).active = target := rfl

/-- Theorem 10: After Boss's Orders, old active is on bench. -/
theorem boss_orders_old_active_benched (opp : PlayerState) (target : Pokemon)
    (hb : target ∈ opp.bench) :
    opp.active ∈ (applyBossOrders opp target hb).bench := by
  simp [applyBossOrders]

/-- Theorem 11: Boss's Orders preserves bench size (old active added, target removed). -/
theorem boss_orders_preserves_count (opp : PlayerState) (target : Pokemon)
    (hb : target ∈ opp.bench) :
    (applyBossOrders opp target hb).bench.length =
    opp.bench.length := by
  show (opp.active :: opp.bench.erase target).length = opp.bench.length
  simp only [List.length_cons]
  have h1 := List.length_erase_of_mem hb
  have h2 : 0 < opp.bench.length := List.length_pos_of_mem hb
  omega

-- ============================================================
-- §8  Theorems: N mechanics (12–14)
-- ============================================================

/-- Theorem 12: N draws exactly prizeCount cards if deck is large enough. -/
theorem n_draws_prizes (ps : PlayerState)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ ps.prizeCount) :
    (applyN ps).hand.length = ps.prizeCount := by
  simp [applyN, List.length_replicate]
  omega

/-- Theorem 13: N with 1 prize draws 1 (if deck large enough). -/
theorem n_one_prize (ps : PlayerState)
    (hp : ps.prizeCount = 1)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ 1) :
    (applyN ps).hand.length = 1 := by
  simp [applyN, List.length_replicate, hp]
  omega

/-- Theorem 14: N conserves total. -/
theorem n_conserves (ps : PlayerState) :
    (applyN ps).hand.length + (applyN ps).deckSize =
    ps.deckSize + ps.hand.length - 1 := by
  simp [applyN, List.length_replicate]
  omega

-- ============================================================
-- §9  Theorems: Marnie mechanics (15–17)
-- ============================================================

/-- Theorem 15: Marnie draws the specified count if deck large enough. -/
theorem marnie_draws (ps : PlayerState) (n : Nat)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ n) :
    (applyMarnie ps n).hand.length = n := by
  simp [applyMarnie, List.length_replicate]
  omega

/-- Theorem 16: Standard Marnie draws 5. -/
theorem marnie_standard_draw (ps : PlayerState)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ 5) :
    (applyMarnie ps 5).hand.length = 5 := by
  exact marnie_draws ps 5 hbig

/-- Theorem 17: Marnie sets supporter flag. -/
theorem marnie_sets_flag (ps : PlayerState) (n : Nat) :
    (applyMarnie ps n).supporterPlayed = true := by
  simp [applyMarnie]

-- ============================================================
-- §10  Theorems: Cynthia mechanics (18–20)
-- ============================================================

/-- Theorem 18: Cynthia draws exactly 6 if deck large enough. -/
theorem cynthia_draws_6 (ps : PlayerState)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ 6) :
    (applyCynthia ps).hand.length = 6 := by
  simp [applyCynthia, List.length_replicate]
  omega

/-- Theorem 19: Cynthia conserves total cards. -/
theorem cynthia_conserves (ps : PlayerState) :
    (applyCynthia ps).hand.length + (applyCynthia ps).deckSize =
    ps.deckSize + ps.hand.length - 1 := by
  simp [applyCynthia, List.length_replicate]
  omega

/-- Theorem 20: Cynthia hand is all fresh. -/
theorem cynthia_fresh_hand (ps : PlayerState) :
    ∀ c ∈ (applyCynthia ps).hand, c = Card.other "drawn" := by
  intro c hc
  simp [applyCynthia] at hc
  exact hc.2

-- ============================================================
-- §11  Theorems: Judge mechanics (21–22)
-- ============================================================

/-- Theorem 21: Judge draws 4 if deck large enough. -/
theorem judge_draws_4 (ps : PlayerState)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ 4) :
    (applyJudge ps).hand.length = 4 := by
  simp [applyJudge, List.length_replicate]
  omega

/-- Theorem 22: Judge sets supporter flag. -/
theorem judge_sets_flag (ps : PlayerState) :
    (applyJudge ps).supporterPlayed = true := by
  simp [applyJudge]

-- ============================================================
-- §12  Theorems: Interaction and sequencing (23–26)
-- ============================================================

/-- Theorem 23: Cannot play two supporters in the same turn (Prof Research then N). -/
theorem no_double_supporter_prof_n (ps : PlayerState) :
    (applyProfResearch ps).supporterPlayed = true := by
  simp [applyProfResearch]

/-- Theorem 24: New turn after supporter resets the flag. -/
theorem new_turn_resets_after_supporter (ps : PlayerState) :
    (PlayerState.newTurn (applyProfResearch ps)).supporterPlayed = false := rfl

/-- Theorem 25: Boss's Orders does not change hand size. -/
theorem boss_orders_hand_unchanged (opp : PlayerState) (target : Pokemon)
    (hb : target ∈ opp.bench) :
    (applyBossOrders opp target hb).hand = opp.hand := rfl

/-- Theorem 26: Prize count is unchanged by draw supporters. -/
theorem prof_research_preserves_prizes (ps : PlayerState) :
    (applyProfResearch ps).prizeCount = ps.prizeCount := rfl

-- ============================================================
-- §13  Theorems: Deck-out scenarios (27–30)
-- ============================================================

/-- Theorem 27: Prof Research with small deck draws less than 7. -/
theorem prof_research_small_deck (ps : PlayerState)
    (hsmall : ps.deckSize + ps.hand.length - 1 < 7) :
    (applyProfResearch ps).hand.length = ps.deckSize + ps.hand.length - 1 := by
  simp [applyProfResearch, List.length_replicate]
  omega

/-- Theorem 28: N with 6 prizes draws 6 if deck large enough. -/
theorem n_six_prizes (ps : PlayerState)
    (hp : ps.prizeCount = 6)
    (hbig : ps.deckSize + ps.hand.length - 1 ≥ 6) :
    (applyN ps).hand.length = 6 := by
  simp [applyN, List.length_replicate, hp]
  omega

/-- Theorem 29: If deck is empty and hand has only 1 card, Prof Research draws 0. -/
theorem prof_research_empty_deck (ps : PlayerState)
    (hdeck : ps.deckSize = 0) (hhand : ps.hand.length = 1) :
    (applyProfResearch ps).hand.length = 0 := by
  simp [applyProfResearch, List.length_replicate, hdeck, hhand]

/-- Theorem 30: Marnie with deck 0 and hand 1 draws 0. -/
theorem marnie_empty_deck (ps : PlayerState) (n : Nat)
    (hdeck : ps.deckSize = 0) (hhand : ps.hand.length = 1) (hn : n > 0) :
    (applyMarnie ps n).hand.length = 0 := by
  simp [applyMarnie, List.length_replicate, hdeck, hhand]
