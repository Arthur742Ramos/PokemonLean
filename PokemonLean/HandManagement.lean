import PokemonLean.Basic

namespace PokemonLean.HandManagement

open PokemonLean

def drawPhaseCount : Nat := 1

def professorsResearchCount : Nat := 7

def marnieSelfCount : Nat := 5

def marnieOpponentCount : Nat := 4

def handSize (player : PlayerState) : Nat :=
  player.hand.length

def drawCards (player : PlayerState) (count : Nat) : Option PlayerState :=
  if count ≤ player.deck.length then
    some { player with
      deck := player.deck.drop count
      hand := player.hand ++ player.deck.take count }
  else
    none


theorem drawCards_zero (player : PlayerState) :
    drawCards player 0 = some player := by
  simp [drawCards]

theorem drawCards_none_of_gt (player : PlayerState) (count : Nat)
    (h : player.deck.length < count) :
    drawCards player count = none := by
  unfold drawCards
  have h' : ¬ count ≤ player.deck.length := Nat.not_le_of_gt h
  simp [h']

theorem drawCards_some_of_le (player : PlayerState) (count : Nat)
    (h : count ≤ player.deck.length) :
    drawCards player count =
      some { player with
        deck := player.deck.drop count
        hand := player.hand ++ player.deck.take count } := by
  simp [drawCards, h]

theorem drawCards_hand_length (player player' : PlayerState) (count : Nat)
    (h : drawCards player count = some player') :
    player'.hand.length = player.hand.length + count := by
  by_cases hLe : count ≤ player.deck.length
  · simp [drawCards, hLe] at h
    cases h
    simp [List.length_take, Nat.min_eq_left hLe, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · simp [drawCards, hLe] at h

theorem drawCards_deck_length (player player' : PlayerState) (count : Nat)
    (h : drawCards player count = some player') :
    player'.deck.length + count = player.deck.length := by
  by_cases hLe : count ≤ player.deck.length
  · simp [drawCards, hLe] at h
    cases h
    simp [List.length_drop, Nat.sub_add_cancel hLe]
  · simp [drawCards, hLe] at h

theorem drawCards_preserves_discard (player player' : PlayerState) (count : Nat)
    (h : drawCards player count = some player') :
    player'.discard = player.discard := by
  by_cases hLe : count ≤ player.deck.length
  · simp [drawCards, hLe] at h
    cases h
    rfl
  · simp [drawCards, hLe] at h

theorem drawCards_preserves_prizes (player player' : PlayerState) (count : Nat)
    (h : drawCards player count = some player') :
    player'.prizes = player.prizes := by
  by_cases hLe : count ≤ player.deck.length
  · simp [drawCards, hLe] at h
    cases h
    rfl
  · simp [drawCards, hLe] at h

def drawPhase (player : PlayerState) : Option PlayerState :=
  drawCards player drawPhaseCount


theorem drawPhase_none_of_empty_deck (player : PlayerState)
    (h : player.deck = []) :
    drawPhase player = none := by
  simp [drawPhase, drawCards, drawPhaseCount, h]

theorem drawPhase_some_of_deck_length_pos (player : PlayerState)
    (h : 0 < player.deck.length) :
    ∃ player', drawPhase player = some player' := by
  refine ⟨{ player with
    deck := player.deck.drop drawPhaseCount
    hand := player.hand ++ player.deck.take drawPhaseCount }, ?_⟩
  have hLe : drawPhaseCount ≤ player.deck.length := by
    simpa [drawPhaseCount] using Nat.succ_le_of_lt h
  simp [drawPhase, drawCards, hLe]

theorem drawPhase_hand_length (player player' : PlayerState)
    (h : drawPhase player = some player') :
    player'.hand.length = player.hand.length + drawPhaseCount := by
  exact drawCards_hand_length player player' drawPhaseCount (by simpa [drawPhase] using h)

theorem drawPhase_deck_length (player player' : PlayerState)
    (h : drawPhase player = some player') :
    player'.deck.length + drawPhaseCount = player.deck.length := by
  exact drawCards_deck_length player player' drawPhaseCount (by simpa [drawPhase] using h)

def professorsResearch (player : PlayerState) : Option PlayerState :=
  if professorsResearchCount ≤ player.deck.length then
    some { player with
      deck := player.deck.drop professorsResearchCount
      hand := player.deck.take professorsResearchCount
      discard := player.hand ++ player.discard }
  else
    none

theorem professorsResearch_none_of_short_deck (player : PlayerState)
    (h : player.deck.length < professorsResearchCount) :
    professorsResearch player = none := by
  unfold professorsResearch
  have h' : ¬ professorsResearchCount ≤ player.deck.length := Nat.not_le_of_gt h
  simp [h']

theorem professorsResearch_some_of_sufficient_deck (player : PlayerState)
    (h : professorsResearchCount ≤ player.deck.length) :
    professorsResearch player =
      some { player with
        deck := player.deck.drop professorsResearchCount
        hand := player.deck.take professorsResearchCount
        discard := player.hand ++ player.discard } := by
  simp [professorsResearch, h]

theorem professorsResearch_hand_eq (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.hand = player.deck.take professorsResearchCount := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    rfl
  · simp [professorsResearch, hLe] at h

theorem professorsResearch_discard_eq (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.discard = player.hand ++ player.discard := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    rfl
  · simp [professorsResearch, hLe] at h

theorem professorsResearch_hand_length (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.hand.length = professorsResearchCount := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    simp [List.length_take, Nat.min_eq_left hLe]
  · simp [professorsResearch, hLe] at h

theorem professorsResearch_deck_length (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.deck.length + professorsResearchCount = player.deck.length := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    simp [List.length_drop, Nat.sub_add_cancel hLe]
  · simp [professorsResearch, hLe] at h

theorem professorsResearch_preserves_active (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.active = player.active := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    rfl
  · simp [professorsResearch, hLe] at h

theorem professorsResearch_preserves_bench (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.bench = player.bench := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    rfl
  · simp [professorsResearch, hLe] at h

theorem professorsResearch_preserves_prizes (player player' : PlayerState)
    (h : professorsResearch player = some player') :
    player'.prizes = player.prizes := by
  by_cases hLe : professorsResearchCount ≤ player.deck.length
  · simp [professorsResearch, hLe] at h
    cases h
    rfl
  · simp [professorsResearch, hLe] at h

def putHandOnBottom (player : PlayerState) : PlayerState :=
  { player with
    deck := player.deck ++ player.hand
    hand := [] }


theorem putHandOnBottom_deck_length (player : PlayerState) :
    (putHandOnBottom player).deck.length = player.deck.length + player.hand.length := by
  simp [putHandOnBottom]


def marnieBottomOpponentHand (opponent : PlayerState) : PlayerState :=
  putHandOnBottom opponent


def marnieSelf (player : PlayerState) : Option PlayerState :=
  drawCards (putHandOnBottom player) marnieSelfCount

def marnieOpponent (player : PlayerState) : Option PlayerState :=
  drawCards (marnieBottomOpponentHand player) marnieOpponentCount

def playMarnie (current opponent : PlayerState) : Option (PlayerState × PlayerState) :=
  match marnieSelf current, marnieOpponent opponent with
  | some current', some opponent' => some (current', opponent')
  | _, _ => none

theorem marnieSelf_none_of_short_deck (player : PlayerState)
    (h : (putHandOnBottom player).deck.length < marnieSelfCount) :
    marnieSelf player = none := by
  exact drawCards_none_of_gt (putHandOnBottom player) marnieSelfCount h

theorem marnieOpponent_none_of_short_deck (player : PlayerState)
    (h : (marnieBottomOpponentHand player).deck.length < marnieOpponentCount) :
    marnieOpponent player = none := by
  exact drawCards_none_of_gt (marnieBottomOpponentHand player) marnieOpponentCount h

theorem marnieSelf_hand_length (player player' : PlayerState)
    (h : marnieSelf player = some player') :
    player'.hand.length = marnieSelfCount := by
  have hDraw :
      player'.hand.length =
        (putHandOnBottom player).hand.length + marnieSelfCount :=
    drawCards_hand_length (putHandOnBottom player) player' marnieSelfCount (by simpa [marnieSelf] using h)
  simpa [putHandOnBottom] using hDraw

theorem marnieOpponent_hand_length (player player' : PlayerState)
    (h : marnieOpponent player = some player') :
    player'.hand.length = marnieOpponentCount := by
  have hDraw :
      player'.hand.length =
        (marnieBottomOpponentHand player).hand.length + marnieOpponentCount :=
    drawCards_hand_length (marnieBottomOpponentHand player) player' marnieOpponentCount
      (by simpa [marnieOpponent] using h)
  simpa [marnieBottomOpponentHand, putHandOnBottom] using hDraw

theorem playMarnie_some_of_some (current opponent current' opponent' : PlayerState)
    (hCurrent : marnieSelf current = some current')
    (hOpponent : marnieOpponent opponent = some opponent') :
    playMarnie current opponent = some (current', opponent') := by
  simp [playMarnie, hCurrent, hOpponent]

theorem playMarnie_none_left (current opponent : PlayerState)
    (hCurrent : marnieSelf current = none) :
    playMarnie current opponent = none := by
  cases hOpponent : marnieOpponent opponent <;> simp [playMarnie, hCurrent, hOpponent]

theorem playMarnie_none_right (current opponent current' : PlayerState)
    (hCurrent : marnieSelf current = some current')
    (hOpponent : marnieOpponent opponent = none) :
    playMarnie current opponent = none := by
  simp [playMarnie, hCurrent, hOpponent]

def nDrawCount (player : PlayerState) : Nat :=
  player.prizes.length

def nSingle (player : PlayerState) : Option PlayerState :=
  drawCards (putHandOnBottom player) (nDrawCount player)

def playN (current opponent : PlayerState) : Option (PlayerState × PlayerState) :=
  match nSingle current, nSingle opponent with
  | some current', some opponent' => some (current', opponent')
  | _, _ => none


theorem nSingle_hand_length (player player' : PlayerState)
    (h : nSingle player = some player') :
    player'.hand.length = player.prizes.length := by
  have hDraw :
      player'.hand.length =
        (putHandOnBottom player).hand.length + nDrawCount player :=
    drawCards_hand_length (putHandOnBottom player) player' (nDrawCount player)
      (by simpa [nSingle] using h)
  simpa [putHandOnBottom, nDrawCount] using hDraw

theorem playN_some_of_some (current opponent current' opponent' : PlayerState)
    (hCurrent : nSingle current = some current')
    (hOpponent : nSingle opponent = some opponent') :
    playN current opponent = some (current', opponent') := by
  simp [playN, hCurrent, hOpponent]

theorem playN_none_left (current opponent : PlayerState)
    (hCurrent : nSingle current = none) :
    playN current opponent = none := by
  cases hOpponent : nSingle opponent <;> simp [playN, hCurrent, hOpponent]

theorem playN_none_right (current opponent current' : PlayerState)
    (hCurrent : nSingle current = some current')
    (hOpponent : nSingle opponent = none) :
    playN current opponent = none := by
  simp [playN, hCurrent, hOpponent]

def judge (current opponent : PlayerState) (count : Nat) : Option (PlayerState × PlayerState) :=
  match drawCards (putHandOnBottom current) count, drawCards (putHandOnBottom opponent) count with
  | some current', some opponent' => some (current', opponent')
  | _, _ => none

inductive HandDisruptionEffect
  | professorsResearch
  | marnie
  | n
  | judge (count : Nat)
  | opponentHandBottom
  deriving Repr, BEq, DecidableEq

def applyHandDisruption (current opponent : PlayerState) :
    HandDisruptionEffect → Option (PlayerState × PlayerState)
  | .professorsResearch =>
      match professorsResearch current with
      | some current' => some (current', opponent)
      | none => none
  | .marnie => playMarnie current opponent
  | .n => playN current opponent
  | .judge count => judge current opponent count
  | .opponentHandBottom => some (current, putHandOnBottom opponent)


def discardTwo (hand : List Card) (first second : Card) : Option (List Card × List Card) :=
  match removeFirst first hand with
  | none => none
  | some hand' =>
      match removeFirst second hand' with
      | none => none
      | some hand'' => some (hand'', [first, second])

theorem discardTwo_discarded_cards (hand : List Card) (first second : Card) (rest discarded : List Card)
    (h : discardTwo hand first second = some (rest, discarded)) :
    discarded = [first, second] := by
  unfold discardTwo at h
  cases hFirst : removeFirst first hand with
  | none =>
      simp [hFirst] at h
  | some hand' =>
      cases hSecond : removeFirst second hand' with
      | none =>
          simp [hFirst, hSecond] at h
      | some hand2 =>
          simp [hFirst, hSecond] at h
          rcases h with ⟨hRest, hDiscarded⟩
          cases hRest
          exact hDiscarded.symm

theorem discardTwo_length (hand : List Card) (first second : Card) (rest discarded : List Card)
    (h : discardTwo hand first second = some (rest, discarded)) :
    rest.length + 2 = hand.length := by
  unfold discardTwo at h
  cases hFirst : removeFirst first hand with
  | none =>
      simp [hFirst] at h
  | some hand' =>
      cases hSecond : removeFirst second hand' with
      | none =>
          simp [hFirst, hSecond] at h
      | some handTail =>
          simp [hFirst, hSecond] at h
          rcases h with ⟨hRest, _⟩
          cases hRest
          have hLenFirst : hand'.length + 1 = hand.length :=
            removeFirst_length first hand hand' hFirst
          have hLenSecond : rest.length + 1 = hand'.length :=
            removeFirst_length second hand' rest hSecond
          omega

def payDiscardTwo (player : PlayerState) (first second : Card) : Option PlayerState :=
  match discardTwo player.hand first second with
  | none => none
  | some (newHand, discarded) =>
      some { player with
        hand := newHand
        discard := discarded ++ player.discard }

theorem payDiscardTwo_hand_length (player player' : PlayerState) (first second : Card)
    (h : payDiscardTwo player first second = some player') :
    player'.hand.length + 2 = player.hand.length := by
  unfold payDiscardTwo at h
  cases hDiscard : discardTwo player.hand first second with
  | none =>
      simp [hDiscard] at h
  | some pair =>
      rcases pair with ⟨newHand, discarded⟩
      simp [hDiscard] at h
      cases h
      exact discardTwo_length player.hand first second newHand discarded hDiscard

theorem payDiscardTwo_preserves_deck (player player' : PlayerState) (first second : Card)
    (h : payDiscardTwo player first second = some player') :
    player'.deck = player.deck := by
  unfold payDiscardTwo at h
  cases hDiscard : discardTwo player.hand first second with
  | none =>
      simp [hDiscard] at h
  | some pair =>
      simp [hDiscard] at h
      cases h
      rfl

theorem payDiscardTwo_discard_growth (player player' : PlayerState) (first second : Card)
    (h : payDiscardTwo player first second = some player') :
    player'.discard.length = player.discard.length + 2 := by
  unfold payDiscardTwo at h
  cases hDiscard : discardTwo player.hand first second with
  | none =>
      simp [hDiscard] at h
  | some pair =>
      rcases pair with ⟨newHand, discarded⟩
      simp [hDiscard] at h
      cases h
      have hCards : discarded = [first, second] :=
        discardTwo_discarded_cards player.hand first second newHand discarded hDiscard
      simp [hCards, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end PokemonLean.HandManagement
