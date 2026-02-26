import PokemonLean.Basic

namespace PokemonLean.Decks

open PokemonLean

structure DeckRules where
  deckSize : Nat
  maxCopies : Nat
  minPokemon : Nat
  deriving Repr

def standardRules : DeckRules :=
  { deckSize := 60, maxCopies := 4, minPokemon := 1 }

def isPokemon (card : Card) : Bool :=
  !isTrainer card

def pokemonCount (deck : List Card) : Nat :=
  deck.countP isPokemon

def trainerCount (deck : List Card) : Nat :=
  deck.countP isTrainer

theorem pokemonCount_nil : pokemonCount [] = 0 := by
  simp [pokemonCount]

theorem trainerCount_nil : trainerCount [] = 0 := by
  simp [trainerCount]

theorem pokemonCount_cons (card : Card) (deck : List Card) :
    pokemonCount (card :: deck) =
      (if isPokemon card then 1 else 0) + pokemonCount deck := by
  -- `countP` is tail-recursive, so the cons-case is easy.
  simp [pokemonCount, List.countP_cons, Nat.add_comm]

theorem trainerCount_cons (card : Card) (deck : List Card) :
    trainerCount (card :: deck) =
      (if isTrainer card then 1 else 0) + trainerCount deck := by
  simp [trainerCount, List.countP_cons, Nat.add_comm]

theorem pokemonCount_le_length (deck : List Card) :
    pokemonCount deck ≤ deck.length := by
  simpa [pokemonCount] using (List.countP_le_length (p := isPokemon) (l := deck))

theorem trainerCount_le_length (deck : List Card) :
    trainerCount deck ≤ deck.length := by
  simpa [trainerCount] using (List.countP_le_length (p := isTrainer) (l := deck))

theorem pokemonCount_add_trainerCount (deck : List Card) :
    pokemonCount deck + trainerCount deck = deck.length := by
  -- `countP` splits the list into trainers vs non-trainers.
  have h := List.length_eq_countP_add_countP (p := isTrainer) (l := deck)
  -- `¬ isTrainer` is `isPokemon` by definition.
  -- Rearrange the resulting equality.
  have h' : trainerCount deck + pokemonCount deck = deck.length := by
    -- `length = countP isTrainer + countP (fun c => ¬isTrainer c)`
    simpa [trainerCount, pokemonCount, isPokemon, Nat.add_comm] using h.symm
  simpa [Nat.add_comm] using h'

theorem pokemonCount_zero_iff_all_trainers (deck : List Card) :
    pokemonCount deck = 0 ↔ (∀ card ∈ deck, isTrainer card = true) := by
  -- `countP p = 0` iff `p` is false everywhere.
  simp [pokemonCount, isPokemon]

theorem trainerCount_zero_iff_all_pokemon (deck : List Card) :
    trainerCount deck = 0 ↔ (∀ card ∈ deck, isTrainer card = false) := by
  simp [trainerCount]

def countCardName (name : String) (deck : List Card) : Nat :=
  deck.filter (fun c => c.name == name) |>.length

theorem countCardName_le_length (name : String) (deck : List Card) :
    countCardName name deck ≤ deck.length := by
  -- filtering cannot increase length
  simpa [countCardName] using (List.length_filter_le (l := deck) (p := fun c => c.name == name))

def deckHasPokemon (deck : List Card) : Prop :=
  pokemonCount deck > 0

def DeckValidity (rules : DeckRules) (deck : List Card) : Prop :=
  deck.length = rules.deckSize ∧
  (∀ card ∈ deck, countCardName card.name deck ≤ rules.maxCopies) ∧
  rules.minPokemon ≤ pokemonCount deck

theorem deckValidity_length (rules : DeckRules) (deck : List Card) :
    DeckValidity rules deck → deck.length = rules.deckSize := by
  intro h
  exact h.1

theorem deckValidity_minPokemon (rules : DeckRules) (deck : List Card) :
    DeckValidity rules deck → rules.minPokemon ≤ pokemonCount deck := by
  intro h
  exact h.2.2

def checkDeckValidity (rules : DeckRules) (deck : List Card) : Bool :=
  deck.length == rules.deckSize &&
  deck.all (fun card => decide (countCardName card.name deck ≤ rules.maxCopies)) &&
  decide (rules.minPokemon ≤ pokemonCount deck)

theorem checkDeckValidity_sound (rules : DeckRules) (deck : List Card) :
    checkDeckValidity rules deck = true → DeckValidity rules deck := by
  intro h
  unfold checkDeckValidity at h
  -- `checkDeckValidity` is `((a && b) && c)`; split the conjunctions without unfolding `pokemonCount`.
  have h₁ :
      (deck.length == rules.deckSize &&
          deck.all (fun card => decide (countCardName card.name deck ≤ rules.maxCopies))) = true ∧
        decide (rules.minPokemon ≤ pokemonCount deck) = true := by
    exact Eq.mp (Bool.and_eq_true _ _) h
  have hAB := h₁.1
  have hMinBool := h₁.2
  have h₂ :
      (deck.length == rules.deckSize) = true ∧
        deck.all (fun card => decide (countCardName card.name deck ≤ rules.maxCopies)) = true := by
    exact Eq.mp (Bool.and_eq_true _ _) hAB
  have hLenBool := h₂.1
  have hAllBool := h₂.2

  have hLen : deck.length = rules.deckSize := (beq_iff_eq).1 hLenBool
  have hAll : ∀ card ∈ deck, countCardName card.name deck ≤ rules.maxCopies := by
    intro card hMem
    have : decide (countCardName card.name deck ≤ rules.maxCopies) = true :=
      (List.all_eq_true).1 hAllBool card hMem
    exact of_decide_eq_true this
  have hMin : rules.minPokemon ≤ pokemonCount deck := of_decide_eq_true hMinBool

  exact ⟨hLen, hAll, hMin⟩

theorem checkDeckValidity_complete (rules : DeckRules) (deck : List Card)
    (h : DeckValidity rules deck) :
    checkDeckValidity rules deck = true := by
  rcases h with ⟨hLen, hAll, hMin⟩
  unfold checkDeckValidity

  have ha : (deck.length == rules.deckSize) = true := (beq_iff_eq).2 hLen
  have hb : deck.all (fun card => decide (countCardName card.name deck ≤ rules.maxCopies)) = true := by
    apply (List.all_eq_true).2
    intro card hMem
    exact decide_eq_true (hAll card hMem)
  have hc : decide (rules.minPokemon ≤ pokemonCount deck) = true := decide_eq_true hMin

  have hab :
      (deck.length == rules.deckSize &&
          deck.all (fun card => decide (countCardName card.name deck ≤ rules.maxCopies))) = true := by
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨ha, hb⟩

  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hab, hc⟩

def drawFromDeck (deck : List Card) (n : Nat) : Option (List Card × List Card) :=
  if n ≤ deck.length then
    some (deck.take n, deck.drop n)
  else
    none

theorem drawFromDeck_length (deck : List Card) (n : Nat) (drawn rest : List Card)
    (h : drawFromDeck deck n = some (drawn, rest)) :
    drawn.length = n ∧ rest.length + n = deck.length := by
  unfold drawFromDeck at h
  by_cases hLe : n ≤ deck.length
  · simp [hLe] at h
    rcases h with ⟨hTake, hDrop⟩
    -- substitute `drawn` and `rest`
    cases hTake.symm
    cases hDrop.symm
    constructor
    · simp [List.length_take, Nat.min_eq_left hLe]
    · simp [List.length_drop, Nat.sub_add_cancel hLe]
  · have : False := by
      simp [hLe] at h
    exact False.elim this

theorem drawFromDeck_none_of_gt (deck : List Card) (n : Nat)
    (h : deck.length < n) :
    drawFromDeck deck n = none := by
  unfold drawFromDeck
  have h' : ¬ n ≤ deck.length := Nat.not_le_of_gt h
  simp [h']

def dealPrizes (deck : List Card) (count : Nat) : Option (List Card × List Card) :=
  drawFromDeck deck count

theorem dealPrizes_length (deck : List Card) (count : Nat) (prizes rest : List Card)
    (h : dealPrizes deck count = some (prizes, rest)) :
    prizes.length = count ∧ rest.length + count = deck.length := by
  exact drawFromDeck_length deck count prizes rest h

theorem dealPrizes_none_of_short_deck (deck : List Card) (count : Nat)
    (h : deck.length < count) :
    dealPrizes deck count = none := by
  exact drawFromDeck_none_of_gt deck count h

def openingHandSize : Nat := 7

def drawOpeningHand (deck : List Card) : Option (List Card × List Card) :=
  drawFromDeck deck openingHandSize

theorem drawOpeningHand_length (deck : List Card) (hand rest : List Card)
    (h : drawOpeningHand deck = some (hand, rest)) :
    hand.length = openingHandSize ∧ rest.length + openingHandSize = deck.length := by
  exact drawFromDeck_length deck openingHandSize hand rest h

def setupPlayer (deck : List Card) : Option (PlayerState × List Card) :=
  match drawOpeningHand deck with
  | none => none
  | some (hand, rest) =>
      some ({ deck := rest, hand := hand, bench := [], active := none, discard := [], prizes := [] }, rest)

theorem setupPlayer_hand_length (deck : List Card) (player : PlayerState) (rest : List Card)
    (h : setupPlayer deck = some (player, rest)) :
    player.hand.length = openingHandSize := by
  unfold setupPlayer at h
  cases hDraw : drawOpeningHand deck with
  | none =>
      simp [hDraw] at h
  | some pair =>
      rcases pair with ⟨hand, remaining⟩
      simp [hDraw] at h
      rcases h with ⟨hPlayer, hRest⟩
      subst hPlayer
      subst hRest
      have hLen := drawOpeningHand_length deck hand remaining hDraw
      simpa using hLen.1

def addPrizesToPlayer (player : PlayerState) (prizes : List Card) : PlayerState :=
  { player with prizes := prizes }


def setupPrizes (player : PlayerState) (count : Nat) : Option PlayerState :=
  match dealPrizes player.deck count with
  | none => none
  | some (prizes, rest) =>
      some { player with deck := rest, prizes := prizes }

theorem setupPrizes_length (player : PlayerState) (count : Nat) (player' : PlayerState)
    (h : setupPrizes player count = some player') :
    player'.prizes.length = count := by
  unfold setupPrizes at h
  cases hDeal : dealPrizes player.deck count with
  | none => simp [hDeal] at h
  | some pair =>
      cases pair with
      | mk prizes rest =>
          simp [hDeal] at h
          cases h
          have hLen := dealPrizes_length player.deck count prizes rest hDeal
          exact hLen.1

def standardPrizeSetup (player : PlayerState) : Option PlayerState :=
  setupPrizes player standardPrizeCount

theorem standardPrizeSetup_length (player : PlayerState) (player' : PlayerState)
    (h : standardPrizeSetup player = some player') :
    player'.prizes.length = standardPrizeCount := by
  unfold standardPrizeSetup at h
  exact setupPrizes_length player standardPrizeCount player' h

end PokemonLean.Decks
