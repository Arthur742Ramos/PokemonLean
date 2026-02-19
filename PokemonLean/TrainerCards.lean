import PokemonLean.Basic
import PokemonLean.Switching

namespace PokemonLean.TrainerCards

open PokemonLean
open PokemonLean.Switching

inductive TrainerKind
  | item
  | supporter
  | tool
  | stadium
  deriving Repr, BEq, DecidableEq

inductive TrainerEffect
  | draw (count : Nat)
  | healActive (amount : Nat)
  | switchActive (index : Nat)
  | takePrize
  | addDamage (amount : Nat)
  | discardTop (count : Nat)
  | searchDeck (name : String)
  deriving Repr, BEq, DecidableEq

structure TrainerCard where
  card : Card
  kind : TrainerKind
  effect : TrainerEffect
  deriving Repr, BEq, DecidableEq

def trainerName (trainer : TrainerCard) : String :=
  trainer.card.name

def isTrainerCard (trainer : TrainerCard) : Prop :=
  isTrainer trainer.card = true

def isSupporter (trainer : TrainerCard) : Bool :=
  match trainer.kind with
  | .supporter => true
  | _ => false

def isItem (trainer : TrainerCard) : Bool :=
  match trainer.kind with
  | .item => true
  | _ => false

def isTool (trainer : TrainerCard) : Bool :=
  match trainer.kind with
  | .tool => true
  | _ => false

def isStadium (trainer : TrainerCard) : Bool :=
  match trainer.kind with
  | .stadium => true
  | _ => false

def supporterCount : List TrainerCard → Nat
  | [] => 0
  | t :: rest => (if isSupporter t then 1 else 0) + supporterCount rest

def itemCount : List TrainerCard → Nat
  | [] => 0
  | t :: rest => (if isItem t then 1 else 0) + itemCount rest

def toolCount : List TrainerCard → Nat
  | [] => 0
  | t :: rest => (if isTool t then 1 else 0) + toolCount rest

def stadiumCount : List TrainerCard → Nat
  | [] => 0
  | t :: rest => (if isStadium t then 1 else 0) + stadiumCount rest

theorem supporterCount_le_length (ts : List TrainerCard) :
    supporterCount ts ≤ ts.length := by
  induction ts with
  | nil => simp [supporterCount]
  | cons t rest ih =>
      simp [supporterCount]
      split <;> omega

theorem itemCount_le_length (ts : List TrainerCard) :
    itemCount ts ≤ ts.length := by
  induction ts with
  | nil => simp [itemCount]
  | cons t rest ih =>
      simp [itemCount]
      split <;> omega

theorem toolCount_le_length (ts : List TrainerCard) :
    toolCount ts ≤ ts.length := by
  induction ts with
  | nil => simp [toolCount]
  | cons t rest ih =>
      simp [toolCount]
      split <;> omega

theorem stadiumCount_le_length (ts : List TrainerCard) :
    stadiumCount ts ≤ ts.length := by
  induction ts with
  | nil => simp [stadiumCount]
  | cons t rest ih =>
      simp [stadiumCount]
      split <;> omega

theorem supporterCount_zero_of_all_non_supporter (ts : List TrainerCard)
    (h : ∀ t ∈ ts, isSupporter t = false) :
    supporterCount ts = 0 := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      have hRest : ∀ t ∈ rest, isSupporter t = false := by
        intro t hMem
        exact h t (by simp [hMem])
      have hHead := h t (by simp)
      simp [supporterCount, hHead, ih hRest]

inductive TrainerError
  | cardNotInHand
  | notTrainer
  | emptyDeck
  | noActive
  | noBench
  | noPrizes
  | invalidSwitch
  | insufficientCards
  | cardNotFound
  | noDefender
  deriving Repr, BEq, DecidableEq

def removeFirstByName (name : String) : List Card → Option (Card × List Card)
  | [] => none
  | c :: rest =>
      if c.name == name then
        some (c, rest)
      else
        match removeFirstByName name rest with
        | none => none
        | some (found, rest') => some (found, c :: rest')

theorem removeFirstByName_length (name : String) :
    ∀ (deck : List Card) (found : Card) (rest : List Card),
      removeFirstByName name deck = some (found, rest) →
        rest.length + 1 = deck.length := by
  intro deck found rest h
  induction deck generalizing found rest with
  | nil =>
      simp [removeFirstByName] at h
  | cons head tail ih =>
      simp [removeFirstByName] at h
      split at h
      · cases h
        simp
      · cases hRec : removeFirstByName name tail with
        | none =>
            simp [hRec] at h
        | some pair =>
            rcases pair with ⟨found', rest'⟩
            simp [hRec] at h
            have hLen := ih found' rest' hRec
            rcases h with ⟨_, hRest⟩
            cases hRest
            simp [List.length_cons, hLen]

theorem removeFirstByName_mem (name : String) :
    ∀ (deck : List Card) (found : Card) (rest : List Card),
      removeFirstByName name deck = some (found, rest) →
        found ∈ deck := by
  intro deck found rest h
  induction deck generalizing found rest with
  | nil =>
      simp [removeFirstByName] at h
  | cons head tail ih =>
      simp [removeFirstByName] at h
      split at h
      · cases h
        simp
      · cases hRec : removeFirstByName name tail with
        | none =>
            simp [hRec] at h
        | some pair =>
            rcases pair with ⟨found', rest'⟩
            simp [hRec] at h
            have hMemTail := ih found' rest' hRec
            rcases h with ⟨hFound, _⟩
            have hMem : found ∈ tail := by
              simpa [hFound] using hMemTail
            exact (List.mem_cons).2 (Or.inr hMem)

theorem removeFirst_mem (card : Card) : ∀ {hand rest}, removeFirst card hand = some rest → card ∈ hand := by
  intro hand rest h
  induction hand generalizing rest with
  | nil =>
      simp [removeFirst] at h
  | cons head tail ih =>
      unfold removeFirst at h
      split at h
      · rename_i hBeq
        have hEq : head = card := eq_of_beq hBeq
        exact List.mem_cons.mpr (Or.inl hEq.symm)
      · cases hRec : removeFirst card tail with
        | none =>
            simp [hRec] at h
        | some rest' =>
            simp [hRec] at h
            cases h
            exact List.mem_cons.mpr (Or.inr (ih hRec))

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

def discardTop (hand : List Card) (n : Nat) : Option (List Card × List Card) :=
  if n ≤ hand.length then
    some (hand.take n, hand.drop n)
  else
    none

theorem discardTop_length (hand : List Card) (n : Nat) (discarded rest : List Card)
    (h : discardTop hand n = some (discarded, rest)) :
    discarded.length = n ∧ rest.length + n = hand.length := by
  unfold discardTop at h
  by_cases hLe : n ≤ hand.length
  · simp [hLe] at h
    rcases h with ⟨hTake, hDrop⟩
    cases hTake.symm
    cases hDrop.symm
    constructor
    · simp [List.length_take, Nat.min_eq_left hLe]
    · simp [List.length_drop, Nat.sub_add_cancel hLe]
  · have : False := by
      simp [hLe] at h
    exact False.elim this

theorem discardTop_none_of_gt (hand : List Card) (n : Nat)
    (h : hand.length < n) :
    discardTop hand n = none := by
  unfold discardTop
  have h' : ¬ n ≤ hand.length := Nat.not_le_of_gt h
  simp [h']

def applyTrainerEffect (state : GameState) : TrainerEffect → Except TrainerError GameState
  | .draw count =>
      let player := state.activePlayer
      let playerState := getPlayerState state player
      match drawFromDeck playerState.deck count with
      | none => .error .emptyDeck
      | some (drawn, rest) =>
          let updatedPlayerState :=
            { playerState with deck := rest, hand := playerState.hand ++ drawn }
          .ok (setPlayerState state player updatedPlayerState)
  | .healActive amount =>
      let player := state.activePlayer
      let playerState := getPlayerState state player
      match playerState.active with
      | none => .error .noActive
      | some active =>
          let updatedActive := { active with damage := Nat.sub active.damage amount }
          let updatedPlayerState := { playerState with active := some updatedActive }
          .ok (setPlayerState state player updatedPlayerState)
  | .switchActive index =>
      match switchActive state index with
      | none => .error .invalidSwitch
      | some state' => .ok state'
  | .takePrize =>
      let player := state.activePlayer
      let opponent := otherPlayer player
      let playerState := getPlayerState state player
      let opponentState := getPlayerState state opponent
      match opponentState.prizes with
      | [] => .error .noPrizes
      | _ =>
          let (newPlayer, newOpponent) := takePrize playerState opponentState
          let state' := setPlayerState (setPlayerState state player newPlayer) opponent newOpponent
          .ok state'
  | .addDamage amount =>
      let opponent := otherPlayer state.activePlayer
      let opponentState := getPlayerState state opponent
      match opponentState.active with
      | none => .error .noDefender
      | some active =>
          let updatedActive := applyDamage active amount
          let updatedOpponent := { opponentState with active := some updatedActive }
          .ok (setPlayerState state opponent updatedOpponent)
  | .discardTop count =>
      let player := state.activePlayer
      let playerState := getPlayerState state player
      match discardTop playerState.hand count with
      | none => .error .insufficientCards
      | some (discarded, rest) =>
          let updatedPlayerState :=
            { playerState with hand := rest, discard := discarded ++ playerState.discard }
          .ok (setPlayerState state player updatedPlayerState)
  | .searchDeck name =>
      let player := state.activePlayer
      let playerState := getPlayerState state player
      match removeFirstByName name playerState.deck with
      | none => .error .cardNotFound
      | some (found, rest) =>
          let updatedPlayerState :=
            { playerState with deck := rest, hand := found :: playerState.hand }
          .ok (setPlayerState state player updatedPlayerState)

def playTrainerCard (state : GameState) (trainer : TrainerCard) : Except TrainerError GameState :=
  let player := state.activePlayer
  let playerState := getPlayerState state player
  if isTrainer trainer.card then
    match removeFirst trainer.card playerState.hand with
    | none => .error .cardNotInHand
    | some newHand =>
        let updatedPlayerState :=
          { playerState with hand := newHand, discard := trainer.card :: playerState.discard }
        applyTrainerEffect (setPlayerState state player updatedPlayerState) trainer.effect
  else
    .error .notTrainer

def playTrainerSequence (state : GameState) : List TrainerCard → Except TrainerError GameState
  | [] => .ok state
  | trainer :: rest =>
      match playTrainerCard state trainer with
      | .error err => .error err
      | .ok next => playTrainerSequence next rest

def trainerSequenceLegal (trainers : List TrainerCard) : Prop :=
  supporterCount trainers ≤ 1

theorem trainerSequenceLegal_nil : trainerSequenceLegal [] := by
  simp [trainerSequenceLegal, supporterCount]

theorem trainerSequenceLegal_cons_supporter (t : TrainerCard) (ts : List TrainerCard)
    (hSupporter : isSupporter t = true) :
    trainerSequenceLegal (t :: ts) ↔ supporterCount ts = 0 := by
  -- unfold the definition: in the supporter case we have `supporterCount (t :: ts) = 1 + supporterCount ts`
  simp [trainerSequenceLegal, supporterCount, hSupporter]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem trainerSequenceLegal_cons_non_supporter (t : TrainerCard) (ts : List TrainerCard)
    (hSupporter : isSupporter t = false) :
    trainerSequenceLegal (t :: ts) ↔ trainerSequenceLegal ts := by
  simp [trainerSequenceLegal, supporterCount, hSupporter]

theorem playTrainerSequence_nil (state : GameState) :
    playTrainerSequence state [] = .ok state := by
  rfl

theorem playTrainerSequence_cons_ok (state : GameState) (trainer : TrainerCard) (rest : List TrainerCard)
    (next : GameState) (h : playTrainerCard state trainer = .ok next) :
    playTrainerSequence state (trainer :: rest) = playTrainerSequence next rest := by
  simp [playTrainerSequence, h]

theorem playTrainerCard_in_hand (state : GameState) (trainer : TrainerCard) (next : GameState)
    (h : playTrainerCard state trainer = .ok next) :
    trainer.card ∈ (getPlayerState state state.activePlayer).hand := by
  unfold playTrainerCard at h
  split at h
  · match hRemove : removeFirst trainer.card (getPlayerState state state.activePlayer).hand with
    | none => simp [hRemove] at h
    | some newHand =>
        simp [hRemove] at h
        exact removeFirst_mem trainer.card hRemove
  · simp at h

theorem playTrainerCard_supporter_limit (trainers : List TrainerCard)
    (hLegal : trainerSequenceLegal trainers) :
    supporterCount trainers ≤ 1 := by
  exact hLegal

end PokemonLean.TrainerCards
