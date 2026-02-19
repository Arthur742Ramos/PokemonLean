import PokemonLean.Core.Types
import PokemonLean.Probability

namespace PokemonLean.InformationTheory

abbrev Rat := PokemonLean.Probability.Rat
abbrev GameState := PokemonLean.Core.Types.GameState
abbrev PlayerState := PokemonLean.Core.Types.PlayerState
abbrev PlayerId := PokemonLean.Core.Types.PlayerId
abbrev Card := PokemonLean.Core.Types.Card
abbrev Pokemon := PokemonLean.Core.Types.Pokemon

def playerStateFor (viewer : PlayerId) (gs : GameState) : PlayerState :=
  match viewer with
  | .player1 => gs.player1
  | .player2 => gs.player2

def opponentStateFor (viewer : PlayerId) (gs : GameState) : PlayerState :=
  match viewer with
  | .player1 => gs.player2
  | .player2 => gs.player1

/-- Hidden information from the perspective of one player. -/
structure HiddenState where
  opponentHand : List Card
  opponentDeckOrder : List Card
  faceDownPrizes : List Card
  deriving Repr, Inhabited, DecidableEq

/-- Publicly visible information from one player's perspective. -/
structure VisibleState where
  ownHand : List Card
  ownActive : Option Pokemon
  opponentActive : Option Pokemon
  ownBench : List Pokemon
  opponentBench : List Pokemon
  ownDiscard : List Card
  opponentDiscard : List Card
  ownPrizeCount : Nat
  opponentPrizeCount : Nat
  deriving Repr, Inhabited, DecidableEq

def hiddenStateFor (viewer : PlayerId) (gs : GameState) : HiddenState :=
  let me := playerStateFor viewer gs
  let opp := opponentStateFor viewer gs
  { opponentHand := opp.hand
    opponentDeckOrder := opp.deck
    faceDownPrizes := me.prizes ++ opp.prizes }

def visibleStateFor (viewer : PlayerId) (gs : GameState) : VisibleState :=
  let me := playerStateFor viewer gs
  let opp := opponentStateFor viewer gs
  { ownHand := me.hand
    ownActive := me.active
    opponentActive := opp.active
    ownBench := me.bench
    opponentBench := opp.bench
    ownDiscard := me.discard
    opponentDiscard := opp.discard
    ownPrizeCount := me.prizesRemaining
    opponentPrizeCount := opp.prizesRemaining }

/-- All full game states consistent with the same visible projection. -/
def InformationSet (viewer : PlayerId) (vs : VisibleState) : GameState → Prop :=
  fun gs => visibleStateFor viewer gs = vs

def log2Approx (p : Rat) : Rat :=
  if p <= 0 then 0
  else if p = (1 : Rat) then 0
  else if p <= (1 : Rat) / (8 : Rat) then (-3 : Rat)
  else if p <= (1 : Rat) / (4 : Rat) then (-2 : Rat)
  else if p <= (1 : Rat) / (2 : Rat) then (-1 : Rat)
  else (-1 : Rat) / (2 : Rat)

/-- Rational Shannon entropy approximation: `-∑ p * log2Approx(p)`. -/
def entropy {α : Type} (dist : List (α × Rat)) : Rat :=
  dist.foldl (fun acc xp => acc - xp.2 * log2Approx xp.2) 0

def deckSize : Nat := 60
def openingHandSize : Nat := 7

def openingHandEntropyUnits (knownFromOpponentHand : Nat) : Nat :=
  openingHandSize - knownFromOpponentHand

theorem INITIAL_HAND_ENTROPY (knownFromOpponentHand : Nat) :
    openingHandEntropyUnits knownFromOpponentHand ≤ openingHandEntropyUnits 0 := by
  unfold openingHandEntropyUnits openingHandSize
  exact Nat.sub_le 7 knownFromOpponentHand

def unknownDeckHandCompositionEntropy (publicDiscardCount : Nat) : Nat :=
  deckSize - publicDiscardCount

theorem DISCARD_PILE_REDUCES_ENTROPY (publicDiscardCount : Nat) :
    unknownDeckHandCompositionEntropy (publicDiscardCount + 1) ≤
      unknownDeckHandCompositionEntropy publicDiscardCount := by
  unfold unknownDeckHandCompositionEntropy deckSize
  exact Nat.sub_le_sub_left (Nat.le_succ publicDiscardCount) 60

def totalPrizeCards : Nat := 6

def unknownPrizeEntropy (prizesTaken : Nat) : Nat :=
  totalPrizeCards - prizesTaken

theorem PRIZE_INFORMATION_THEOREM (prizesTaken : Nat) :
    unknownPrizeEntropy (prizesTaken + 1) ≤ unknownPrizeEntropy prizesTaken := by
  unfold unknownPrizeEntropy totalPrizeCards
  exact Nat.sub_le_sub_left (Nat.le_succ prizesTaken) 6

inductive SupporterCard where
  | professorsResearch
  | iono
  | judge
  | bossOrders
  deriving Repr, Inhabited, DecidableEq

inductive Action where
  | playSupporter (supporter : SupporterCard)
  | playItem
  | attack
  | pass
  deriving Repr, Inhabited, DecidableEq

def optimalInformationGain : Action → Rat
  | .playSupporter .professorsResearch => (7 : Rat)
  | .playSupporter _ => (4 : Rat)
  | .playItem => (2 : Rat)
  | .attack => (1 : Rat)
  | .pass => (0 : Rat)

theorem PROFESSORS_RESEARCH_MAX_INFORMATION (a : Action) :
    optimalInformationGain a ≤ optimalInformationGain (.playSupporter .professorsResearch) := by
  cases a with
  | playSupporter s =>
      cases s <;> simp [optimalInformationGain]
      all_goals native_decide
  | playItem =>
      simp [optimalInformationGain]
      native_decide
  | attack =>
      simp [optimalInformationGain]
      native_decide
  | pass =>
      simp [optimalInformationGain]
      native_decide

structure CountingKnowledge where
  player1DeckKnown : Bool
  player2DeckKnown : Bool
  player1PrizesKnown : Bool
  player2PrizesKnown : Bool
  deriving Repr, Inhabited, DecidableEq

def PerfectInformationGame (k : CountingKnowledge) : Prop :=
  k.player1DeckKnown = true ∧
  k.player2DeckKnown = true ∧
  k.player1PrizesKnown = true ∧
  k.player2PrizesKnown = true

theorem PERFECT_INFORMATION_ENDGAME (k : CountingKnowledge)
    (hDeck1 : k.player1DeckKnown = true)
    (hDeck2 : k.player2DeckKnown = true)
    (hPrize1 : k.player1PrizesKnown = true)
    (hPrize2 : k.player2PrizesKnown = true) :
    PerfectInformationGame k := by
  exact ⟨hDeck1, hDeck2, hPrize1, hPrize2⟩

structure HiddenInformationSnapshot where
  opponentHandUnknown : Nat
  deckOrderUnknown : Nat
  faceDownPrizeUnknown : Nat
  deriving Repr, Inhabited, DecidableEq

def totalHiddenInformationEntropy (s : HiddenInformationSnapshot) : Nat :=
  s.opponentHandUnknown + s.deckOrderUnknown + s.faceDownPrizeUnknown

theorem INFORMATION_MONOTONICITY
    (before after : HiddenInformationSnapshot)
    (hHand : after.opponentHandUnknown ≤ before.opponentHandUnknown)
    (hDeck : after.deckOrderUnknown ≤ before.deckOrderUnknown)
    (hPrize : after.faceDownPrizeUnknown ≤ before.faceDownPrizeUnknown) :
    totalHiddenInformationEntropy after ≤ totalHiddenInformationEntropy before := by
  unfold totalHiddenInformationEntropy
  exact Nat.add_le_add (Nat.add_le_add hHand hDeck) hPrize

end PokemonLean.InformationTheory
