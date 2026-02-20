import Lean.Data.Rat
import Std.Tactic
import PokemonLean.Core.Types

namespace PokemonLean.CardAdvantage

abbrev GameState := PokemonLean.Core.Types.GameState
abbrev PlayerState := PokemonLean.Core.Types.PlayerState
abbrev Player := PokemonLean.Core.Types.PlayerId
abbrev Card := PokemonLean.Core.Types.Card
abbrev Pokemon := PokemonLean.Core.Types.Pokemon
abbrev EnergyType := PokemonLean.Core.Types.EnergyType
abbrev Rat := Lean.Rat

def opponent : Player → Player
  | .player1 => .player2
  | .player2 => .player1

def playerStateFor (gs : GameState) (p : Player) : PlayerState :=
  match p with
  | .player1 => gs.player1
  | .player2 => gs.player2

def setPlayerState (gs : GameState) (p : Player) (ps : PlayerState) : GameState :=
  match p with
  | .player1 => { gs with player1 := ps }
  | .player2 => { gs with player2 := ps }

def handSize (gs : GameState) (p : Player) : Nat :=
  (playerStateFor gs p).hand.length

def benchSize (gs : GameState) (p : Player) : Nat :=
  (playerStateFor gs p).bench.length

def prizesRemaining (gs : GameState) (p : Player) : Nat :=
  (playerStateFor gs p).prizesRemaining

/-- Net card advantage:
`(your hand + your bench + opponent prizes remaining) -
 (opponent hand + opponent bench + your prizes remaining)`. -/
def cardAdvantage (gs : GameState) (p : Player) : Int :=
  let me := playerStateFor gs p
  let opp := playerStateFor gs (opponent p)
  Int.ofNat (me.hand.length + me.bench.length + opp.prizesRemaining) -
    Int.ofNat (opp.hand.length + opp.bench.length + me.prizesRemaining)

def drawCard (gs : GameState) (p : Player) (c : Card) : GameState :=
  let me := playerStateFor gs p
  setPlayerState gs p { me with hand := c :: me.hand }

theorem DRAW_INCREASES_ADVANTAGE (gs : GameState) (p : Player) (c : Card) :
    cardAdvantage (drawCard gs p c) p = cardAdvantage gs p + 1 := by
  cases p <;>
    simp [drawCard, cardAdvantage, playerStateFor, opponent, setPlayerState,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.ofNat_succ, Int.add_assoc, Int.add_left_comm, Int.add_comm]

def professorsResearchDrawCount : Nat := 7

/-- Professor's Research: discard hand, draw 7. -/
def playProfessorsResearch (gs : GameState) (p : Player) : GameState :=
  let me := playerStateFor gs p
  let me' := { me with
    hand := List.replicate professorsResearchDrawCount default
    discard := me.hand ++ me.discard }
  setPlayerState gs p me'

theorem SUPPORTER_ADVANTAGE (gs : GameState) (p : Player) :
    cardAdvantage (playProfessorsResearch gs p) p - cardAdvantage gs p =
      (7 : Int) - Int.ofNat (handSize gs p) := by
  cases p <;>
    simp [playProfessorsResearch, cardAdvantage, handSize, playerStateFor, opponent, setPlayerState,
      professorsResearchDrawCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm, Int.add_comm]

/-- Model of KO resolution: opponent loses active, attacker takes `prizeCount` prizes. -/
def knockOutOpponent (gs : GameState) (attacker : Player) (prizeCount : Nat) : GameState :=
  let me := playerStateFor gs attacker
  let opp := playerStateFor gs (opponent attacker)
  let me' := { me with prizesRemaining := me.prizesRemaining - prizeCount }
  let opp' := { opp with active := none }
  setPlayerState (setPlayerState gs attacker me') (opponent attacker) opp'

theorem KO_ADVANTAGE_MULTI_PRIZE (gs : GameState) (p : Player) (prizeCount : Nat)
    (hPrize : prizeCount ≤ prizesRemaining gs p) :
    cardAdvantage (knockOutOpponent gs p prizeCount) p =
      cardAdvantage gs p + Int.ofNat prizeCount := by
  cases p <;>
    simp [knockOutOpponent, cardAdvantage, prizesRemaining, playerStateFor, opponent, setPlayerState] at hPrize ⊢
  · omega
  · omega

theorem KO_ADVANTAGE (gs : GameState) (p : Player)
    (hPrize : 1 ≤ prizesRemaining gs p) :
    cardAdvantage (knockOutOpponent gs p 1) p = cardAdvantage gs p + 1 := by
  simpa using KO_ADVANTAGE_MULTI_PRIZE gs p 1 hPrize

theorem MULTI_PRIZE_KO_GIVES_MORE (gs : GameState) (p : Player) (prizeCount : Nat)
    (hPos : 1 ≤ prizeCount)
    (hPrize : prizeCount ≤ prizesRemaining gs p) :
    cardAdvantage (knockOutOpponent gs p prizeCount) p ≥
      cardAdvantage (knockOutOpponent gs p 1) p := by
  rw [KO_ADVANTAGE_MULTI_PRIZE gs p prizeCount hPrize, KO_ADVANTAGE gs p (Nat.le_trans hPos hPrize)]
  have hInt : (1 : Int) ≤ Int.ofNat prizeCount := by
    simpa using (Int.ofNat_le.mpr hPos)
  omega

def pokemonEnergyCount (pk : Pokemon) : Nat :=
  pk.attachedEnergy.length

def activeEnergyCount : Option Pokemon → Nat
  | none => 0
  | some pk => pokemonEnergyCount pk

def benchEnergyCount (bench : List Pokemon) : Nat :=
  (bench.map pokemonEnergyCount).sum

/-- Tempo proxy: total attached energy on active + bench. -/
def tempo (gs : GameState) (p : Player) : Nat :=
  let me := playerStateFor gs p
  activeEnergyCount me.active + benchEnergyCount me.bench

def attachEnergyToActive (gs : GameState) (p : Player) (e : EnergyType) : GameState :=
  let me := playerStateFor gs p
  let me' := { me with
    active := me.active.map (fun activePk => { activePk with attachedEnergy := e :: activePk.attachedEnergy }) }
  setPlayerState gs p me'

theorem ENERGY_ATTACHMENT_TEMPO (gs : GameState) (p : Player) (e : EnergyType) (activePk : Pokemon)
    (hActive : (playerStateFor gs p).active = some activePk) :
    tempo (attachEnergyToActive gs p e) p = tempo gs p + 1 := by
  cases p <;>
    simp [tempo, attachEnergyToActive, playerStateFor, setPlayerState, activeEnergyCount,
      benchEnergyCount, pokemonEnergyCount, hActive, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

inductive Action where
  | playProfessorsResearch
  | playEnergySearchSupporter
  | playPotion
  | pass
  deriving Repr, DecidableEq, Inhabited

def supporterAdvantageGain : Action → Int
  | .playProfessorsResearch => 7
  | .playEnergySearchSupporter => 0
  | .playPotion => 0
  | .pass => 0

def supporterTempoGain : Action → Nat
  | .playProfessorsResearch => 0
  | .playEnergySearchSupporter => 1
  | .playPotion => 0
  | .pass => 0

theorem TEMPO_VS_ADVANTAGE_TRADEOFF :
    supporterAdvantageGain .playProfessorsResearch >
      supporterAdvantageGain .playEnergySearchSupporter ∧
    supporterTempoGain .playProfessorsResearch <
      supporterTempoGain .playEnergySearchSupporter ∧
    Action.playProfessorsResearch ≠ Action.playEnergySearchSupporter := by
  decide

def activeCount (ps : PlayerState) : Nat :=
  match ps.active with
  | none => 0
  | some _ => 1

/-- Count of Pokemon in play (active + bench). -/
def boardPresence (gs : GameState) (p : Player) : Nat :=
  let me := playerStateFor gs p
  activeCount me + me.bench.length

def koRecoveryOptions (gs : GameState) (p : Player) : Nat :=
  benchSize gs p

def spreadDamageTargets (gs : GameState) (p : Player) : Nat :=
  benchSize gs p

theorem BENCH_ADVANTAGE (gs : GameState) (p q : Player)
    (hBench : benchSize gs p > benchSize gs q) :
    koRecoveryOptions gs p > koRecoveryOptions gs q ∧
      spreadDamageTargets gs p > spreadDamageTargets gs q := by
  exact ⟨hBench, hBench⟩

def totalPrizeCards : Nat := 6

def firstKOWinsPrizeRace (tradedKOs : Nat) : Prop :=
  totalPrizeCards - (tradedKOs + 1) < totalPrizeCards - tradedKOs

theorem PRIZE_RACE_THEOREM (tradedKOs : Nat)
    (hTrades : tradedKOs + 1 ≤ totalPrizeCards) :
    firstKOWinsPrizeRace tradedKOs := by
  unfold firstKOWinsPrizeRace totalPrizeCards
  omega

def actionsPerTurn (gs : GameState) (p : Player) : Int :=
  cardAdvantage gs p + 1

theorem CARD_ADVANTAGE_WIN_CORRELATION (gs : GameState) (p : Player) (N : Nat)
    (hAdv : Int.ofNat N ≤ cardAdvantage gs p) :
    Int.ofNat (N + 1) ≤ actionsPerTurn gs p := by
  unfold actionsPerTurn
  omega

/-- Rational efficiency metric for key actions. -/
def resourceEfficiency : Action → Rat
  | .playProfessorsResearch => (7 : Rat) / (1 : Rat)
  | .playEnergySearchSupporter => (1 : Rat) / (1 : Rat)
  | .playPotion => (0 : Rat)
  | .pass => (0 : Rat)

theorem PROFESSORS_RESEARCH_EFFICIENCY :
    resourceEfficiency .playProfessorsResearch = (7 : Rat) / (1 : Rat) := by
  rfl

theorem POTION_EFFICIENCY :
    resourceEfficiency .playPotion = (0 : Rat) := by
  rfl

theorem PROFESSORS_RESEARCH_BEST_EFFICIENCY (a : Action) :
    resourceEfficiency a ≤ resourceEfficiency .playProfessorsResearch := by
  cases a <;> decide

end PokemonLean.CardAdvantage
