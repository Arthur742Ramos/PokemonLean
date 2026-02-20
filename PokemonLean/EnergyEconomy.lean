import Lean.Data.Rat
import Std.Tactic
import PokemonLean.Core.Types

namespace PokemonLean.EnergyEconomy

open PokemonLean.Core.Types

abbrev Player := PlayerId
abbrev Rat := Lean.Rat

/-- Total energy symbols required by an attack. -/
def energyCost (attack : Attack) : Nat :=
  attack.cost.length

/-- Damage efficiency measured as damage divided by total energy cost. -/
def damagePerEnergy (attack : Attack) : Rat :=
  if _h : energyCost attack = 0 then
    0
  else
    (Int.ofNat attack.damage : Rat) / (Int.ofNat (energyCost attack) : Rat)

/-- Ceiling division for natural numbers. -/
def ceilDiv (a b : Nat) : Nat :=
  if b = 0 then 0 else (a + b - 1) / b

/-- Extra attachments beyond the default one attachment per turn. -/
def energyAcceleration : Nat := 0

def attachmentsPerTurn (extra : Nat) : Nat :=
  1 + extra

/-- Number of turns needed to provide `cost` energy at `1 + extra` attachments per turn. -/
def turnsToPowerUp (cost extra : Nat) : Nat :=
  ceilDiv cost (attachmentsPerTurn extra)

theorem ENERGY_BOTTLENECK (K : Nat) :
    turnsToPowerUp K 0 ≥ K := by
  simp [turnsToPowerUp, attachmentsPerTurn, ceilDiv]

theorem ACCELERATION_ADVANTAGE (K A : Nat) :
    turnsToPowerUp K A = ceilDiv K (1 + A) ∧ turnsToPowerUp K 0 = K := by
  constructor
  · rfl
  · simp [turnsToPowerUp, attachmentsPerTurn, ceilDiv]

def doubleTurboEnergyProvided : Nat := 2
def doubleTurboDamagePenalty : Int := 20

def doubleTurboDamage (baseDamage : Nat) : Int :=
  Int.ofNat baseDamage - doubleTurboDamagePenalty

/-- Better tempo payoff than two basic attachments for a 2-energy attack. -/
def doubleTurboWorthIt (baseDamage : Nat) : Prop :=
  (Int.ofNat doubleTurboEnergyProvided) * doubleTurboDamage baseDamage > Int.ofNat baseDamage

theorem DOUBLE_TURBO_TRADEOFF (baseDamage : Nat) :
    doubleTurboWorthIt baseDamage ↔ baseDamage > 40 := by
  unfold doubleTurboWorthIt doubleTurboDamage doubleTurboEnergyProvided doubleTurboDamagePenalty
  constructor <;> intro h
  · have hTwo : (Int.ofNat 2 : Int) = 2 := by decide
    rw [hTwo] at h
    have hmul : (2 : Int) * (Int.ofNat baseDamage - 20) =
        (Int.ofNat baseDamage - 20) + (Int.ofNat baseDamage - 20) := by
      omega
    rw [hmul] at h
    have hInt : (40 : Int) < Int.ofNat baseDamage := by
      omega
    exact Int.ofNat_lt.mp hInt
  · have hInt : (40 : Int) < Int.ofNat baseDamage := Int.ofNat_lt.mpr h
    have h' : (Int.ofNat baseDamage - 20) + (Int.ofNat baseDamage - 20) > Int.ofNat baseDamage := by
      omega
    have hTwo : (Int.ofNat 2 : Int) = 2 := by decide
    rw [hTwo]
    have hmul : (2 : Int) * (Int.ofNat baseDamage - 20) =
        (Int.ofNat baseDamage - 20) + (Int.ofNat baseDamage - 20) := by
      omega
    rw [hmul]
    exact h'

def playerState (gs : GameState) (player : Player) : PlayerState :=
  match player with
  | .player1 => gs.player1
  | .player2 => gs.player2

def playerPokemon (ps : PlayerState) : List Pokemon :=
  (match ps.active with
   | some p => [p]
   | none => []) ++ ps.bench

def pokemonAttachedEnergy (pokemon : Pokemon) : Nat :=
  pokemon.attachedEnergy.length

def pokemonAttackEnergyNeed (pokemon : Pokemon) : Nat :=
  (pokemon.attacks.map energyCost).sum

def totalEnergyInPlay (ps : PlayerState) : Nat :=
  (playerPokemon ps).map pokemonAttachedEnergy |>.sum

def totalEnergyNeeded (ps : PlayerState) : Nat :=
  (playerPokemon ps).map pokemonAttackEnergyNeed |>.sum

/-- Energy in play minus energy needed to pay all listed attacks. -/
def energySurplus (gs : GameState) (player : Player) : Int :=
  Int.ofNat (totalEnergyInPlay (playerState gs player)) -
    Int.ofNat (totalEnergyNeeded (playerState gs player))

def canAttackEveryTurn (gs : GameState) (player : Player) : Prop :=
  Int.ofNat (totalEnergyInPlay (playerState gs player)) ≥
    Int.ofNat (totalEnergyNeeded (playerState gs player))

theorem SURPLUS_POSITIVE_MEANS_READY (gs : GameState) (player : Player)
    (hSurplus : energySurplus gs player ≥ 0) :
    canAttackEveryTurn gs player := by
  unfold energySurplus at hSurplus
  unfold canAttackEveryTurn
  omega

def tempoGainFromEnergyDenial : Nat := 1

theorem ENERGY_DENIAL_THEOREM (K : Nat) :
    turnsToPowerUp (K + 1) 0 = turnsToPowerUp K 0 + tempoGainFromEnergyDenial := by
  simp [turnsToPowerUp, attachmentsPerTurn, ceilDiv, tempoGainFromEnergyDenial, Nat.add_assoc]

theorem RETREAT_COST_TAX (K R : Nat) :
    turnsToPowerUp (K + R) 0 = turnsToPowerUp K 0 + R := by
  simp [turnsToPowerUp, attachmentsPerTurn, ceilDiv]

theorem FREE_RETREAT_VALUE (K : Nat) :
    turnsToPowerUp (K + 0) 0 = turnsToPowerUp K 0 := by
  simpa using RETREAT_COST_TAX K 0

inductive EnergyInvestment
  | pokemonA
  | pokemonB
  deriving DecidableEq, Repr

def pokemonDPE (pokemon : Pokemon) : Rat :=
  (pokemon.attacks.map damagePerEnergy).foldl (fun a b => if a ≤ b then b else a) 0

/-- Two-Pokémon attachment choice: pick the higher damage-per-energy target. -/
def energyROI (pokemonA pokemonB : Pokemon) : EnergyInvestment :=
  if pokemonDPE pokemonA ≥ pokemonDPE pokemonB then
    .pokemonA
  else
    .pokemonB

theorem HIGHER_DPE_OPTIMAL (pokemonA pokemonB : Pokemon)
    (h : pokemonDPE pokemonA ≥ pokemonDPE pokemonB) :
    energyROI pokemonA pokemonB = .pokemonA := by
  simp [energyROI, h]

end PokemonLean.EnergyEconomy
