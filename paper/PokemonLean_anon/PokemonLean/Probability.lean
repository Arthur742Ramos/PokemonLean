import Lean.Data.Rat
import PokemonLean.Core.Types

open Lean

namespace PokemonLean.Probability

abbrev Rat := Lean.Rat
abbrev Attack := PokemonLean.Core.Types.Attack

structure Dist (α : Type) where
  outcomes : List (α × Rat)
  deriving Repr, Inhabited

namespace Dist

variable {α : Type} {β : Type}

protected def pure (x : α) : Dist α :=
  { outcomes := [(x, 1)] }

protected def bind (d : Dist α) (f : α → Dist β) : Dist β :=
  { outcomes := d.outcomes.flatMap (fun ap =>
      let a := ap.1
      let p := ap.2
      (f a).outcomes.map (fun bq => (bq.1, p * bq.2))) }

protected def map (f : α → β) (d : Dist α) : Dist β :=
  { outcomes := d.outcomes.map (fun ap => (f ap.1, ap.2)) }

def probOf [DecidableEq α] (d : Dist α) (x : α) : Rat :=
  d.outcomes.foldl (fun acc yp => if yp.1 = x then acc + yp.2 else acc) 0

def totalMass (d : Dist α) : Rat :=
  d.outcomes.foldl (fun acc yp => acc + yp.2) 0

instance : Monad Dist where
  pure := Dist.pure
  bind := Dist.bind
  map := Dist.map
  seq mf mx := Dist.bind mf (fun f => Dist.bind (mx ()) (fun x => Dist.pure (f x)))

end Dist

def CoinFlip : Dist Bool :=
  { outcomes := [(true, (1 : Rat) / (2 : Rat)), (false, (1 : Rat) / (2 : Rat))] }

def flipCoins : Nat → Dist Nat
  | 0 => pure 0
  | n + 1 => do
      let h ← CoinFlip
      let k ← flipCoins n
      pure (k + if h then 1 else 0)

def expectedValue (d : Dist Rat) : Rat :=
  d.outcomes.foldl (fun acc xp => acc + xp.1 * xp.2) 0

instance : Coe (Dist Bool) (Dist Rat) where
  coe d := Dist.map (fun b => if b then (1 : Rat) else (0 : Rat)) d

def natDistToRat (d : Dist Nat) : Dist Rat :=
  Dist.map (fun n => (Int.ofNat n : Rat)) d

def expectedNat (d : Dist Nat) : Rat :=
  expectedValue (natDistToRat d)

theorem expectedValue_coinFlip :
    expectedValue CoinFlip = (1 : Rat) / (2 : Rat) := by
  decide

theorem flipCoins3_binomial :
    Dist.probOf (flipCoins 3) 0 = (1 : Rat) / (8 : Rat) ∧
    Dist.probOf (flipCoins 3) 1 = (3 : Rat) / (8 : Rat) ∧
    Dist.probOf (flipCoins 3) 2 = (3 : Rat) / (8 : Rat) ∧
    Dist.probOf (flipCoins 3) 3 = (1 : Rat) / (8 : Rat) := by
  decide

theorem expectedHeads_flipCoins3 :
    expectedNat (flipCoins 3) = (3 : Rat) / (2 : Rat) := by
  decide

structure CoinFlipEffect where
  flips : Nat
  damagePerHeads : Nat
  deriving Repr, Inhabited

def probabilisticDamage (attack : Attack) (effect : CoinFlipEffect) : Dist Nat :=
  Dist.map (fun heads => attack.damage + effect.damagePerHeads * heads) (flipCoins effect.flips)

def tripleCoinAttack : Attack :=
  { name := "Triple Coins"
    cost := []
    damage := 0
    effect := "Flip 3 coins. This attack does 30 damage for each heads." }

def tripleCoinEffect : CoinFlipEffect :=
  { flips := 3, damagePerHeads := 30 }

def tripleCoinDamage : Dist Nat :=
  probabilisticDamage tripleCoinAttack tripleCoinEffect

theorem tripleCoin_expectedDamage :
    expectedNat tripleCoinDamage = (45 : Rat) := by
  decide

theorem tripleCoin_expectedBounds :
    (0 : Rat) ≤ expectedNat tripleCoinDamage ∧
    expectedNat tripleCoinDamage ≤ (90 : Rat) := by
  decide

def flipUntilTails : Nat → Dist Nat
  | 0 => pure 0
  | n + 1 => do
      let h ← CoinFlip
      if h then
        let k ← flipUntilTails n
        pure (k + 1)
      else
        pure 0

structure UntilTailsEffect where
  maxFlips : Nat
  damagePerHeads : Nat
  deriving Repr, Inhabited

def probabilisticDamageUntilTails (attack : Attack) (effect : UntilTailsEffect) : Dist Nat :=
  Dist.map (fun heads => attack.damage + effect.damagePerHeads * heads) (flipUntilTails effect.maxFlips)

def furySwipesAttack : Attack :=
  { name := "Fury Swipes"
    cost := []
    damage := 0
    effect := "Flip coins until you get tails. This attack does 30 damage for each heads." }

def furySwipesEffect : UntilTailsEffect :=
  { maxFlips := 3, damagePerHeads := 30 }

def furySwipesDamage : Dist Nat :=
  probabilisticDamageUntilTails furySwipesAttack furySwipesEffect

theorem furySwipes_expectedDamage :
    expectedNat furySwipesDamage = (105 : Rat) / (4 : Rat) := by
  decide

theorem furySwipes_expectedBounds :
    (0 : Rat) ≤ expectedNat furySwipesDamage ∧
    expectedNat furySwipesDamage ≤ (30 : Rat) := by
  decide

end PokemonLean.Probability
