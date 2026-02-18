import PokemonLean.Basic

namespace PokemonLean.GXAttacks

open PokemonLean

-- ============================================================================
-- ONCE-PER-GAME MECHANIC TYPES
-- ============================================================================

inductive OncePerGameKind
  | gxAttack
  | vstarPower
  | aceSpec
  deriving Repr, BEq, DecidableEq

structure OncePerGameState where
  gxUsed : Bool := false
  vstarUsed : Bool := false
  deriving Repr, BEq, DecidableEq

def initialOncePerGame : OncePerGameState :=
  { gxUsed := false, vstarUsed := false }

-- 1
theorem initial_gx_available : initialOncePerGame.gxUsed = false := rfl
-- 2
theorem initial_vstar_available : initialOncePerGame.vstarUsed = false := rfl

-- ============================================================================
-- GX ATTACK MODEL
-- ============================================================================

structure GXAttack where
  name : String
  baseDamage : Nat
  extraEffect : Bool
  energyCost : List EnergyType
  deriving Repr, BEq, DecidableEq

def canUseGX (state : OncePerGameState) : Bool := !state.gxUsed

def useGX (state : OncePerGameState) : OncePerGameState :=
  { state with gxUsed := true }

-- 3
theorem canUseGX_initial : canUseGX initialOncePerGame = true := rfl
-- 4
theorem cannot_use_gx_after_use : canUseGX (useGX initialOncePerGame) = false := rfl
-- 5
theorem useGX_sets_true (s : OncePerGameState) : (useGX s).gxUsed = true := rfl
-- 6
theorem useGX_preserves_vstar (s : OncePerGameState) : (useGX s).vstarUsed = s.vstarUsed := rfl
-- 7
theorem canUseGX_false_after_use (s : OncePerGameState) : canUseGX (useGX s) = false := rfl
-- 8
theorem canUseGX_iff (s : OncePerGameState) : canUseGX s = true ↔ s.gxUsed = false := by
  simp [canUseGX]
-- 9
theorem gx_idempotent (s : OncePerGameState) : useGX (useGX s) = useGX s := rfl

-- ============================================================================
-- VSTAR POWER MODEL
-- ============================================================================

inductive VStarPowerKind
  | vstarAttack
  | vstarAbility
  deriving Repr, BEq, DecidableEq

structure VStarPower where
  name : String
  kind : VStarPowerKind
  baseDamage : Nat
  energyCost : List EnergyType
  deriving Repr, BEq, DecidableEq

def canUseVStar (state : OncePerGameState) : Bool := !state.vstarUsed

def useVStar (state : OncePerGameState) : OncePerGameState :=
  { state with vstarUsed := true }

-- 10
theorem canUseVStar_initial : canUseVStar initialOncePerGame = true := rfl
-- 11
theorem cannot_use_vstar_after_use : canUseVStar (useVStar initialOncePerGame) = false := rfl
-- 12
theorem useVStar_sets_true (s : OncePerGameState) : (useVStar s).vstarUsed = true := rfl
-- 13
theorem useVStar_preserves_gx (s : OncePerGameState) : (useVStar s).gxUsed = s.gxUsed := rfl
-- 14
theorem canUseVStar_false_after_use (s : OncePerGameState) : canUseVStar (useVStar s) = false := rfl
-- 15
theorem canUseVStar_iff (s : OncePerGameState) : canUseVStar s = true ↔ s.vstarUsed = false := by
  simp [canUseVStar]
-- 16
theorem vstar_idempotent (s : OncePerGameState) : useVStar (useVStar s) = useVStar s := rfl

-- ============================================================================
-- INDEPENDENCE OF GX AND VSTAR
-- ============================================================================

-- 17
theorem gx_and_vstar_independent_initial :
    canUseGX initialOncePerGame = true ∧ canUseVStar initialOncePerGame = true := ⟨rfl, rfl⟩
-- 18
theorem use_gx_preserves_vstar_availability :
    canUseVStar (useGX initialOncePerGame) = true := rfl
-- 19
theorem use_vstar_preserves_gx_availability :
    canUseGX (useVStar initialOncePerGame) = true := rfl
-- 20
theorem can_use_both_in_same_game :
    let s1 := useGX initialOncePerGame
    let s2 := useVStar s1
    s2.gxUsed = true ∧ s2.vstarUsed = true := ⟨rfl, rfl⟩
-- 21
theorem order_doesnt_matter_gx_then_vstar :
    useVStar (useGX initialOncePerGame) = useGX (useVStar initialOncePerGame) := rfl
-- 22
theorem both_used_means_neither_available (s : OncePerGameState)
    (hg : s.gxUsed = true) (hv : s.vstarUsed = true) :
    canUseGX s = false ∧ canUseVStar s = false := by
  simp [canUseGX, canUseVStar, hg, hv]

-- ============================================================================
-- PRIZE VALUE MECHANICS
-- ============================================================================

inductive PrizeValue
  | one
  | two
  | three
  deriving Repr, BEq, DecidableEq

def PrizeValue.toNat : PrizeValue → Nat
  | .one   => 1
  | .two   => 2
  | .three => 3

-- 23
theorem prize_one_val : PrizeValue.one.toNat = 1 := rfl
-- 24
theorem prize_two_val : PrizeValue.two.toNat = 2 := rfl
-- 25
theorem prize_three_val : PrizeValue.three.toNat = 3 := rfl
-- 26
theorem prize_pos (p : PrizeValue) : p.toNat > 0 := by cases p <;> decide
-- 27
theorem prize_le_three (p : PrizeValue) : p.toNat ≤ 3 := by cases p <;> decide
-- 28
theorem prize_ge_one (p : PrizeValue) : p.toNat ≥ 1 := by cases p <;> decide
-- 29
theorem two_vmax_kos_win : PrizeValue.three.toNat + PrizeValue.three.toNat = 6 := rfl
-- 30
theorem three_v_kos_win : PrizeValue.two.toNat * 3 = 6 := rfl
-- 31
theorem six_regular_kos_win : PrizeValue.one.toNat * 6 = 6 := rfl
-- 32
theorem v_plus_vmax_is_five : PrizeValue.two.toNat + PrizeValue.three.toNat = 5 := rfl
-- 33
theorem two_v_plus_one_regular :
    PrizeValue.two.toNat + PrizeValue.two.toNat + PrizeValue.one.toNat = 5 := rfl

-- ============================================================================
-- POWER BUDGET / HP SCALING
-- ============================================================================

structure PowerBudget where
  minHP : Nat
  maxHP : Nat
  prizeValue : PrizeValue
  deriving Repr, BEq, DecidableEq

def regularBudget : PowerBudget := { minHP := 30, maxHP := 130, prizeValue := .one }
def vBudget : PowerBudget := { minHP := 190, maxHP := 230, prizeValue := .two }
def vmaxBudget : PowerBudget := { minHP := 300, maxHP := 340, prizeValue := .three }
def vstarBudget : PowerBudget := { minHP := 250, maxHP := 280, prizeValue := .two }
def gxBudget : PowerBudget := { minHP := 170, maxHP := 250, prizeValue := .two }

-- 34
theorem regular_hp_range : regularBudget.minHP = 30 ∧ regularBudget.maxHP = 130 := ⟨rfl, rfl⟩
-- 35
theorem v_hp_range : vBudget.minHP = 190 ∧ vBudget.maxHP = 230 := ⟨rfl, rfl⟩
-- 36
theorem vmax_hp_range : vmaxBudget.minHP = 300 ∧ vmaxBudget.maxHP = 340 := ⟨rfl, rfl⟩
-- 37
theorem vstar_hp_range : vstarBudget.minHP = 250 ∧ vstarBudget.maxHP = 280 := ⟨rfl, rfl⟩
-- 38
theorem gx_hp_range : gxBudget.minHP = 170 ∧ gxBudget.maxHP = 250 := ⟨rfl, rfl⟩
-- 39
theorem v_hp_gt_regular : vBudget.minHP > regularBudget.maxHP := by decide
-- 40
theorem vmax_hp_gt_v : vmaxBudget.minHP > vBudget.maxHP := by decide
-- 41
theorem vstar_hp_gt_v : vstarBudget.minHP > vBudget.maxHP := by decide
-- 42
theorem higher_hp_higher_prize_v :
    vBudget.prizeValue.toNat > regularBudget.prizeValue.toNat := by decide
-- 43
theorem higher_hp_higher_prize_vmax :
    vmaxBudget.prizeValue.toNat > vBudget.prizeValue.toNat := by decide

-- ============================================================================
-- GX ATTACK DAMAGE CALCULATION
-- ============================================================================

def gxDamage (attack : GXAttack) (bonusDamage : Nat) : Nat :=
  attack.baseDamage + (if attack.extraEffect then bonusDamage else 0)

-- 44
theorem gxDamage_no_extra (attack : GXAttack) (bonus : Nat) (h : attack.extraEffect = false) :
    gxDamage attack bonus = attack.baseDamage := by simp [gxDamage, h]
-- 45
theorem gxDamage_with_extra (attack : GXAttack) (bonus : Nat) (h : attack.extraEffect = true) :
    gxDamage attack bonus = attack.baseDamage + bonus := by simp [gxDamage, h]
-- 46
theorem gxDamage_ge_base (attack : GXAttack) (bonus : Nat) :
    gxDamage attack bonus ≥ attack.baseDamage := by
  unfold gxDamage; split <;> omega
-- 47
theorem gxDamage_zero_bonus (attack : GXAttack) :
    gxDamage attack 0 = attack.baseDamage := by unfold gxDamage; split <;> omega

-- ============================================================================
-- VSTAR POWER DAMAGE
-- ============================================================================

def vstarDamage (power : VStarPower) : Nat :=
  match power.kind with
  | .vstarAttack => power.baseDamage
  | .vstarAbility => 0

-- 48
theorem vstar_ability_no_damage (power : VStarPower) (h : power.kind = .vstarAbility) :
    vstarDamage power = 0 := by simp [vstarDamage, h]
-- 49
theorem vstar_attack_has_damage (power : VStarPower) (h : power.kind = .vstarAttack) :
    vstarDamage power = power.baseDamage := by simp [vstarDamage, h]
-- 50
theorem vstar_damage_le_base (power : VStarPower) :
    vstarDamage power ≤ power.baseDamage := by
  unfold vstarDamage; cases power.kind <;> simp

-- ============================================================================
-- EXTENDED GAME STATE
-- ============================================================================

structure ExtendedGameState where
  base : GameState
  player1Once : OncePerGameState
  player2Once : OncePerGameState
  deriving Repr, BEq, DecidableEq

def mkExtendedState (gs : GameState) : ExtendedGameState :=
  { base := gs, player1Once := initialOncePerGame, player2Once := initialOncePerGame }

def getOncePerGame (egs : ExtendedGameState) (player : PlayerId) : OncePerGameState :=
  match player with
  | .playerOne => egs.player1Once
  | .playerTwo => egs.player2Once

def setOncePerGame (egs : ExtendedGameState) (player : PlayerId) (s : OncePerGameState) : ExtendedGameState :=
  match player with
  | .playerOne => { egs with player1Once := s }
  | .playerTwo => { egs with player2Once := s }

-- 51
theorem mkExtended_p1_fresh (gs : GameState) :
    (mkExtendedState gs).player1Once = initialOncePerGame := rfl
-- 52
theorem mkExtended_p2_fresh (gs : GameState) :
    (mkExtendedState gs).player2Once = initialOncePerGame := rfl
-- 53
theorem getOncePerGame_p1 (egs : ExtendedGameState) :
    getOncePerGame egs .playerOne = egs.player1Once := rfl
-- 54
theorem getOncePerGame_p2 (egs : ExtendedGameState) :
    getOncePerGame egs .playerTwo = egs.player2Once := rfl
-- 55
theorem setOncePerGame_p1 (egs : ExtendedGameState) (s : OncePerGameState) :
    (setOncePerGame egs .playerOne s).player1Once = s := rfl
-- 56
theorem setOncePerGame_p2 (egs : ExtendedGameState) (s : OncePerGameState) :
    (setOncePerGame egs .playerTwo s).player2Once = s := rfl
-- 57
theorem set_p1_preserves_p2 (egs : ExtendedGameState) (s : OncePerGameState) :
    (setOncePerGame egs .playerOne s).player2Once = egs.player2Once := rfl
-- 58
theorem set_p2_preserves_p1 (egs : ExtendedGameState) (s : OncePerGameState) :
    (setOncePerGame egs .playerTwo s).player1Once = egs.player1Once := rfl
-- 59
theorem set_preserves_base_p1 (egs : ExtendedGameState) (s : OncePerGameState) :
    (setOncePerGame egs .playerOne s).base = egs.base := rfl
-- 60
theorem set_preserves_base_p2 (egs : ExtendedGameState) (s : OncePerGameState) :
    (setOncePerGame egs .playerTwo s).base = egs.base := rfl

-- ============================================================================
-- PRIZE MATH
-- ============================================================================

def prizesRemaining (total taken : Nat) : Nat := total - taken

-- 61
theorem start_with_six : prizesRemaining 6 0 = 6 := rfl
-- 62
theorem win_when_six_taken : prizesRemaining 6 6 = 0 := rfl
-- 63
theorem one_vmax_ko_leaves_three : prizesRemaining 6 3 = 3 := rfl
-- 64
theorem two_v_kos_leaves_two : prizesRemaining 6 4 = 2 := rfl
-- 65
theorem three_regular_kos_leaves_three : prizesRemaining 6 3 = 3 := rfl

-- ============================================================================
-- PRIZE TRADE EFFICIENCY
-- ============================================================================

def prizeTradeRatio (yourPrizeValue opponentPrizeValue : PrizeValue) : Bool :=
  yourPrizeValue.toNat ≤ opponentPrizeValue.toNat

-- 66
theorem favorable_trade_regular_vs_v : prizeTradeRatio .one .two = true := rfl
-- 67
theorem favorable_trade_regular_vs_vmax : prizeTradeRatio .one .three = true := rfl
-- 68
theorem even_trade_v_vs_v : prizeTradeRatio .two .two = true := rfl
-- 69
theorem unfavorable_trade_vmax_vs_regular : prizeTradeRatio .three .one = false := rfl
-- 70
theorem unfavorable_trade_v_vs_regular : prizeTradeRatio .two .one = false := rfl

end PokemonLean.GXAttacks
