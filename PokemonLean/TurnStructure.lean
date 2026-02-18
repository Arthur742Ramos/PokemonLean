import PokemonLean.Basic

namespace PokemonLean.TurnStructure

open PokemonLean

-- ============================================================================
-- TURN PHASES
-- ============================================================================

inductive TurnPhase
  | drawPhase
  | mainPhase
  | attackPhase
  | betweenTurns
  deriving Repr, BEq, DecidableEq

def TurnPhase.toNat : TurnPhase → Nat
  | .drawPhase     => 0
  | .mainPhase     => 1
  | .attackPhase   => 2
  | .betweenTurns  => 3

instance : LT TurnPhase where
  lt a b := a.toNat < b.toNat

instance : LE TurnPhase where
  le a b := a.toNat ≤ b.toNat

instance (a b : TurnPhase) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

instance (a b : TurnPhase) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

-- 1
theorem draw_lt_main : TurnPhase.drawPhase < TurnPhase.mainPhase := by decide
-- 2
theorem main_lt_attack : TurnPhase.mainPhase < TurnPhase.attackPhase := by decide
-- 3
theorem attack_lt_between : TurnPhase.attackPhase < TurnPhase.betweenTurns := by decide
-- 4
theorem draw_lt_attack : TurnPhase.drawPhase < TurnPhase.attackPhase := by decide
-- 5
theorem draw_lt_between : TurnPhase.drawPhase < TurnPhase.betweenTurns := by decide
-- 6
theorem main_lt_between : TurnPhase.mainPhase < TurnPhase.betweenTurns := by decide
-- 7
theorem phase_lt_irrefl (p : TurnPhase) : ¬(p < p) := Nat.lt_irrefl _
-- 8
theorem phase_lt_trans {a b c : TurnPhase} (h1 : a < b) (h2 : b < c) : a < c :=
  Nat.lt_trans h1 h2
-- 9
theorem phase_le_refl (p : TurnPhase) : p ≤ p := Nat.le_refl _
-- 10
theorem phase_le_antisymm {a b : TurnPhase} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h1 h2; decide)
-- 11
theorem phase_trichotomy (a b : TurnPhase) : a < b ∨ a = b ∨ b < a := by
  cases a <;> cases b <;> first | exact Or.inl (by decide) | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (by decide))
-- 12
theorem phase_cases (p : TurnPhase) :
    p = .drawPhase ∨ p = .mainPhase ∨ p = .attackPhase ∨ p = .betweenTurns := by
  cases p <;> simp
-- 13
theorem four_phases : [TurnPhase.drawPhase, .mainPhase, .attackPhase, .betweenTurns].length = 4 := rfl

-- ============================================================================
-- MAIN PHASE ACTIONS
-- ============================================================================

inductive MainPhaseAction
  | playBasicPokemon
  | evolvePokemon
  | attachEnergy
  | playTrainer
  | retreat
  | useAbility
  deriving Repr, BEq, DecidableEq

structure TurnActionLog where
  energyAttached : Bool := false
  supporterPlayed : Bool := false
  stadiumPlayed : Bool := false
  retreated : Bool := false
  gxAttackUsed : Bool := false
  vstarPowerUsed : Bool := false
  normalEnergyCount : Nat := 0
  deriving Repr, BEq, DecidableEq

def emptyLog : TurnActionLog :=
  { energyAttached := false, supporterPlayed := false, stadiumPlayed := false,
    retreated := false, gxAttackUsed := false, vstarPowerUsed := false,
    normalEnergyCount := 0 }

-- 14
theorem emptyLog_no_energy : emptyLog.energyAttached = false := rfl
-- 15
theorem emptyLog_no_supporter : emptyLog.supporterPlayed = false := rfl
-- 16
theorem emptyLog_no_stadium : emptyLog.stadiumPlayed = false := rfl
-- 17
theorem emptyLog_no_retreat : emptyLog.retreated = false := rfl
-- 18
theorem emptyLog_no_gx : emptyLog.gxAttackUsed = false := rfl
-- 19
theorem emptyLog_no_vstar : emptyLog.vstarPowerUsed = false := rfl
-- 20
theorem emptyLog_zero_energy_count : emptyLog.normalEnergyCount = 0 := rfl

-- ============================================================================
-- ONCE-PER-TURN CONSTRAINTS
-- ============================================================================

def canAttachEnergy (log : TurnActionLog) : Bool := !log.energyAttached
def canPlaySupporter (log : TurnActionLog) : Bool := !log.supporterPlayed
def canPlayStadium (log : TurnActionLog) : Bool := !log.stadiumPlayed

def logEnergyAttach (log : TurnActionLog) : TurnActionLog :=
  { log with energyAttached := true, normalEnergyCount := log.normalEnergyCount + 1 }

def logSupporterPlayed (log : TurnActionLog) : TurnActionLog :=
  { log with supporterPlayed := true }

def logStadiumPlayed (log : TurnActionLog) : TurnActionLog :=
  { log with stadiumPlayed := true }

def logRetreat (log : TurnActionLog) : TurnActionLog :=
  { log with retreated := true }

-- 21
theorem canAttachEnergy_empty : canAttachEnergy emptyLog = true := rfl
-- 22
theorem canPlaySupporter_empty : canPlaySupporter emptyLog = true := rfl
-- 23
theorem canPlayStadium_empty : canPlayStadium emptyLog = true := rfl
-- 24
theorem cannot_attach_after_attach : canAttachEnergy (logEnergyAttach emptyLog) = false := rfl
-- 25
theorem cannot_supporter_after_supporter : canPlaySupporter (logSupporterPlayed emptyLog) = false := rfl
-- 26
theorem cannot_stadium_after_stadium : canPlayStadium (logStadiumPlayed emptyLog) = false := rfl
-- 27
theorem attach_then_supporter_ok : canPlaySupporter (logEnergyAttach emptyLog) = true := rfl
-- 28
theorem supporter_then_attach_ok : canAttachEnergy (logSupporterPlayed emptyLog) = true := rfl
-- 29
theorem energy_count_after_attach : (logEnergyAttach emptyLog).normalEnergyCount = 1 := rfl
-- 30
theorem energy_count_monotone (log : TurnActionLog) :
    log.normalEnergyCount ≤ (logEnergyAttach log).normalEnergyCount := by
  simp [logEnergyAttach]
-- 31
theorem logEnergyAttach_sets_true (log : TurnActionLog) :
    (logEnergyAttach log).energyAttached = true := by unfold logEnergyAttach; rfl
-- 32
theorem logSupporterPlayed_sets_true (log : TurnActionLog) :
    (logSupporterPlayed log).supporterPlayed = true := by unfold logSupporterPlayed; rfl
-- 33
theorem logStadiumPlayed_sets_true (log : TurnActionLog) :
    (logStadiumPlayed log).stadiumPlayed = true := by unfold logStadiumPlayed; rfl
-- 34
theorem logRetreat_sets_true (log : TurnActionLog) :
    (logRetreat log).retreated = true := by unfold logRetreat; rfl
-- 35
theorem logEnergyAttach_preserves_supporter (log : TurnActionLog) :
    (logEnergyAttach log).supporterPlayed = log.supporterPlayed := by unfold logEnergyAttach; rfl
-- 36
theorem logSupporterPlayed_preserves_energy (log : TurnActionLog) :
    (logSupporterPlayed log).energyAttached = log.energyAttached := by unfold logSupporterPlayed; rfl
-- 37
theorem logStadiumPlayed_preserves_energy (log : TurnActionLog) :
    (logStadiumPlayed log).energyAttached = log.energyAttached := by unfold logStadiumPlayed; rfl
-- 38
theorem logStadiumPlayed_preserves_supporter (log : TurnActionLog) :
    (logStadiumPlayed log).supporterPlayed = log.supporterPlayed := by unfold logStadiumPlayed; rfl
-- 39
theorem logRetreat_preserves_energy (log : TurnActionLog) :
    (logRetreat log).energyAttached = log.energyAttached := by unfold logRetreat; rfl
-- 40
theorem logRetreat_preserves_supporter (log : TurnActionLog) :
    (logRetreat log).supporterPlayed = log.supporterPlayed := by unfold logRetreat; rfl

-- ============================================================================
-- FIRST TURN RULES
-- ============================================================================

structure TurnContext where
  turnNumber : Nat
  isFirstPlayer : Bool
  deriving Repr, BEq, DecidableEq

def firstTurnNoAttack (ctx : TurnContext) : Bool :=
  ctx.turnNumber == 1 && ctx.isFirstPlayer

-- 41
theorem firstTurnNoAttack_turn1_first : firstTurnNoAttack ⟨1, true⟩ = true := rfl
-- 42
theorem firstTurnNoAttack_turn1_second : firstTurnNoAttack ⟨1, false⟩ = false := rfl
-- 43
theorem firstTurnNoAttack_turn2_first : firstTurnNoAttack ⟨2, true⟩ = false := rfl
-- 44
theorem firstTurnNoAttack_turn2_second : firstTurnNoAttack ⟨2, false⟩ = false := rfl
-- 45
theorem after_turn1_can_attack (ctx : TurnContext) (h : ctx.turnNumber > 1) :
    firstTurnNoAttack ctx = false := by
  simp [firstTurnNoAttack]; intro heq; omega

def firstTurnNoSupporter (ctx : TurnContext) : Bool :=
  ctx.turnNumber == 1 && ctx.isFirstPlayer

-- 46
theorem firstTurnNoSupporter_turn1_first : firstTurnNoSupporter ⟨1, true⟩ = true := rfl
-- 47
theorem firstTurnNoSupporter_turn2 (b : Bool) : firstTurnNoSupporter ⟨2, b⟩ = false := rfl
-- 48
theorem firstTurn_restrictions_match (ctx : TurnContext) :
    firstTurnNoAttack ctx = firstTurnNoSupporter ctx := rfl

def canAttackThisTurn (ctx : TurnContext) (log : TurnActionLog) (activeStatus : Option StatusCondition) : Bool :=
  !firstTurnNoAttack ctx &&
  (match activeStatus with
   | some .paralyzed => false
   | some .asleep => false
   | _ => true) &&
  !log.gxAttackUsed

-- 49
theorem canAttack_healthy_turn2 : canAttackThisTurn ⟨2, true⟩ emptyLog none = true := rfl
-- 50
theorem cannot_attack_paralyzed_turn2 : canAttackThisTurn ⟨2, true⟩ emptyLog (some .paralyzed) = false := rfl
-- 51
theorem cannot_attack_asleep_turn2 : canAttackThisTurn ⟨2, true⟩ emptyLog (some .asleep) = false := rfl
-- 52
theorem canAttack_burned_turn2 : canAttackThisTurn ⟨2, true⟩ emptyLog (some .burned) = true := rfl
-- 53
theorem canAttack_poisoned_turn2 : canAttackThisTurn ⟨2, true⟩ emptyLog (some .poisoned) = true := rfl
-- 54
theorem canAttack_confused_turn2 : canAttackThisTurn ⟨2, true⟩ emptyLog (some .confused) = true := rfl
-- 55
theorem cannot_attack_turn1_first : canAttackThisTurn ⟨1, true⟩ emptyLog none = false := rfl

-- ============================================================================
-- BETWEEN TURNS
-- ============================================================================

def applyPoisonBetweenTurns (pokemon : PokemonInPlay) : PokemonInPlay :=
  match pokemon.status with
  | some .poisoned => { pokemon with damage := pokemon.damage + 10 }
  | _ => pokemon

def applyBurnBetweenTurns (pokemon : PokemonInPlay) (flipHeads : Bool) : PokemonInPlay :=
  match pokemon.status with
  | some .burned =>
    if flipHeads then { pokemon with status := none }
    else { pokemon with damage := pokemon.damage + 20 }
  | _ => pokemon

-- 56
theorem poison_adds_10 (pokemon : PokemonInPlay) (h : pokemon.status = some .poisoned) :
    (applyPoisonBetweenTurns pokemon).damage = pokemon.damage + 10 := by
  simp [applyPoisonBetweenTurns, h]

-- 57
theorem poison_preserves_status (pokemon : PokemonInPlay) (h : pokemon.status = some .poisoned) :
    (applyPoisonBetweenTurns pokemon).status = some .poisoned := by
  simp [applyPoisonBetweenTurns, h]

-- 58
theorem poison_preserves_energy (pokemon : PokemonInPlay) :
    (applyPoisonBetweenTurns pokemon).energy = pokemon.energy := by
  unfold applyPoisonBetweenTurns
  cases pokemon.status with
  | none => rfl
  | some s => cases s <;> rfl

-- 59
theorem poison_preserves_card (pokemon : PokemonInPlay) :
    (applyPoisonBetweenTurns pokemon).card = pokemon.card := by
  unfold applyPoisonBetweenTurns
  cases pokemon.status with
  | none => rfl
  | some s => cases s <;> rfl

-- 60
theorem no_poison_no_change (pokemon : PokemonInPlay) (h : pokemon.status ≠ some .poisoned) :
    applyPoisonBetweenTurns pokemon = pokemon := by
  unfold applyPoisonBetweenTurns
  cases hs : pokemon.status with
  | none => rfl
  | some s => cases s <;> simp_all

-- 61
theorem burn_heads_removes_status (pokemon : PokemonInPlay) (h : pokemon.status = some .burned) :
    (applyBurnBetweenTurns pokemon true).status = none := by
  simp [applyBurnBetweenTurns, h]

-- 62
theorem burn_tails_adds_20 (pokemon : PokemonInPlay) (h : pokemon.status = some .burned) :
    (applyBurnBetweenTurns pokemon false).damage = pokemon.damage + 20 := by
  simp [applyBurnBetweenTurns, h]

-- 63
theorem burn_tails_keeps_status (pokemon : PokemonInPlay) (h : pokemon.status = some .burned) :
    (applyBurnBetweenTurns pokemon false).status = some .burned := by
  simp [applyBurnBetweenTurns, h]

-- 64
theorem not_burned_no_burn_effect (pokemon : PokemonInPlay) (flip : Bool)
    (h : pokemon.status ≠ some .burned) :
    applyBurnBetweenTurns pokemon flip = pokemon := by
  unfold applyBurnBetweenTurns
  cases hs : pokemon.status with
  | none => rfl
  | some s => cases s <;> simp_all

-- 65
theorem burn_preserves_energy (pokemon : PokemonInPlay) (flip : Bool) :
    (applyBurnBetweenTurns pokemon flip).energy = pokemon.energy := by
  unfold applyBurnBetweenTurns
  cases hs : pokemon.status with
  | none => rfl
  | some s => cases s <;> simp <;> cases flip <;> rfl

-- 66
theorem burn_preserves_card (pokemon : PokemonInPlay) (flip : Bool) :
    (applyBurnBetweenTurns pokemon flip).card = pokemon.card := by
  unfold applyBurnBetweenTurns
  cases hs : pokemon.status with
  | none => rfl
  | some s => cases s <;> simp <;> cases flip <;> rfl

-- ============================================================================
-- TURN COUNTER PROPERTIES
-- ============================================================================

def nextTurn (ctx : TurnContext) : TurnContext :=
  { turnNumber := ctx.turnNumber + 1, isFirstPlayer := !ctx.isFirstPlayer }

-- 67
theorem nextTurn_increments (ctx : TurnContext) :
    (nextTurn ctx).turnNumber = ctx.turnNumber + 1 := rfl
-- 68
theorem nextTurn_swaps_player (ctx : TurnContext) :
    (nextTurn ctx).isFirstPlayer = !ctx.isFirstPlayer := rfl
-- 69
theorem nextTurn_gt (ctx : TurnContext) :
    ctx.turnNumber < (nextTurn ctx).turnNumber := by
  simp [nextTurn]
-- 70
theorem two_turns_later (ctx : TurnContext) :
    (nextTurn (nextTurn ctx)).turnNumber = ctx.turnNumber + 2 := by
  simp [nextTurn, Nat.add_assoc]

-- ============================================================================
-- DRAW PHASE
-- ============================================================================

def drawCard (player : PlayerState) : Option PlayerState :=
  match player.deck with
  | [] => none
  | c :: rest => some { player with deck := rest, hand := c :: player.hand }

-- 71
theorem drawCard_empty_deck (player : PlayerState) (h : player.deck = []) :
    drawCard player = none := by simp [drawCard, h]

-- 72
theorem drawCard_nonempty (player : PlayerState) (c : Card) (rest : List Card)
    (h : player.deck = c :: rest) :
    ∃ p', drawCard player = some p' :=
  ⟨{ player with deck := rest, hand := c :: player.hand }, by simp [drawCard, h]⟩

-- 73
theorem drawCard_preserves_bench (player : PlayerState) (p' : PlayerState)
    (h : drawCard player = some p') :
    p'.bench = player.bench := by
  cases hd : player.deck with
  | nil => simp [drawCard, hd] at h
  | cons c rest => simp [drawCard, hd] at h; subst h; rfl

-- 74
theorem drawCard_preserves_active (player : PlayerState) (p' : PlayerState)
    (h : drawCard player = some p') :
    p'.active = player.active := by
  cases hd : player.deck with
  | nil => simp [drawCard, hd] at h
  | cons c rest => simp [drawCard, hd] at h; subst h; rfl

-- 75
theorem drawCard_preserves_prizes (player : PlayerState) (p' : PlayerState)
    (h : drawCard player = some p') :
    p'.prizes = player.prizes := by
  cases hd : player.deck with
  | nil => simp [drawCard, hd] at h
  | cons c rest => simp [drawCard, hd] at h; subst h; rfl

-- 76
theorem drawCard_preserves_discard (player : PlayerState) (p' : PlayerState)
    (h : drawCard player = some p') :
    p'.discard = player.discard := by
  cases hd : player.deck with
  | nil => simp [drawCard, hd] at h
  | cons c rest => simp [drawCard, hd] at h; subst h; rfl

-- 77
theorem drawCard_total_cards_preserved (player : PlayerState) (p' : PlayerState)
    (h : drawCard player = some p') :
    p'.deck.length + p'.hand.length = player.deck.length + player.hand.length := by
  cases hd : player.deck with
  | nil => simp [drawCard, hd] at h
  | cons c rest => simp [drawCard, hd] at h; subst h; simp; omega

-- 78
theorem drawCard_deck_shrinks (player : PlayerState) (p' : PlayerState)
    (h : drawCard player = some p') :
    p'.deck.length + 1 = player.deck.length := by
  cases hd : player.deck with
  | nil => simp [drawCard, hd] at h
  | cons c rest => simp [drawCard, hd] at h; subst h; simp

end PokemonLean.TurnStructure
