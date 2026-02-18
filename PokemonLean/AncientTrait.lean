import PokemonLean.Basic

namespace PokemonLean.AncientTrait

open PokemonLean

-- ============================================================================
-- ANCIENT TRAIT RULES
-- ============================================================================

inductive TraitKind
  | omegaBarrage
  | alphaGrowth
  | deltaEvolution
  | thetaStop
  | thetaDouble
  deriving Repr, BEq, DecidableEq

def attackAllowance : TraitKind → Nat
  | .omegaBarrage => 2
  | _ => 1

def attachmentAllowance : TraitKind → Nat
  | .alphaGrowth => 2
  | _ => 1

def canEvolveSameTurn : TraitKind → Bool
  | .deltaEvolution => true
  | _ => false

def blocksOpponentAbilities : TraitKind → Bool
  | .thetaStop => true
  | _ => false

def toolCapacity : TraitKind → Nat
  | .thetaDouble => 2
  | _ => 1

def abilityCanAffect (trait : TraitKind) (fromOpponent : Bool) : Bool :=
  !(blocksOpponentAbilities trait && fromOpponent)

def canAttachTool (trait : TraitKind) (attachedCount : Nat) : Bool :=
  decide (attachedCount < toolCapacity trait)

@[simp] theorem attackAllowance_omegaBarrage : attackAllowance .omegaBarrage = 2 := rfl
@[simp] theorem attackAllowance_alphaGrowth : attackAllowance .alphaGrowth = 1 := rfl
@[simp] theorem attackAllowance_deltaEvolution : attackAllowance .deltaEvolution = 1 := rfl
@[simp] theorem attackAllowance_thetaStop : attackAllowance .thetaStop = 1 := rfl
@[simp] theorem attackAllowance_thetaDouble : attackAllowance .thetaDouble = 1 := rfl

theorem attackAllowance_pos (trait : TraitKind) : attackAllowance trait > 0 := by
  cases trait <;> decide

theorem attackAllowance_le_two (trait : TraitKind) : attackAllowance trait ≤ 2 := by
  cases trait <;> decide

theorem attackAllowance_eq_two_iff (trait : TraitKind) :
    attackAllowance trait = 2 ↔ trait = .omegaBarrage := by
  cases trait <;> simp [attackAllowance]

@[simp] theorem attachmentAllowance_omegaBarrage : attachmentAllowance .omegaBarrage = 1 := rfl
@[simp] theorem attachmentAllowance_alphaGrowth : attachmentAllowance .alphaGrowth = 2 := rfl
@[simp] theorem attachmentAllowance_deltaEvolution : attachmentAllowance .deltaEvolution = 1 := rfl
@[simp] theorem attachmentAllowance_thetaStop : attachmentAllowance .thetaStop = 1 := rfl
@[simp] theorem attachmentAllowance_thetaDouble : attachmentAllowance .thetaDouble = 1 := rfl

theorem attachmentAllowance_pos (trait : TraitKind) : attachmentAllowance trait > 0 := by
  cases trait <;> decide

theorem attachmentAllowance_le_two (trait : TraitKind) : attachmentAllowance trait ≤ 2 := by
  cases trait <;> decide

theorem attachmentAllowance_eq_two_iff (trait : TraitKind) :
    attachmentAllowance trait = 2 ↔ trait = .alphaGrowth := by
  cases trait <;> simp [attachmentAllowance]

@[simp] theorem canEvolveSameTurn_omegaBarrage : canEvolveSameTurn .omegaBarrage = false := rfl
@[simp] theorem canEvolveSameTurn_alphaGrowth : canEvolveSameTurn .alphaGrowth = false := rfl
@[simp] theorem canEvolveSameTurn_deltaEvolution : canEvolveSameTurn .deltaEvolution = true := rfl
@[simp] theorem canEvolveSameTurn_thetaStop : canEvolveSameTurn .thetaStop = false := rfl
@[simp] theorem canEvolveSameTurn_thetaDouble : canEvolveSameTurn .thetaDouble = false := rfl

theorem canEvolveSameTurn_true_iff (trait : TraitKind) :
    canEvolveSameTurn trait = true ↔ trait = .deltaEvolution := by
  cases trait <;> simp [canEvolveSameTurn]

@[simp] theorem blocksOpponentAbilities_omegaBarrage : blocksOpponentAbilities .omegaBarrage = false := rfl
@[simp] theorem blocksOpponentAbilities_alphaGrowth : blocksOpponentAbilities .alphaGrowth = false := rfl
@[simp] theorem blocksOpponentAbilities_deltaEvolution : blocksOpponentAbilities .deltaEvolution = false := rfl
@[simp] theorem blocksOpponentAbilities_thetaStop : blocksOpponentAbilities .thetaStop = true := rfl
@[simp] theorem blocksOpponentAbilities_thetaDouble : blocksOpponentAbilities .thetaDouble = false := rfl

theorem blocksOpponentAbilities_true_iff (trait : TraitKind) :
    blocksOpponentAbilities trait = true ↔ trait = .thetaStop := by
  cases trait <;> simp [blocksOpponentAbilities]

@[simp] theorem toolCapacity_omegaBarrage : toolCapacity .omegaBarrage = 1 := rfl
@[simp] theorem toolCapacity_alphaGrowth : toolCapacity .alphaGrowth = 1 := rfl
@[simp] theorem toolCapacity_deltaEvolution : toolCapacity .deltaEvolution = 1 := rfl
@[simp] theorem toolCapacity_thetaStop : toolCapacity .thetaStop = 1 := rfl
@[simp] theorem toolCapacity_thetaDouble : toolCapacity .thetaDouble = 2 := rfl

theorem toolCapacity_pos (trait : TraitKind) : toolCapacity trait > 0 := by
  cases trait <;> decide

theorem toolCapacity_le_two (trait : TraitKind) : toolCapacity trait ≤ 2 := by
  cases trait <;> decide

theorem toolCapacity_eq_two_iff (trait : TraitKind) :
    toolCapacity trait = 2 ↔ trait = .thetaDouble := by
  cases trait <;> simp [toolCapacity]

@[simp] theorem abilityCanAffect_thetaStop_opponent :
    abilityCanAffect .thetaStop true = false := by
  simp [abilityCanAffect]

@[simp] theorem abilityCanAffect_thetaStop_self :
    abilityCanAffect .thetaStop false = true := by
  simp [abilityCanAffect]

@[simp] theorem abilityCanAffect_omegaBarrage_opponent :
    abilityCanAffect .omegaBarrage true = true := by
  simp [abilityCanAffect]

theorem abilityCanAffect_false_iff (trait : TraitKind) (fromOpponent : Bool) :
    abilityCanAffect trait fromOpponent = false ↔
      blocksOpponentAbilities trait = true ∧ fromOpponent = true := by
  cases trait <;> cases fromOpponent <;> simp [abilityCanAffect, blocksOpponentAbilities]

theorem canAttachTool_true_iff (trait : TraitKind) (attachedCount : Nat) :
    canAttachTool trait attachedCount = true ↔ attachedCount < toolCapacity trait := by
  simp [canAttachTool]

theorem canAttachTool_false_iff (trait : TraitKind) (attachedCount : Nat) :
    canAttachTool trait attachedCount = false ↔ toolCapacity trait ≤ attachedCount := by
  simp [canAttachTool]

@[simp] theorem canAttachTool_thetaDouble_one :
    canAttachTool .thetaDouble 1 = true := by
  simp [canAttachTool, toolCapacity]

@[simp] theorem canAttachTool_thetaDouble_two :
    canAttachTool .thetaDouble 2 = false := by
  simp [canAttachTool, toolCapacity]

@[simp] theorem canAttachTool_regular_one :
    canAttachTool .omegaBarrage 1 = false := by
  simp [canAttachTool, toolCapacity]

-- ============================================================================
-- BREAK EVOLUTION (RETAIN PREVIOUS ATTACKS)
-- ============================================================================

structure BreakEvolution where
  baseCard : Card
  breakCard : Card
  deriving Repr, BEq, DecidableEq

def evolveToBreak (baseCard breakCard : Card) : BreakEvolution :=
  { baseCard := baseCard, breakCard := breakCard }

def breakAttacks (evo : BreakEvolution) : List Attack :=
  evo.baseCard.attacks ++ evo.breakCard.attacks

def breakAttackCount (evo : BreakEvolution) : Nat :=
  (breakAttacks evo).length

@[simp] theorem evolveToBreak_baseCard (baseCard breakCard : Card) :
    (evolveToBreak baseCard breakCard).baseCard = baseCard := rfl

@[simp] theorem evolveToBreak_breakCard (baseCard breakCard : Card) :
    (evolveToBreak baseCard breakCard).breakCard = breakCard := rfl

theorem breakAttackCount_eq (evo : BreakEvolution) :
    breakAttackCount evo = evo.baseCard.attacks.length + evo.breakCard.attacks.length := by
  simp [breakAttackCount, breakAttacks]

theorem breakRetainsBaseAttack (evo : BreakEvolution) (attack : Attack)
    (hMem : attack ∈ evo.baseCard.attacks) :
    attack ∈ breakAttacks evo := by
  exact List.mem_append.mpr (Or.inl hMem)

theorem breakIncludesBreakAttack (evo : BreakEvolution) (attack : Attack)
    (hMem : attack ∈ evo.breakCard.attacks) :
    attack ∈ breakAttacks evo := by
  exact List.mem_append.mpr (Or.inr hMem)

theorem breakRetainsAllBaseAttacks (evo : BreakEvolution) :
    ∀ attack ∈ evo.baseCard.attacks, attack ∈ breakAttacks evo := by
  intro attack hMem
  exact breakRetainsBaseAttack evo attack hMem

theorem breakAttackCount_ge_base (evo : BreakEvolution) :
    evo.baseCard.attacks.length ≤ breakAttackCount evo := by
  simp [breakAttackCount, breakAttacks]

theorem breakAttackCount_ge_break (evo : BreakEvolution) :
    evo.breakCard.attacks.length ≤ breakAttackCount evo := by
  simp [breakAttackCount, breakAttacks]

@[simp] theorem breakAttacks_when_break_has_no_attacks (evo : BreakEvolution)
    (h : evo.breakCard.attacks = []) :
    breakAttacks evo = evo.baseCard.attacks := by
  simp [breakAttacks, h]

@[simp] theorem breakAttacks_when_base_has_no_attacks (evo : BreakEvolution)
    (h : evo.baseCard.attacks = []) :
    breakAttacks evo = evo.breakCard.attacks := by
  simp [breakAttacks, h]

-- ============================================================================
-- PRISM STAR DECK RULES + LOST ZONE DESTINATION
-- ============================================================================

structure PrismStarCard where
  card : Card
  deriving Repr, BEq, DecidableEq

def prismStarCountByName (deck : List PrismStarCard) (name : String) : Nat :=
  deck.countP (fun c => c.card.name == name)

def prismStarDeckLegal (deck : List PrismStarCard) : Prop :=
  ∀ name : String, prismStarCountByName deck name ≤ 1

@[simp] theorem prismStarCountByName_nil (name : String) :
    prismStarCountByName [] name = 0 := by
  simp [prismStarCountByName]

@[simp] theorem prismStarCountByName_cons (c : PrismStarCard) (deck : List PrismStarCard) (name : String) :
    prismStarCountByName (c :: deck) name =
      (if c.card.name == name then 1 else 0) + prismStarCountByName deck name := by
  simp [prismStarCountByName, List.countP_cons, Nat.add_comm]

theorem prismStarCountByName_le_length (deck : List PrismStarCard) (name : String) :
    prismStarCountByName deck name ≤ deck.length := by
  simpa [prismStarCountByName] using
    (List.countP_le_length (p := fun c : PrismStarCard => c.card.name == name) (l := deck))

theorem prismStarDeckLegal_nil : prismStarDeckLegal [] := by
  intro name
  simp

theorem prismStarDeckLegal_singleton (c : PrismStarCard) : prismStarDeckLegal [c] := by
  intro name
  by_cases h : c.card.name == name <;> simp [prismStarCountByName, h]

theorem prismStarDeckLegal_iff (deck : List PrismStarCard) :
    prismStarDeckLegal deck ↔ ∀ name : String, prismStarCountByName deck name ≤ 1 := Iff.rfl

structure LostZone where
  cards : List Card
  deriving Repr, BEq, DecidableEq

structure DiscardPile where
  cards : List Card
  deriving Repr, BEq, DecidableEq

def emptyLostZone : LostZone := { cards := [] }
def emptyDiscardPile : DiscardPile := { cards := [] }

def sendToLostZone (lostZone : LostZone) (card : Card) : LostZone :=
  { cards := card :: lostZone.cards }

def sendToDiscardPile (discardPile : DiscardPile) (card : Card) : DiscardPile :=
  { cards := card :: discardPile.cards }

def discardWithPrismRule (lostZone : LostZone) (discardPile : DiscardPile)
    (card : Card) (isPrismStar : Bool) : LostZone × DiscardPile :=
  if isPrismStar then
    (sendToLostZone lostZone card, discardPile)
  else
    (lostZone, sendToDiscardPile discardPile card)

def lostZoneCount (lostZone : LostZone) : Nat := lostZone.cards.length
def discardPileCount (discardPile : DiscardPile) : Nat := discardPile.cards.length

def inLostZone (lostZone : LostZone) (card : Card) : Bool :=
  lostZone.cards.any (· == card)

def inDiscardPile (discardPile : DiscardPile) (card : Card) : Bool :=
  discardPile.cards.any (· == card)

@[simp] theorem emptyLostZone_count : lostZoneCount emptyLostZone = 0 := by
  rfl

@[simp] theorem emptyDiscardPile_count : discardPileCount emptyDiscardPile = 0 := by
  rfl

@[simp] theorem sendToLostZone_count (lostZone : LostZone) (card : Card) :
    lostZoneCount (sendToLostZone lostZone card) = lostZoneCount lostZone + 1 := by
  simp [sendToLostZone, lostZoneCount]

@[simp] theorem sendToDiscardPile_count (discardPile : DiscardPile) (card : Card) :
    discardPileCount (sendToDiscardPile discardPile card) = discardPileCount discardPile + 1 := by
  simp [sendToDiscardPile, discardPileCount]

theorem discardWithPrismRule_prism_lostCount (lostZone : LostZone) (discardPile : DiscardPile) (card : Card) :
    lostZoneCount (discardWithPrismRule lostZone discardPile card true).1 =
      lostZoneCount lostZone + 1 := by
  simp [discardWithPrismRule]

theorem discardWithPrismRule_prism_discardUnchanged
    (lostZone : LostZone) (discardPile : DiscardPile) (card : Card) :
    (discardWithPrismRule lostZone discardPile card true).2 = discardPile := by
  simp [discardWithPrismRule]

theorem discardWithPrismRule_nonprism_lostUnchanged
    (lostZone : LostZone) (discardPile : DiscardPile) (card : Card) :
    (discardWithPrismRule lostZone discardPile card false).1 = lostZone := by
  simp [discardWithPrismRule]

theorem discardWithPrismRule_nonprism_discardCount
    (lostZone : LostZone) (discardPile : DiscardPile) (card : Card) :
    discardPileCount (discardWithPrismRule lostZone discardPile card false).2 =
      discardPileCount discardPile + 1 := by
  simp [discardWithPrismRule]

theorem discardWithPrismRule_prism_inLostZone
    (lostZone : LostZone) (discardPile : DiscardPile) (card : Card) :
    inLostZone (discardWithPrismRule lostZone discardPile card true).1 card = true := by sorry

theorem discardWithPrismRule_nonprism_inDiscardPile
    (lostZone : LostZone) (discardPile : DiscardPile) (card : Card) :
    inDiscardPile (discardWithPrismRule lostZone discardPile card false).2 card = true := by sorry

-- ============================================================================
-- RADIANT POKEMON DECK RULE (AT MOST ONE)
-- ============================================================================

structure DeckPokemonCard where
  card : Card
  isRadiant : Bool := false
  deriving Repr, BEq, DecidableEq

def radiantCount (deck : List DeckPokemonCard) : Nat :=
  deck.countP (fun c => c.isRadiant)

def radiantDeckLegal (deck : List DeckPokemonCard) : Prop :=
  radiantCount deck ≤ 1

@[simp] theorem radiantCount_nil : radiantCount [] = 0 := by
  simp [radiantCount]

@[simp] theorem radiantCount_cons (c : DeckPokemonCard) (deck : List DeckPokemonCard) :
    radiantCount (c :: deck) = (if c.isRadiant then 1 else 0) + radiantCount deck := by
  simp [radiantCount, List.countP_cons, Nat.add_comm]

theorem radiantCount_le_length (deck : List DeckPokemonCard) : radiantCount deck ≤ deck.length := by
  simpa [radiantCount] using
    (List.countP_le_length (p := fun c : DeckPokemonCard => c.isRadiant) (l := deck))

theorem radiantDeckLegal_nil : radiantDeckLegal [] := by
  simp [radiantDeckLegal]

theorem radiantDeckLegal_singleton_radiant (c : DeckPokemonCard) (h : c.isRadiant = true) :
    radiantDeckLegal [c] := by
  simp [radiantDeckLegal, radiantCount, h]

theorem radiantDeckLegal_singleton_nonradiant (c : DeckPokemonCard) (h : c.isRadiant = false) :
    radiantDeckLegal [c] := by
  simp [radiantDeckLegal, radiantCount, h]

theorem radiantDeckLegal_iff (deck : List DeckPokemonCard) :
    radiantDeckLegal deck ↔ radiantCount deck ≤ 1 := Iff.rfl

-- ============================================================================
-- TAG TEAM GX ATTACKS (BONUS EFFECT WITH EXTRA ENERGY)
-- ============================================================================

structure TagTeamGXAttack where
  attack : Attack
  bonusEnergyRequired : Nat
  bonusDamage : Nat := 0
  deriving Repr, BEq, DecidableEq

def hasBonusEffect (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat) : Bool :=
  decide (gxAttack.bonusEnergyRequired ≤ attachedEnergy)

structure TagTeamGXResult where
  damage : Nat
  extraEffectApplied : Bool
  deriving Repr, BEq, DecidableEq

def resolveTagTeamGXAttack (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat) : TagTeamGXResult :=
  if hasBonusEffect gxAttack attachedEnergy then
    { damage := gxAttack.attack.baseDamage + gxAttack.bonusDamage
      extraEffectApplied := true }
  else
    { damage := gxAttack.attack.baseDamage
      extraEffectApplied := false }

theorem hasBonusEffect_true_iff (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat) :
    hasBonusEffect gxAttack attachedEnergy = true ↔ gxAttack.bonusEnergyRequired ≤ attachedEnergy := by
  simp [hasBonusEffect]

theorem hasBonusEffect_false_iff (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat) :
    hasBonusEffect gxAttack attachedEnergy = false ↔ ¬ gxAttack.bonusEnergyRequired ≤ attachedEnergy := by
  simp [hasBonusEffect]

theorem resolveTagTeamGXAttack_bonus_damage
    (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat)
    (h : gxAttack.bonusEnergyRequired ≤ attachedEnergy) :
    (resolveTagTeamGXAttack gxAttack attachedEnergy).damage =
      gxAttack.attack.baseDamage + gxAttack.bonusDamage := by
  have hBonus : hasBonusEffect gxAttack attachedEnergy = true := by
    simp [hasBonusEffect, h]
  simp [resolveTagTeamGXAttack, hBonus]

theorem resolveTagTeamGXAttack_base_damage
    (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat)
    (h : attachedEnergy < gxAttack.bonusEnergyRequired) :
    (resolveTagTeamGXAttack gxAttack attachedEnergy).damage =
      gxAttack.attack.baseDamage := by
  have hBonus : hasBonusEffect gxAttack attachedEnergy = false := by
    simp [hasBonusEffect, Nat.not_le.mpr h]
  simp [resolveTagTeamGXAttack, hBonus]

theorem resolveTagTeamGXAttack_bonus_flag_true
    (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat)
    (h : gxAttack.bonusEnergyRequired ≤ attachedEnergy) :
    (resolveTagTeamGXAttack gxAttack attachedEnergy).extraEffectApplied = true := by
  have hBonus : hasBonusEffect gxAttack attachedEnergy = true := by
    simp [hasBonusEffect, h]
  simp [resolveTagTeamGXAttack, hBonus]

theorem resolveTagTeamGXAttack_bonus_flag_false
    (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat)
    (h : attachedEnergy < gxAttack.bonusEnergyRequired) :
    (resolveTagTeamGXAttack gxAttack attachedEnergy).extraEffectApplied = false := by
  have hBonus : hasBonusEffect gxAttack attachedEnergy = false := by
    simp [hasBonusEffect, Nat.not_le.mpr h]
  simp [resolveTagTeamGXAttack, hBonus]

theorem resolveTagTeamGXAttack_damage_ge_base
    (gxAttack : TagTeamGXAttack) (attachedEnergy : Nat) :
    gxAttack.attack.baseDamage ≤ (resolveTagTeamGXAttack gxAttack attachedEnergy).damage := by
  cases hBonus : hasBonusEffect gxAttack attachedEnergy <;>
    simp [resolveTagTeamGXAttack, hBonus]

theorem hasBonusEffect_monotone (gxAttack : TagTeamGXAttack) {e₁ e₂ : Nat}
    (hLe : e₁ ≤ e₂) (hBonus : hasBonusEffect gxAttack e₁ = true) :
    hasBonusEffect gxAttack e₂ = true := by
  have hReq : gxAttack.bonusEnergyRequired ≤ e₁ :=
    (hasBonusEffect_true_iff gxAttack e₁).1 hBonus
  exact (hasBonusEffect_true_iff gxAttack e₂).2 (Nat.le_trans hReq hLe)

structure TagTeamGXUsage where
  used : Bool := false
  deriving Repr, BEq, DecidableEq

def freshTagTeamGXUsage : TagTeamGXUsage := { used := false }

def canUseTagTeamGX (usage : TagTeamGXUsage) : Bool :=
  !usage.used

def markTagTeamGXUsed (usage : TagTeamGXUsage) : TagTeamGXUsage :=
  { usage with used := true }

def useTagTeamGX (usage : TagTeamGXUsage) : Option TagTeamGXUsage :=
  if usage.used then none else some (markTagTeamGXUsed usage)

@[simp] theorem freshTagTeamGXUsage_unused : freshTagTeamGXUsage.used = false := rfl

@[simp] theorem canUseTagTeamGX_fresh : canUseTagTeamGX freshTagTeamGXUsage = true := by
  simp [canUseTagTeamGX, freshTagTeamGXUsage]

@[simp] theorem markTagTeamGXUsed_sets_flag (usage : TagTeamGXUsage) :
    (markTagTeamGXUsed usage).used = true := by
  simp [markTagTeamGXUsed]

theorem useTagTeamGX_none_when_used (usage : TagTeamGXUsage) (h : usage.used = true) :
    useTagTeamGX usage = none := by
  simp [useTagTeamGX, h]

theorem useTagTeamGX_some_when_unused (usage : TagTeamGXUsage) (h : usage.used = false) :
    useTagTeamGX usage = some (markTagTeamGXUsed usage) := by
  simp [useTagTeamGX, h]

theorem useTagTeamGX_marks_used (usage next : TagTeamGXUsage)
    (h : useTagTeamGX usage = some next) :
    next.used = true := by
  by_cases hUsed : usage.used
  · simp [useTagTeamGX, hUsed] at h
  · simp [useTagTeamGX, hUsed] at h
    cases h
    simp [markTagTeamGXUsed]

theorem useTagTeamGX_twice_none (usage next : TagTeamGXUsage)
    (h : useTagTeamGX usage = some next) :
    useTagTeamGX next = none := by
  have hUsed : next.used = true := useTagTeamGX_marks_used usage next h
  simp [useTagTeamGX, hUsed]

theorem canUseTagTeamGX_after_success (usage next : TagTeamGXUsage)
    (h : useTagTeamGX usage = some next) :
    canUseTagTeamGX next = false := by
  have hUsed : next.used = true := useTagTeamGX_marks_used usage next h
  simp [canUseTagTeamGX, hUsed]

end PokemonLean.AncientTrait
