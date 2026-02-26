import PokemonLean.Core.Types

namespace PokemonLean.CardEffects

open PokemonLean.Core.Types

/-! # Iconic Pokémon TCG Card Effects

Formalizations of six iconic Pokémon TCG card effects as state transitions,
with correctness proofs and card conservation. Zero sorry, zero admit, zero axiom.
-/

/-- Helper constructor for concrete trainer cards. -/
def mkTrainerCard (name text : String) : Card :=
  { name := name
    kind := .trainer
    pokemon := none
    energyType := none
    hp := 0
    stage := none
    attacks := []
    weakness := none
    resistance := none
    retreatCost := 0
    ruleBox := .none
    evolvesFrom := none
    abilityText := none
    effectText := text
    setCode := none
    setNumber := none
    regulationMark := none
    isBasicEnergy := false }

-- ═══════════════════════════════════════════════════════════════
-- Card definitions
-- ═══════════════════════════════════════════════════════════════

def professorsResearchCard : Card :=
  mkTrainerCard "Professor's Research" "Discard your hand, then draw 7 cards."

def bossesOrdersCard : Card :=
  mkTrainerCard "Boss's Orders" "Switch in 1 of your opponent's Benched Pokemon to the Active Spot."

def switchCard : Card :=
  mkTrainerCard "Switch" "Switch your Active Pokemon with 1 of your Benched Pokemon."

def rareCandyCard : Card :=
  mkTrainerCard "Rare Candy"
    "Choose 1 of your Basic Pokemon in play. Evolve it to Stage 2, skipping Stage 1."

def superPotionCard : Card :=
  mkTrainerCard "Super Potion"
    "Heal 60 damage from 1 of your Pokemon. If you do, discard an Energy from it."

def ultraBallCard : Card :=
  mkTrainerCard "Ultra Ball"
    "Discard 2 cards from your hand. Search your deck for a Pokemon and put it into your hand."

-- ═══════════════════════════════════════════════════════════════
-- Card counting infrastructure
-- ═══════════════════════════════════════════════════════════════

/-- Count Pokemon currently in play for one player. -/
def inPlayCount (p : PlayerState) : Nat :=
  (if p.active.isSome then 1 else 0) + p.bench.length

/-- Count all cards in a player's zones. -/
def playerCardCount (p : PlayerState) : Nat :=
  p.hand.length + p.deck.length + p.discard.length +
  p.prizes.length + p.lostZone.length + inPlayCount p

-- ═══════════════════════════════════════════════════════════════
-- List helpers
-- ═══════════════════════════════════════════════════════════════

def removeFirst? {α : Type} [DecidableEq α] (x : α) : List α → Option (List α)
  | [] => none
  | head :: tail =>
      if head = x then some tail
      else match removeFirst? x tail with
           | none => none
           | some rest => some (head :: rest)

theorem removeFirst?_length {α : Type} [DecidableEq α] (x : α) :
    ∀ (xs ys : List α), removeFirst? x xs = some ys → ys.length + 1 = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; simp [removeFirst?] at h
  | cons head tail ih =>
      intro ys h
      simp only [removeFirst?] at h
      by_cases heq : head = x
      · simp [heq] at h; subst h; simp
      · simp [heq] at h
        cases hRec : removeFirst? x tail with
        | none => simp [hRec] at h
        | some rest =>
            simp [hRec] at h; subst h
            have := ih rest hRec; simp; omega

def removeAt? {α : Type} : List α → Nat → Option (α × List α)
  | [], _ => none
  | x :: xs, 0 => some (x, xs)
  | x :: xs, n + 1 =>
      match removeAt? xs n with
      | none => none
      | some (removed, rest) => some (removed, x :: rest)

theorem removeAt?_length {α : Type} :
    ∀ (xs : List α) (idx : Nat) (removed : α) (rest : List α),
      removeAt? xs idx = some (removed, rest) → rest.length + 1 = xs.length := by
  intro xs
  induction xs with
  | nil => intro idx _ _ h; cases idx <;> simp [removeAt?] at h
  | cons head tail ih =>
      intro idx removed rest h
      cases idx with
      | zero =>
          simp [removeAt?] at h
          obtain ⟨_, rfl⟩ := h; simp
      | succ n =>
          simp [removeAt?] at h
          cases hRec : removeAt? tail n with
          | none => simp [hRec] at h
          | some pair =>
              simp [hRec] at h
              obtain ⟨rfl, rfl⟩ := h
              have := ih n pair.1 pair.2 hRec
              simp; omega

-- ═══════════════════════════════════════════════════════════════
-- (1) PROFESSOR'S RESEARCH
-- Discard your hand, draw 7 cards from deck.
-- ═══════════════════════════════════════════════════════════════

/-- Professor's Research effect on a player state. -/
def professorsResearchEffect (p : PlayerState) : PlayerState :=
  let drawCount := min 7 p.deck.length
  { p with
    hand := p.deck.take drawCount
    deck := p.deck.drop drawCount
    discard := p.hand ++ p.discard
    supporterPlayed := true }

theorem professorsResearch_hand_size (p : PlayerState) :
    (professorsResearchEffect p).hand.length = min 7 p.deck.length := by
  simp [professorsResearchEffect, List.length_take]

theorem professorsResearchEffect_preserves_cards (p : PlayerState) :
    playerCardCount (professorsResearchEffect p) = playerCardCount p := by
  unfold professorsResearchEffect playerCardCount inPlayCount
  simp [List.length_take, List.length_drop, List.length_append]
  omega

-- ═══════════════════════════════════════════════════════════════
-- Switching helper (shared by Boss's Orders and Switch)
-- ═══════════════════════════════════════════════════════════════

/-- Switch active with benched Pokémon at given index. -/
def switchWithBench (p : PlayerState) (idx : Nat) : PlayerState :=
  match p.active with
  | none => p
  | some oldActive =>
      match removeAt? p.bench idx with
      | none => p
      | some (promoted, rest) =>
          { p with active := some promoted, bench := oldActive :: rest }

theorem switchWithBench_preserves_inPlay (p : PlayerState) (idx : Nat) :
    inPlayCount (switchWithBench p idx) = inPlayCount p := by
  unfold switchWithBench
  cases hA : p.active with
  | none => rfl
  | some oldActive =>
      cases hR : removeAt? p.bench idx with
      | none => rfl
      | some pair =>
          have hLen := removeAt?_length p.bench idx pair.1 pair.2 hR
          simp [inPlayCount, hA, hR]; omega

theorem switchWithBench_preserves_cards (p : PlayerState) (idx : Nat) :
    playerCardCount (switchWithBench p idx) = playerCardCount p := by
  unfold switchWithBench playerCardCount
  cases hA : p.active with
  | none => rfl
  | some oldActive =>
      cases hR : removeAt? p.bench idx with
      | none => rfl
      | some pair =>
          have hLen := removeAt?_length p.bench idx pair.1 pair.2 hR
          simp [inPlayCount, hA, hR]; omega

-- ═══════════════════════════════════════════════════════════════
-- (2) BOSS'S ORDERS
-- Switch opponent's active with one of their benched Pokémon.
-- ═══════════════════════════════════════════════════════════════

theorem bossesOrders_opponent_active_changes (p : PlayerState) (benchIdx : Nat)
    (oldActive promoted : Pokemon) (rest : List Pokemon)
    (hActive : p.active = some oldActive)
    (hRemove : removeAt? p.bench benchIdx = some (promoted, rest))
    (hDiff : promoted ≠ oldActive) :
    (switchWithBench p benchIdx).active ≠ p.active := by
  simp [switchWithBench, hActive, hRemove]
  exact hDiff

theorem bossesOrders_bench_decreases (bench : List Pokemon) (benchIdx : Nat)
    (promoted : Pokemon) (rest : List Pokemon)
    (hRemove : removeAt? bench benchIdx = some (promoted, rest)) :
    rest.length + 1 = bench.length :=
  removeAt?_length _ _ _ _ hRemove

theorem bossesOrders_conserves_cards (p : PlayerState) (benchIdx : Nat) :
    playerCardCount (switchWithBench p benchIdx) = playerCardCount p :=
  switchWithBench_preserves_cards p benchIdx

-- ═══════════════════════════════════════════════════════════════
-- (3) SWITCH
-- Switch your active with one of your benched Pokémon.
-- ═══════════════════════════════════════════════════════════════

theorem switch_active_changes (p : PlayerState) (benchIdx : Nat)
    (oldActive promoted : Pokemon) (rest : List Pokemon)
    (hActive : p.active = some oldActive)
    (hRemove : removeAt? p.bench benchIdx = some (promoted, rest))
    (hDiff : promoted ≠ oldActive) :
    (switchWithBench p benchIdx).active ≠ p.active := by
  simp [switchWithBench, hActive, hRemove]
  exact hDiff

theorem switch_conserves_cards (p : PlayerState) (benchIdx : Nat) :
    playerCardCount (switchWithBench p benchIdx) = playerCardCount p :=
  switchWithBench_preserves_cards p benchIdx

theorem switch_preserves_pokemon_count (p : PlayerState) (benchIdx : Nat) :
    inPlayCount (switchWithBench p benchIdx) = inPlayCount p :=
  switchWithBench_preserves_inPlay p benchIdx

-- ═══════════════════════════════════════════════════════════════
-- (4) RARE CANDY
-- Evolve Basic directly to Stage 2, skipping Stage 1.
-- ═══════════════════════════════════════════════════════════════

/-- Convert a Pokemon back to a Card for discard pile. -/
def pokemonToCard (mon : Pokemon) : Card :=
  { name := mon.name, kind := .pokemon, pokemon := some mon,
    energyType := some mon.energyType, hp := mon.hp, stage := some mon.stage,
    attacks := mon.attacks, weakness := mon.weakness, resistance := mon.resistance,
    retreatCost := mon.retreatCost, ruleBox := mon.ruleBox, evolvesFrom := mon.evolvesFrom,
    abilityText := mon.abilityText, effectText := mon.effectText,
    setCode := none, setNumber := none, regulationMark := none, isBasicEnergy := false }

/-- Rare Candy: evolve active Basic directly to Stage 2. -/
def rareCandyEffect (p : PlayerState) (stage2Card : Card) : PlayerState :=
  match p.active, stage2Card.pokemon, stage2Card.stage with
  | some basic, some evolved, some .stage2 =>
      if basic.stage = .basic then
        match removeFirst? stage2Card p.hand with
        | none => p
        | some hand' =>
            { p with
              hand := hand'
              active := some { evolved with stage := .stage2 }
              discard := pokemonToCard basic :: p.discard }
      else p
  | _, _, _ => p

theorem rareCandy_stage_is_stage2 (p : PlayerState) (stage2Card : Card)
    (basic evolved : Pokemon) (newHand : List Card)
    (hActive : p.active = some basic)
    (hPoke : stage2Card.pokemon = some evolved)
    (hStage : stage2Card.stage = some Stage.stage2)
    (hBasic : basic.stage = .basic)
    (hRemove : removeFirst? stage2Card p.hand = some newHand) :
    ((rareCandyEffect p stage2Card).active).map Pokemon.stage = some Stage.stage2 := by
  simp [rareCandyEffect, hActive, hPoke, hStage, hBasic, hRemove]

theorem rareCandy_basic_no_longer_active (p : PlayerState) (stage2Card : Card)
    (basic evolved : Pokemon) (newHand : List Card)
    (hActive : p.active = some basic)
    (hPoke : stage2Card.pokemon = some evolved)
    (hStage : stage2Card.stage = some Stage.stage2)
    (hBasic : basic.stage = .basic)
    (hRemove : removeFirst? stage2Card p.hand = some newHand)
    (hNotEvolved : { evolved with stage := Stage.stage2 } ≠ basic) :
    (rareCandyEffect p stage2Card).active ≠ some basic := by
  simp [rareCandyEffect, hActive, hPoke, hStage, hBasic, hRemove]
  exact hNotEvolved

theorem rareCandyEffect_preserves_cards (p : PlayerState) (stage2Card : Card) :
    playerCardCount (rareCandyEffect p stage2Card) = playerCardCount p := by
  unfold rareCandyEffect
  cases hA : p.active with
  | none => rfl
  | some basic =>
      cases hP : stage2Card.pokemon with
      | none => rfl
      | some evolved =>
          cases hSt : stage2Card.stage with
          | none => rfl
          | some st =>
              cases st <;> try rfl
              -- stage2 case
              by_cases hB : basic.stage = Stage.basic
              · simp only [hB, ↓reduceIte]
                cases hR : removeFirst? stage2Card p.hand with
                | none => rfl
                | some hand' =>
                    have hLen := removeFirst?_length stage2Card p.hand hand' hR
                    simp [playerCardCount, inPlayCount, hA]; omega
              · simp [hB]

-- ═══════════════════════════════════════════════════════════════
-- (5) SUPER POTION
-- Heal 60 damage, discard an energy.
-- ═══════════════════════════════════════════════════════════════

/-- Super Potion: heal 60 damage, discard an energy from active. -/
def superPotionEffect (p : PlayerState) : PlayerState :=
  match p.active with
  | none => p
  | some active =>
      match active.attachedEnergy with
      | [] => p
      | _ :: remaining =>
          let healAmt := min 60 active.damage
          { p with active := some { active with
              damage := active.damage - healAmt
              attachedEnergy := remaining } }

theorem superPotion_damage_decreases (p : PlayerState)
    (active : Pokemon) (e : EnergyType) (rest : List EnergyType)
    (hActive : p.active = some active)
    (hEnergy : active.attachedEnergy = e :: rest) :
    ((superPotionEffect p).active).map Pokemon.damage =
      some (active.damage - min 60 active.damage) := by
  simp [superPotionEffect, hActive, hEnergy]

theorem superPotion_energy_count_decreases (p : PlayerState)
    (active : Pokemon) (e : EnergyType) (rest : List EnergyType)
    (hActive : p.active = some active)
    (hEnergy : active.attachedEnergy = e :: rest) :
    ((superPotionEffect p).active).map (fun m => m.attachedEnergy.length) =
      some rest.length := by
  simp [superPotionEffect, hActive, hEnergy]

theorem superPotionEffect_preserves_cards (p : PlayerState) :
    playerCardCount (superPotionEffect p) = playerCardCount p := by
  simp only [superPotionEffect]
  cases hA : p.active with
  | none => rfl
  | some active =>
      simp only [hA]
      cases hE : active.attachedEnergy with
      | nil => rfl
      | cons _ _ => simp [playerCardCount, inPlayCount, hA]

-- ═══════════════════════════════════════════════════════════════
-- (6) ULTRA BALL
-- Discard 2 from hand, search deck for a Pokémon.
-- ═══════════════════════════════════════════════════════════════

/-- Ultra Ball: discard 2 from hand, search deck for a Pokemon card. -/
def ultraBallEffect (p : PlayerState) (d1 d2 target : Card) : PlayerState :=
  if target.kind ≠ .pokemon then p
  else match removeFirst? d1 p.hand with
  | none => p
  | some h1 =>
      match removeFirst? d2 h1 with
      | none => p
      | some h2 =>
          match removeFirst? target p.deck with
          | none => p
          | some dk =>
              { p with
                hand := target :: h2
                deck := dk
                discard := d1 :: d2 :: p.discard }

theorem ultraBall_hand_delta (p : PlayerState) (d1 d2 target : Card)
    (h1 h2 dk : List Card)
    (hKind : target.kind = .pokemon)
    (hR1 : removeFirst? d1 p.hand = some h1)
    (hR2 : removeFirst? d2 h1 = some h2)
    (hS : removeFirst? target p.deck = some dk) :
    (ultraBallEffect p d1 d2 target).hand.length + 1 = p.hand.length := by
  have l1 := removeFirst?_length d1 p.hand h1 hR1
  have l2 := removeFirst?_length d2 h1 h2 hR2
  simp [ultraBallEffect, hKind, hR1, hR2, hS]
  omega

theorem ultraBall_deck_delta (p : PlayerState) (d1 d2 target : Card)
    (h1 h2 dk : List Card)
    (hKind : target.kind = .pokemon)
    (hR1 : removeFirst? d1 p.hand = some h1)
    (hR2 : removeFirst? d2 h1 = some h2)
    (hS : removeFirst? target p.deck = some dk) :
    (ultraBallEffect p d1 d2 target).deck.length + 1 = p.deck.length := by
  have l := removeFirst?_length target p.deck dk hS
  simp [ultraBallEffect, hKind, hR1, hR2, hS]
  omega

theorem ultraBallEffect_preserves_cards (p : PlayerState) (d1 d2 target : Card) :
    playerCardCount (ultraBallEffect p d1 d2 target) = playerCardCount p := by
  simp only [ultraBallEffect]
  by_cases hKind : target.kind ≠ .pokemon
  · simp [hKind]
  · have hK : target.kind = .pokemon := by
      cases h : target.kind <;> simp_all
    simp only [hK, ne_eq, not_true_eq_false, ↓reduceIte]
    cases hR1 : removeFirst? d1 p.hand with
    | none => simp [hR1]
    | some h1 =>
        simp only [hR1]
        cases hR2 : removeFirst? d2 h1 with
        | none => simp [hR2]
        | some h2 =>
            simp only [hR2]
            cases hS : removeFirst? target p.deck with
            | none => simp [hS]
            | some dk =>
                have l1 := removeFirst?_length d1 p.hand h1 hR1
                have l2 := removeFirst?_length d2 h1 h2 hR2
                have l3 := removeFirst?_length target p.deck dk hS
                simp [playerCardCount, inPlayCount, hS]; omega

end PokemonLean.CardEffects
