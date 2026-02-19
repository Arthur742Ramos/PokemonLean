-- Advanced Game Theory and Strategy
-- PokemonLean: N-Ply Solver, Lethal Detection, Expected Damage

import PokemonLean.Basic

namespace PokemonLean.GameTheory

open PokemonLean

-- ============================================================================
-- N-PLY LOOKAHEAD SOLVER
-- ============================================================================

/-- Result of N-ply lookahead solver. -/
structure NPlyResult where
  energySequence : List EnergyType
  attackIndex : Nat
  expectedDamage : Nat
  isLethal : Bool
  turnsToKill : Nat
  deriving Repr

/-- Apply a sequence of energy attachments. -/
def applyEnergySequence (attacker : PokemonInPlay) : List EnergyType → PokemonInPlay
  | [] => attacker
  | e :: rest => applyEnergySequence { attacker with energy := e :: attacker.energy } rest

/-- All energy types for enumeration. -/
def allEnergyTypes : List EnergyType :=
  [.fire, .water, .grass, .lightning, .psychic, .fighting, .dark, .metal, .fairy, .dragon, .colorless]

/-- Attack damage calculation. -/
def attackDamage (attacker : PokemonInPlay) (defender : PokemonInPlay) (attack : Attack) : Nat :=
  calculateDamage attack attacker.card.energyType defender.card

/-- Find best attack from a list. -/
def bestAttackFrom (attacker : PokemonInPlay) (defender : PokemonInPlay) : List Attack → Option (Nat × Attack)
  | [] => none
  | attack :: rest =>
      let current : Option (Nat × Attack) :=
        if hasEnergyCost attack attacker.energy then some (0, attack) else none
      let tail := (bestAttackFrom attacker defender rest).map (fun (idx, atk) => (idx + 1, atk))
      match current, tail with
      | none, none => none
      | some c, none => some c
      | none, some b => some b
      | some c, some b =>
          if attackDamage attacker defender c.2 >= attackDamage attacker defender b.2 then some c else some b

/-- Find best attack for attacker's card. -/
def bestAttack (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option (Nat × Attack) :=
  bestAttackFrom attacker defender attacker.card.attacks

/-- Solve for N turns of energy attachment then attack. -/
def solveNPly (attacker : PokemonInPlay) (defender : PokemonInPlay) (n : Nat) : Option NPlyResult :=
  match n with
  | 0 =>
    match bestAttack attacker defender with
    | none => none
    | some (idx, attack) =>
      let damage := attackDamage attacker defender attack
      some {
        energySequence := []
        attackIndex := idx
        expectedDamage := damage
        isLethal := damage + defender.damage >= defender.card.hp
        turnsToKill := if damage > 0 then (defender.card.hp - defender.damage + damage - 1) / damage else 0
      }
  | n + 1 =>
    -- Try each energy type and recurse
    let results := allEnergyTypes.filterMap (fun energyType =>
      let newAttacker := { attacker with energy := energyType :: attacker.energy }
      match solveNPly newAttacker defender n with
      | none => none
      | some result =>
        some { result with energySequence := energyType :: result.energySequence })
    -- Pick best result by damage
    results.foldl (fun best curr =>
      match best with
      | none => some curr
      | some b => if curr.expectedDamage > b.expectedDamage then some curr else some b) none

/-- Attack index from solver is a valid Nat. -/
theorem solveNPly_attackIndex_nat (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (n : Nat) (result : NPlyResult) (_h : solveNPly attacker defender n = some result) :
    result.attackIndex ≥ 0 := by
  omega

/-- solveNPly at n=0 returns damage computed from bestAttack. -/
theorem solveNPly_zero_damage (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (result : NPlyResult)
    (h : solveNPly attacker defender 0 = some result) :
    ∃ (idx : Nat) (attack : Attack),
      bestAttack attacker defender = some (idx, attack) ∧
      result.attackIndex = idx ∧
      result.expectedDamage = attackDamage attacker defender attack := by
  simp only [solveNPly] at h
  match hBest : bestAttack attacker defender with
  | none => simp [hBest] at h
  | some (idx, atk) =>
    simp only [hBest, Option.some.injEq] at h
    exact ⟨idx, atk, rfl, by simp only [← h], by simp only [← h]⟩

/-- solveNPly isLethal flag is correct. -/
theorem solveNPly_zero_isLethal (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (result : NPlyResult)
    (h : solveNPly attacker defender 0 = some result) :
    result.isLethal ↔ (result.expectedDamage + defender.damage >= defender.card.hp) := by
  simp only [solveNPly] at h
  match hBest : bestAttack attacker defender with
  | none => simp [hBest] at h
  | some (idx, atk) =>
    simp only [hBest, Option.some.injEq] at h
    simp only [← h, ge_iff_le, decide_eq_true_eq]

/-- Energy sequence correctness: applyEnergySequence adds energies. -/
theorem applyEnergySequence_energy (attacker : PokemonInPlay) (energies : List EnergyType) :
    (applyEnergySequence attacker energies).energy = energies.reverse ++ attacker.energy := by
  induction energies generalizing attacker with
  | nil => simp [applyEnergySequence]
  | cons e rest ih =>
    simp only [applyEnergySequence]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

/-- applyEnergySequence preserves card. -/
theorem applyEnergySequence_card (attacker : PokemonInPlay) (energies : List EnergyType) :
    (applyEnergySequence attacker energies).card = attacker.card := by
  induction energies generalizing attacker with
  | nil => rfl
  | cons _ rest ih => simp only [applyEnergySequence]; exact ih _

/-- applyEnergySequence preserves damage. -/
theorem applyEnergySequence_damage (attacker : PokemonInPlay) (energies : List EnergyType) :
    (applyEnergySequence attacker energies).damage = attacker.damage := by
  induction energies generalizing attacker with
  | nil => rfl
  | cons _ rest ih => simp only [applyEnergySequence]; exact ih _

-- ============================================================================
-- LETHAL DETECTION (OTK FINDER)
-- ============================================================================

/-- Action sequence for lethal. -/
structure LethalSequence where
  energyAttachments : List EnergyType
  attackIndex : Nat
  totalDamage : Nat
  deriving Repr

/-- Check if a sequence of energy attachments enables a lethal attack. -/
def checkLethal (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (energies : List EnergyType) : Option LethalSequence :=
  let powered := applyEnergySequence attacker energies
  match bestAttack powered defender with
  | none => none
  | some (idx, attack) =>
    let damage := attackDamage powered defender attack
    if damage + defender.damage >= defender.card.hp then
      some { energyAttachments := energies, attackIndex := idx, totalDamage := damage }
    else
      none

/-- Find lethal within n turns of energy attachment. -/
def findLethalInTurns (attacker : PokemonInPlay) (defender : PokemonInPlay) : Nat → Option LethalSequence
  | 0 => checkLethal attacker defender []
  | n + 1 =>
    match checkLethal attacker defender [] with
    | some seq => some seq
    | none =>
      -- Try adding one energy and recursing
      let results := allEnergyTypes.filterMap (fun e =>
        let newAttacker := { attacker with energy := e :: attacker.energy }
        match findLethalInTurns newAttacker defender n with
        | none => none
        | some seq => some { seq with energyAttachments := e :: seq.energyAttachments })
      results.head?

/-- Find lethal with up to 3 turns of setup (standard game horizon). -/
def findLethal (attacker : PokemonInPlay) (defender : PokemonInPlay) : Option LethalSequence :=
  findLethalInTurns attacker defender 3

theorem checkLethal_isLethal (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (energies : List EnergyType) (seq : LethalSequence)
    (h : checkLethal attacker defender energies = some seq) :
    seq.totalDamage + defender.damage >= defender.card.hp := by
  simp only [checkLethal] at h
  cases hBest : bestAttack (applyEnergySequence attacker energies) defender with
  | none => simp [hBest] at h
  | some choice =>
    simp only [hBest] at h
    by_cases hLethal : attackDamage (applyEnergySequence attacker energies) defender choice.2 +
        defender.damage >= defender.card.hp
    · simp [hLethal] at h
      cases h
      simpa using hLethal
    · simp [hLethal] at h

/-- findLethalInTurns soundness: if it returns a sequence, that sequence is truly lethal. -/
theorem findLethalInTurns_sound (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (n : Nat) (seq : LethalSequence)
    (h : findLethalInTurns attacker defender n = some seq) :
    seq.totalDamage + defender.damage >= defender.card.hp := by
  induction n generalizing attacker seq with
  | zero =>
    -- Base case: findLethalInTurns _ _ 0 = checkLethal _ _ []
    simp only [findLethalInTurns] at h
    exact checkLethal_isLethal attacker defender [] seq h
  | succ m ih =>
    -- Inductive case
    simp only [findLethalInTurns] at h
    match hCheck : checkLethal attacker defender [] with
    | some foundSeq =>
      -- checkLethal succeeded immediately
      simp only [hCheck, Option.some.injEq] at h
      rw [← h]
      exact checkLethal_isLethal attacker defender [] foundSeq hCheck
    | none =>
      -- Need to look at recursive results
      simp only [hCheck] at h
      -- h : results.head? = some seq
      -- Prove all elements in the filterMap result satisfy the lethal condition
      have hAllLethal : ∀ s ∈ (allEnergyTypes.filterMap (fun e =>
          let newAttacker := { attacker with energy := e :: attacker.energy }
          match findLethalInTurns newAttacker defender m with
          | none => none
          | some innerSeq => some { innerSeq with energyAttachments := e :: innerSeq.energyAttachments })),
          s.totalDamage + defender.damage ≥ defender.card.hp := by
        intro s hs
        simp only [List.mem_filterMap] at hs
        obtain ⟨e, _he, hMatch⟩ := hs
        split at hMatch
        · contradiction
        · rename_i innerSeq hRec
          simp only [Option.some.injEq] at hMatch
          have hIHinner := ih { attacker with energy := e :: attacker.energy } innerSeq hRec
          rw [← hMatch]
          exact hIHinner
      -- seq is the head of results, so seq is in results
      cases hHead : (allEnergyTypes.filterMap (fun e =>
          let newAttacker := { attacker with energy := e :: attacker.energy }
          match findLethalInTurns newAttacker defender m with
          | none => none
          | some innerSeq => some { innerSeq with energyAttachments := e :: innerSeq.energyAttachments })) with
      | nil =>
        simp only [hHead, List.head?_nil] at h
        cases h
      | cons first rest =>
        simp only [hHead, List.head?_cons, Option.some.injEq] at h
        subst h
        exact hAllLethal first (by rw [hHead]; exact List.Mem.head _)

/-- findLethal soundness (convenience wrapper). -/
theorem findLethal_sound (attacker : PokemonInPlay) (defender : PokemonInPlay)
    (seq : LethalSequence)
    (h : findLethal attacker defender = some seq) :
    seq.totalDamage + defender.damage >= defender.card.hp := by
  exact findLethalInTurns_sound attacker defender 3 seq h

-- ============================================================================
-- EXPECTED DAMAGE UNDER RNG
-- ============================================================================

/-- Possible damage outcomes for a coin-flip attack. -/
structure DamageDistribution where
  outcomes : List (Nat × Nat)  -- (damage, weight/probability numerator)
  totalWeight : Nat
  deriving Repr

/-- Calculate expected damage numerator (divide by totalWeight for actual expected value). -/
def expectedDamageNumerator (dist : DamageDistribution) : Nat :=
  dist.outcomes.foldl (fun acc (damage, weight) => acc + damage * weight) 0

/-- For attacks without coin flips, damage is deterministic. -/
def deterministicDamage (attack : Attack) (attackerType : EnergyType) (defender : Card) : DamageDistribution :=
  let damage := calculateDamage attack attackerType defender
  { outcomes := [(damage, 1)], totalWeight := 1 }

/-- For a single coin flip attack: heads = base + bonus, tails = base. -/
def singleFlipDamage (baseDamage headsBonus : Nat) (attackerType : EnergyType) (defender : Card) : DamageDistribution :=
  let baseCalc := calculateDamage { name := "", baseDamage := baseDamage, effects := [] } attackerType defender
  let headsCalc := calculateDamage { name := "", baseDamage := baseDamage + headsBonus, effects := [] } attackerType defender
  { outcomes := [(headsCalc, 1), (baseCalc, 1)], totalWeight := 2 }

theorem expectedDamage_deterministic (attack : Attack) (attackerType : EnergyType) (defender : Card) :
    let dist := deterministicDamage attack attackerType defender
    expectedDamageNumerator dist = calculateDamage attack attackerType defender * dist.totalWeight := by
  simp [deterministicDamage, expectedDamageNumerator, List.foldl]

theorem expectedDamage_singleFlip (baseDamage headsBonus : Nat) (attackerType : EnergyType) (defender : Card) :
    let dist := singleFlipDamage baseDamage headsBonus attackerType defender
    expectedDamageNumerator dist =
      calculateDamage { name := "", baseDamage := baseDamage + headsBonus, effects := [] } attackerType defender +
      calculateDamage { name := "", baseDamage := baseDamage, effects := [] } attackerType defender := by
  simp [singleFlipDamage, expectedDamageNumerator, List.foldl]

-- ============================================================================
-- EVOLUTION CHAIN VALIDATION
-- ============================================================================

/-- Evolution relationship between cards. -/
def EvolvesFrom (evolved base : Card) : Prop :=
  evolved.hp >= base.hp  -- Simplified: evolved has >= HP

/-- A valid evolution chain is a sequence where each evolves from previous. -/
inductive EvolutionChain : List Card → Prop
  | single (card : Card) : EvolutionChain [card]
  | evolve (evolved : Card) (chain : List Card) (base : Card)
      (hChain : EvolutionChain (base :: chain))
      (hEvolves : EvolvesFrom evolved base) :
      EvolutionChain (evolved :: base :: chain)

/-- Evolution preserves damage. -/
theorem evolution_preserves_damage (pokemon : PokemonInPlay) (evolved : Card)
    (_hEvolves : EvolvesFrom evolved pokemon.card) :
    let evolvedPokemon := { pokemon with card := evolved }
    evolvedPokemon.damage = pokemon.damage := by
  rfl

/-- Evolution preserves energy attachments. -/
theorem evolution_preserves_energy (pokemon : PokemonInPlay) (evolved : Card)
    (_hEvolves : EvolvesFrom evolved pokemon.card) :
    let evolvedPokemon := { pokemon with card := evolved }
    evolvedPokemon.energy = pokemon.energy := by
  rfl

theorem EvolvesFrom_refl (card : Card) : EvolvesFrom card card := by
  simp [EvolvesFrom]

theorem EvolvesFrom_trans (a b c : Card) :
    EvolvesFrom a b → EvolvesFrom b c → EvolvesFrom a c := by
  intro h1 h2
  dsimp [EvolvesFrom] at h1 h2
  exact Nat.le_trans h2 h1

theorem evolutionChain_tail (evolved base : Card) (chain : List Card)
    (h : EvolutionChain (evolved :: base :: chain)) :
    EvolutionChain (base :: chain) := by
  cases h with
  | evolve evolved' chain' base' hChain hEvolves =>
    simpa using hChain

theorem evolutionChain_head_evolves (evolved base : Card) (chain : List Card)
    (h : EvolutionChain (evolved :: base :: chain)) :
    EvolvesFrom evolved base := by
  cases h with
  | evolve evolved' chain' base' hChain hEvolves =>
    simpa using hEvolves

theorem evolutionChain_length_pos (chain : List Card) (h : EvolutionChain chain) :
    0 < chain.length := by
  cases h with
  | single card => simp
  | evolve evolved chain base hChain hEvolves => simp

theorem evolution_preserves_status (pokemon : PokemonInPlay) (evolved : Card)
    (_hEvolves : EvolvesFrom evolved pokemon.card) :
    let evolvedPokemon := { pokemon with card := evolved }
    evolvedPokemon.status = pokemon.status := by
  rfl

theorem evolution_preserves_damage_le (pokemon : PokemonInPlay) (evolved : Card)
    (hEvolves : EvolvesFrom evolved pokemon.card)
    (hDamage : pokemon.damage ≤ pokemon.card.hp) :
    pokemon.damage ≤ evolved.hp := by
  dsimp [EvolvesFrom] at hEvolves
  exact Nat.le_trans hDamage hEvolves

-- ============================================================================
-- CARD WELL-FORMEDNESS
-- ============================================================================

/-- A card is well-formed if it has valid properties. -/
def WellFormedCard (card : Card) : Prop :=
  card.hp > 0 ∧
  card.name.length > 0 ∧
  (card.attacks.all (fun a => a.name.length > 0)) = true

/-- Check well-formedness (decidable). -/
def checkWellFormed (card : Card) : Bool :=
  card.hp > 0 &&
  card.name.length > 0 &&
  card.attacks.all (fun a => a.name.length > 0)

theorem checkWellFormed_sound (card : Card) :
    checkWellFormed card = true → WellFormedCard card := by
  intro h
  simp only [checkWellFormed, WellFormedCard, Bool.and_eq_true, decide_eq_true_eq] at *
  constructor
  · exact h.1.1
  constructor
  · exact h.1.2
  · exact h.2

-- ============================================================================
-- DECK LEGALITY
-- ============================================================================

/-- Count occurrences of a card name in a deck. -/
def countCardName (name : String) (deck : List Card) : Nat :=
  deck.filter (fun c => c.name == name) |>.length

/-- A deck is legal if it has 60 cards and ≤4 copies of each card. -/
def LegalDeck (deck : List Card) : Prop :=
  deck.length = 60 ∧
  ∀ name, countCardName name deck ≤ 4

/-- Check deck legality. -/
def checkDeckLegality (deck : List Card) : Bool :=
  deck.length == 60 &&
  deck.all (fun card => countCardName card.name deck ≤ 4)

-- ============================================================================
-- STADIUM CARDS
-- ============================================================================

/-- Stadium card effects. -/
inductive StadiumEffect
  | healAllPokemon (amount : Nat)
  | damageAllPokemon (amount : Nat)
  | modifyRetreatCost (delta : Int)
  | drawOnAttach (count : Nat)
  deriving Repr, BEq, DecidableEq

structure Stadium where
  name : String
  effect : StadiumEffect
  deriving Repr, BEq, DecidableEq

/-- Apply stadium effect to game state. -/
def applyStadiumEffect (stadium : Stadium) (state : GameState) : GameState :=
  match stadium.effect with
  | .healAllPokemon amount =>
    let healPokemon := fun (p : PokemonInPlay) => { p with damage := p.damage - amount }
    let healPlayer := fun (ps : PlayerState) =>
      { ps with
        active := ps.active.map healPokemon
        bench := ps.bench.map healPokemon }
    { state with
      playerOne := healPlayer state.playerOne
      playerTwo := healPlayer state.playerTwo }
  | .damageAllPokemon amount =>
    let damagePokemon := fun (p : PokemonInPlay) =>
      { p with damage := Nat.min (p.damage + amount) p.card.hp }
    let damagePlayer := fun (ps : PlayerState) =>
      { ps with
        active := ps.active.map damagePokemon
        bench := ps.bench.map damagePokemon }
    { state with
      playerOne := damagePlayer state.playerOne
      playerTwo := damagePlayer state.playerTwo }
  | .modifyRetreatCost _ => state
  | .drawOnAttach _ => state

theorem applyStadiumEffect_modifyRetreatCost (state : GameState) (delta : Int) :
    applyStadiumEffect { name := "", effect := .modifyRetreatCost delta } state = state := by
  rfl

theorem applyStadiumEffect_drawOnAttach (state : GameState) (count : Nat) :
    applyStadiumEffect { name := "", effect := .drawOnAttach count } state = state := by
  rfl

theorem applyStadiumEffect_healAll_active_none (state : GameState) (amount : Nat)
    (hNone : state.playerOne.active = none) :
    (applyStadiumEffect { name := "", effect := .healAllPokemon amount } state).playerOne.active = none := by
  simp [applyStadiumEffect, hNone]

theorem applyStadiumEffect_damageAll_active_none (state : GameState) (amount : Nat)
    (hNone : state.playerOne.active = none) :
    (applyStadiumEffect { name := "", effect := .damageAllPokemon amount } state).playerOne.active = none := by
  simp [applyStadiumEffect, hNone]

theorem applyStadiumEffect_healAll_preserves_bench_length (state : GameState) (amount : Nat) :
    (applyStadiumEffect { name := "", effect := .healAllPokemon amount } state).playerOne.bench.length =
      state.playerOne.bench.length := by
  simp [applyStadiumEffect, List.length_map]

theorem applyStadiumEffect_damageAll_preserves_bench_length (state : GameState) (amount : Nat) :
    (applyStadiumEffect { name := "", effect := .damageAllPokemon amount } state).playerOne.bench.length =
      state.playerOne.bench.length := by
  simp [applyStadiumEffect, List.length_map]



theorem applyStadiumEffect_healAll_preserves_active_none (state : GameState) (amount : Nat)
    (hNone : state.playerTwo.active = none) :
    (applyStadiumEffect { name := "", effect := .healAllPokemon amount } state).playerTwo.active = none := by
  simp [applyStadiumEffect, hNone]

theorem applyStadiumEffect_damageAll_preserves_active_none (state : GameState) (amount : Nat)
    (hNone : state.playerTwo.active = none) :
    (applyStadiumEffect { name := "", effect := .damageAllPokemon amount } state).playerTwo.active = none := by
  simp [applyStadiumEffect, hNone]
-- ============================================================================
-- PROGRESS METRICS
-- ============================================================================

/-- Progress metric: sum of opponent prizes + opponent active HP remaining. -/
def progressMetric (player : PlayerId) (state : GameState) : Nat :=
  let opponent := otherPlayer player
  let oppState := getPlayerState state opponent
  let prizesRemaining := oppState.prizes.length
  let activeHp := match oppState.active with
    | none => 0
    | some p => p.card.hp - p.damage
  prizesRemaining * 1000 + activeHp

theorem progressMetric_zero_of_no_prizes_no_active (player : PlayerId) (state : GameState)
    (hPrizes : (getPlayerState state (otherPlayer player)).prizes = [])
    (hActive : (getPlayerState state (otherPlayer player)).active = none) :
    progressMetric player state = 0 := by
  simp [progressMetric, hPrizes, hActive]

theorem progressMetric_zero_of_no_prizes_active_none (player : PlayerId) (state : GameState)
    (hPrizes : (getPlayerState state (otherPlayer player)).prizes.isEmpty = true)
    (hActive : (getPlayerState state (otherPlayer player)).active = none) :
    progressMetric player state = 0 := by
  have hPrizes' : (getPlayerState state (otherPlayer player)).prizes = [] := by
    cases h : (getPlayerState state (otherPlayer player)).prizes with
    | nil =>
      rfl
    | cons prize rest =>
      simp [h] at hPrizes
  simp [progressMetric, hPrizes', hActive]

theorem progressMetric_pos_of_prizes (player : PlayerId) (state : GameState)
    (hPrizes : (getPlayerState state (otherPlayer player)).prizes ≠ []) :
    0 < progressMetric player state := by
  cases h : (getPlayerState state (otherPlayer player)).prizes with
  | nil =>
    cases hPrizes (by simp [h])
  | cons prize rest =>
    have hPos : 0 < (rest.length + 1) * 1000 := by
      have h1 : 0 < rest.length + 1 := Nat.succ_pos _
      exact Nat.mul_pos h1 (by decide : 0 < (1000:Nat))
    have hSum : 0 <
        (rest.length + 1) * 1000 +
        match (getPlayerState state (otherPlayer player)).active with
        | none => 0
        | some p => p.card.hp - p.damage := by
      exact Nat.lt_of_lt_of_le hPos (Nat.le_add_right _ _)
    simpa [progressMetric, h] using hSum



theorem progressMetric_ge_active_hp (player : PlayerId) (state : GameState) :
    match (getPlayerState state (otherPlayer player)).active with
    | none => 0 ≤ progressMetric player state
    | some p => p.card.hp - p.damage ≤ progressMetric player state := by
  cases h : (getPlayerState state (otherPlayer player)).active with
  | none =>
    simp [progressMetric, h]
  | some p =>
    simp [progressMetric, h]
/-- Game complexity bound by total cards in play. -/
def gameComplexityBound (state : GameState) : Nat :=
  state.playerOne.deck.length + state.playerTwo.deck.length +
  state.playerOne.prizes.length + state.playerTwo.prizes.length +
  state.playerOne.hand.length + state.playerTwo.hand.length

/-- Player has won the game. -/
def hasWonGame (player : PlayerId) (state : GameState) : Prop :=
  let opponent := otherPlayer player
  let opponentState := getPlayerState state opponent
  opponentState.prizes.isEmpty ∨ opponentState.active.isNone

theorem hasWonGame_prizes_empty (player : PlayerId) (state : GameState)
    (hEmpty : (getPlayerState state (otherPlayer player)).prizes = []) :
    hasWonGame player state := by
  unfold hasWonGame
  left
  simp [hEmpty]

theorem hasWonGame_no_active (player : PlayerId) (state : GameState)
    (hNone : (getPlayerState state (otherPlayer player)).active = none) :
    hasWonGame player state := by
  unfold hasWonGame
  right
  simp [hNone]

-- ============================================================================
-- MULTI-PRIZE KNOCKOUTS (EX/V/VMAX Pokemon)
-- ============================================================================

/-- Card rarity determines prize value. -/
inductive CardRarity
  | common
  | uncommon
  | rare
  | holo
  | ex        -- Worth 2 prizes
  | v         -- Worth 2 prizes
  | vstar     -- Worth 2 prizes
  | vmax      -- Worth 3 prizes
  deriving Repr, BEq, DecidableEq

/-- Prize value based on rarity (how many prizes opponent takes on KO). -/
def prizeValue : CardRarity → Nat
  | .common => 1
  | .uncommon => 1
  | .rare => 1
  | .holo => 1
  | .ex => 2
  | .v => 2
  | .vstar => 2
  | .vmax => 3

/-- Card with rarity annotation. -/
structure RarityCard where
  card : Card
  rarity : CardRarity
  deriving Repr

/-- Take prizes based on knocked out Pokemon's rarity. -/
def takeMultiPrize (attacker defender : PlayerState) (rarity : CardRarity) : PlayerState × PlayerState :=
  let prizesToTake := prizeValue rarity
  let rec takePrizes (n : Nat) (att defState : PlayerState) : PlayerState × PlayerState :=
    match n, defState.prizes with
    | 0, _ => (att, defState)
    | _, [] => (att, defState)
    | n + 1, prize :: rest =>
      takePrizes n ({ att with hand := prize :: att.hand }) ({ defState with prizes := rest })
  takePrizes prizesToTake attacker defender

/-- Prize value is positive for non-normal rarity. -/
theorem takeMultiPrize_effect (rarity : CardRarity) :
    prizeValue rarity ≥ 1 := by
  cases rarity <;> simp [prizeValue]

theorem prizeValue_bounded (rarity : CardRarity) : prizeValue rarity ≤ 3 := by
  cases rarity <;> simp [prizeValue]

-- ============================================================================
-- BENCH TARGET SELECTION (Gust Effects)
-- ============================================================================

/-- Score a bench Pokemon as a target (lower HP, more damage = better target). -/
def benchTargetScore (benched : PokemonInPlay) (attacker : PokemonInPlay) : Int :=
  let remainingHp := (benched.card.hp : Int) - benched.damage
  let canKo := match bestAttack attacker benched with
    | none => false
    | some (_, attack) => attackDamage attacker benched attack + benched.damage >= benched.card.hp
  -- Prefer targets we can KO, then prefer low HP
  if canKo then -1000 - remainingHp else -remainingHp

/-- Find the best bench target for Gust/Boss's Orders effect. -/
def bestBenchTarget (state : GameState) (attacker : PokemonInPlay) : Option PokemonInPlay :=
  let player := state.activePlayer
  let opponent := otherPlayer player
  let opponentState := getPlayerState state opponent
  let bench := opponentState.bench
  if bench.isEmpty then none
  else
    let scored := bench.map (fun p => (p, benchTargetScore p attacker))
    let best := scored.foldl (fun acc (p, score) =>
      match acc with
      | none => some (p, score)
      | some (_, bestScore) => if score < bestScore then some (p, score) else acc) none
    best.map (fun (p, _) => p)

/-- Swap a bench Pokemon to active (for Gust effect). -/
def swapToActive (state : GameState) (player : PlayerId) (benchIdx : Nat) : Option GameState :=
  let playerState := getPlayerState state player
  match playerState.active, listGet? playerState.bench benchIdx with
  | some currentActive, some newActive =>
    let newBench := playerState.bench.eraseIdx benchIdx ++ [currentActive]
    let newPlayerState := { playerState with active := some newActive, bench := newBench }
    some (setPlayerState state player newPlayerState)
  | none, some newActive =>
    let newBench := playerState.bench.eraseIdx benchIdx
    let newPlayerState := { playerState with active := some newActive, bench := newBench }
    some (setPlayerState state player newPlayerState)
  | _, _ => none

/-- bestBenchTarget only returns some when bench is non-empty (by construction). -/
theorem bestBenchTarget_requires_bench (state : GameState) (attacker : PokemonInPlay) :
    (getPlayerState state (otherPlayer state.activePlayer)).bench.isEmpty →
    bestBenchTarget state attacker = none := by
  intro h
  unfold bestBenchTarget
  simp [h]

-- ============================================================================
-- CORPUS WELL-FORMEDNESS VALIDATION
-- ============================================================================

/-- Check if all cards in a list are well-formed. -/
def allWellFormed (cards : List Card) : Bool :=
  cards.all checkWellFormed

/-- Validate corpus entries. -/
def validateCorpus (corpus : List Card) : List (Card × Bool) :=
  corpus.map (fun c => (c, checkWellFormed c))

/-- Count well-formed cards in corpus. -/
def countWellFormed (corpus : List Card) : Nat :=
  corpus.filter checkWellFormed |>.length

-- ============================================================================
-- TYPE SYSTEM THEORY
-- ============================================================================

/-- Base effectiveness multiplier for attacker vs defender. -/
def typeMultiplier (attacker defender : EnergyType) : Nat :=
  match attacker, defender with
  | .fire, .grass => 2
  | .water, .fire => 2
  | .grass, .water => 2
  | .lightning, .water => 2
  | .fighting, .colorless => 2
  | .psychic, .fighting => 2
  | .dark, .psychic => 2
  | .metal, .fairy => 2
  | .fairy, .dragon => 2
  | .dragon, .dark => 2
  | .colorless, .fighting => 2
  | _, _ => 1

/-- Type effectiveness as a proposition. -/
def TypeEffective (attacker defender : EnergyType) : Prop :=
  typeMultiplier attacker defender = 2

/-- A list of defending types is covered if some type is effective. -/
def TypeCoverage (attacker : EnergyType) (defenders : List EnergyType) : Prop :=
  ∃ d ∈ defenders, TypeEffective attacker d

/-- Dual-type effectiveness: either component gives effectiveness. -/
def DualTypeEffective (attacker : EnergyType) (def1 def2 : EnergyType) : Prop :=
  TypeEffective attacker def1 ∨ TypeEffective attacker def2

/-- All types a single attacker hits for effectiveness. -/
def typeCoverageList (attacker : EnergyType) : List EnergyType :=
  allEnergyTypes.filter (fun defender => decide (typeMultiplier attacker defender = 2))

theorem typeMultiplier_pos (attacker defender : EnergyType) : typeMultiplier attacker defender ≥ 1 := by
  cases attacker <;> cases defender <;> simp [typeMultiplier]

theorem typeMultiplier_self (t : EnergyType) : typeMultiplier t t = 1 := by
  cases t <;> simp [typeMultiplier]

theorem typeMultiplier_le_two (attacker defender : EnergyType) : typeMultiplier attacker defender ≤ 2 := by
  cases attacker <;> cases defender <;> simp [typeMultiplier]

theorem typeMultiplier_eq_one_or_two (attacker defender : EnergyType) :
    typeMultiplier attacker defender = 1 ∨ typeMultiplier attacker defender = 2 := by
  cases attacker <;> cases defender <;> simp [typeMultiplier]

theorem typeEffective_iff (attacker defender : EnergyType) :
    TypeEffective attacker defender ↔ typeMultiplier attacker defender = 2 := by
  rfl

theorem typeEffective_not_self (t : EnergyType) : ¬ TypeEffective t t := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_fire_grass : TypeEffective .fire .grass := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_water_fire : TypeEffective .water .fire := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_grass_water : TypeEffective .grass .water := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_lightning_water : TypeEffective .lightning .water := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_fighting_colorless : TypeEffective .fighting .colorless := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_psychic_fighting : TypeEffective .psychic .fighting := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_dark_psychic : TypeEffective .dark .psychic := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_metal_fairy : TypeEffective .metal .fairy := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_fairy_dragon : TypeEffective .fairy .dragon := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_dragon_dark : TypeEffective .dragon .dark := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_colorless_fighting : TypeEffective .colorless .fighting := by
  simp [TypeEffective, typeMultiplier]

theorem typeEffective_fire_iff (defender : EnergyType) :
    TypeEffective .fire defender ↔ defender = .grass := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_water_iff (defender : EnergyType) :
    TypeEffective .water defender ↔ defender = .fire := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_grass_iff (defender : EnergyType) :
    TypeEffective .grass defender ↔ defender = .water := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_lightning_iff (defender : EnergyType) :
    TypeEffective .lightning defender ↔ defender = .water := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_psychic_iff (defender : EnergyType) :
    TypeEffective .psychic defender ↔ defender = .fighting := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_fighting_iff (defender : EnergyType) :
    TypeEffective .fighting defender ↔ defender = .colorless := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_dark_iff (defender : EnergyType) :
    TypeEffective .dark defender ↔ defender = .psychic := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_metal_iff (defender : EnergyType) :
    TypeEffective .metal defender ↔ defender = .fairy := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_fairy_iff (defender : EnergyType) :
    TypeEffective .fairy defender ↔ defender = .dragon := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_dragon_iff (defender : EnergyType) :
    TypeEffective .dragon defender ↔ defender = .dark := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeEffective_colorless_iff (defender : EnergyType) :
    TypeEffective .colorless defender ↔ defender = .fighting := by
  cases defender <;> simp [TypeEffective, typeMultiplier]

theorem typeCoverageList_mem_iff (attacker defender : EnergyType) :
    defender ∈ typeCoverageList attacker ↔ TypeEffective attacker defender := by
  constructor
  · intro h
    have h' := (List.mem_filter.mp h).2
    simpa [TypeEffective] using h'
  · intro h
    have hMem : defender ∈ allEnergyTypes := by
      cases defender <;> simp [allEnergyTypes]
    exact (List.mem_filter.mpr ⟨hMem, by simpa [TypeEffective] using h⟩)

theorem typeCoverageList_sound (attacker defender : EnergyType) :
    defender ∈ typeCoverageList attacker → TypeEffective attacker defender := by
  intro h
  have h' := (List.mem_filter.mp h).2
  simpa [TypeEffective] using h'

theorem typeCoverageList_subset_all (attacker defender : EnergyType) :
    defender ∈ typeCoverageList attacker → defender ∈ allEnergyTypes := by
  intro h
  exact (List.mem_filter.mp h).1

theorem typeCoverageList_complete (attacker defender : EnergyType) :
    TypeEffective attacker defender → defender ∈ typeCoverageList attacker := by
  intro h
  have hMem : defender ∈ allEnergyTypes := by
    cases defender <;> simp [allEnergyTypes]
  exact (List.mem_filter.mpr ⟨hMem, by simpa [TypeEffective] using h⟩)

theorem typeCoverageList_iff (attacker defender : EnergyType) :
    defender ∈ typeCoverageList attacker ↔ TypeEffective attacker defender := by
  constructor
  · exact typeCoverageList_sound attacker defender
  · exact typeCoverageList_complete attacker defender

theorem typeEffective_exists (attacker : EnergyType) : ∃ defender, TypeEffective attacker defender := by
  cases attacker with
  | fire =>
    refine ⟨.grass, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | water =>
    refine ⟨.fire, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | grass =>
    refine ⟨.water, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | lightning =>
    refine ⟨.water, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | psychic =>
    refine ⟨.fighting, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | fighting =>
    refine ⟨.colorless, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | dark =>
    refine ⟨.psychic, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | metal =>
    refine ⟨.fairy, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | fairy =>
    refine ⟨.dragon, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | dragon =>
    refine ⟨.dark, ?_⟩
    simp [TypeEffective, typeMultiplier]
  | colorless =>
    refine ⟨.fighting, ?_⟩
    simp [TypeEffective, typeMultiplier]

theorem typeCoverageList_nonempty (attacker : EnergyType) :
    typeCoverageList attacker ≠ [] := by
  intro hEmpty
  have ⟨defender, hEff⟩ := typeEffective_exists attacker
  have hMem : defender ∈ typeCoverageList attacker := typeCoverageList_complete attacker defender hEff
  exact (List.ne_nil_of_mem hMem) hEmpty

theorem typeCoverageList_length_pos (attacker : EnergyType) :
    0 < (typeCoverageList attacker).length := by
  cases h : typeCoverageList attacker with
  | nil =>
    cases (typeCoverageList_nonempty attacker) (by simp [h])
  | cons d rest =>
    simp

theorem typeCoverageList_no_self (t : EnergyType) : t ∉ typeCoverageList t := by
  intro h
  exact typeEffective_not_self t (typeCoverageList_sound t t h)

theorem typeCoverage_mem (attacker defender : EnergyType) :
    TypeEffective attacker defender → TypeCoverage attacker [defender] := by
  intro h
  exact ⟨defender, by simp, h⟩

theorem typeCoverage_singleton (attacker defender : EnergyType) :
    TypeCoverage attacker [defender] ↔ TypeEffective attacker defender := by
  constructor
  · intro h
    rcases h with ⟨d, hMem, hEff⟩
    have hEq : d = defender := by simpa using hMem
    simpa [hEq] using hEff
  · intro h
    exact typeCoverage_mem attacker defender h

theorem typeCoverage_cons (attacker : EnergyType) (defender : EnergyType) (defenders : List EnergyType) :
    TypeCoverage attacker (defender :: defenders) ↔
      TypeEffective attacker defender ∨ TypeCoverage attacker defenders := by
  constructor
  · intro h
    rcases h with ⟨d, hMem, hEff⟩
    have hMem' : d = defender ∨ d ∈ defenders := by
      simpa using hMem
    cases hMem' with
    | inl hEq =>
      left
      simpa [hEq] using hEff
    | inr hIn =>
      right
      exact ⟨d, hIn, hEff⟩
  · intro h
    cases h with
    | inl hEff =>
      exact ⟨defender, by simp, hEff⟩
    | inr hCov =>
      rcases hCov with ⟨d, hIn, hEff⟩
      exact ⟨d, by simp [hIn], hEff⟩

theorem typeCoverage_pair (attacker : EnergyType) (d1 d2 : EnergyType) :
    TypeCoverage attacker [d1, d2] ↔ TypeEffective attacker d1 ∨ TypeEffective attacker d2 := by
  simpa [typeCoverage_singleton] using (typeCoverage_cons attacker d1 [d2])

theorem typeCoverage_append (attacker : EnergyType) (defenders1 defenders2 : List EnergyType) :
    TypeCoverage attacker (defenders1 ++ defenders2) ↔
      TypeCoverage attacker defenders1 ∨ TypeCoverage attacker defenders2 := by
  constructor
  · intro h
    rcases h with ⟨d, hMem, hEff⟩
    have hMem' : d ∈ defenders1 ∨ d ∈ defenders2 := by
      simpa [List.mem_append] using hMem
    cases hMem' with
    | inl hIn =>
      exact Or.inl ⟨d, hIn, hEff⟩
    | inr hIn =>
      exact Or.inr ⟨d, hIn, hEff⟩
  · intro h
    cases h with
    | inl hCov =>
      rcases hCov with ⟨d, hIn, hEff⟩
      exact ⟨d, by simp [hIn], hEff⟩
    | inr hCov =>
      rcases hCov with ⟨d, hIn, hEff⟩
      exact ⟨d, by simp [hIn], hEff⟩

theorem typeCoverage_append_left (attacker : EnergyType) (defenders1 defenders2 : List EnergyType) :
    TypeCoverage attacker defenders1 → TypeCoverage attacker (defenders1 ++ defenders2) := by
  intro h
  exact (typeCoverage_append attacker defenders1 defenders2).2 (Or.inl h)

theorem typeCoverage_append_right (attacker : EnergyType) (defenders1 defenders2 : List EnergyType) :
    TypeCoverage attacker defenders2 → TypeCoverage attacker (defenders1 ++ defenders2) := by
  intro h
  exact (typeCoverage_append attacker defenders1 defenders2).2 (Or.inr h)

theorem dualTypeEffective_symm (attacker : EnergyType) (d1 d2 : EnergyType) :
    DualTypeEffective attacker d1 d2 ↔ DualTypeEffective attacker d2 d1 := by
  constructor <;> intro h <;> cases h with
  | inl h1 => exact Or.inr h1
  | inr h2 => exact Or.inl h2

theorem dualTypeEffective_left (attacker : EnergyType) (d1 d2 : EnergyType) :
    TypeEffective attacker d1 → DualTypeEffective attacker d1 d2 := by
  intro h
  exact Or.inl h

theorem dualTypeEffective_right (attacker : EnergyType) (d1 d2 : EnergyType) :
    TypeEffective attacker d2 → DualTypeEffective attacker d1 d2 := by
  intro h
  exact Or.inr h

-- ============================================================================
-- TYPE COMBINATIONS
-- ============================================================================

/-- Coverage list for a pair of attacking types. -/
def typePairCoverageList (attacker1 attacker2 : EnergyType) : List EnergyType :=
  allEnergyTypes.filter (fun defender =>
    (typeMultiplier attacker1 defender == 2) || (typeMultiplier attacker2 defender == 2))

def typePairCovers (attacker1 attacker2 defender : EnergyType) : Bool :=
  (typeMultiplier attacker1 defender == 2) || (typeMultiplier attacker2 defender == 2)

theorem typePairCoverageList_iff (attacker1 attacker2 defender : EnergyType) :
    defender ∈ typePairCoverageList attacker1 attacker2 ↔ typePairCovers attacker1 attacker2 defender = true := by
  constructor
  · intro h
    have h' := (List.mem_filter.mp h).2
    simpa [typePairCovers] using h'
  · intro h
    have hMem : defender ∈ allEnergyTypes := by
      cases defender <;> simp [allEnergyTypes]
    exact (List.mem_filter.mpr ⟨hMem, by simpa [typePairCovers] using h⟩)

theorem typePairCoverageList_subset_all (attacker1 attacker2 defender : EnergyType) :
    defender ∈ typePairCoverageList attacker1 attacker2 → defender ∈ allEnergyTypes := by
  intro h
  exact (List.mem_filter.mp h).1
theorem typePairCovers_comm (attacker1 attacker2 defender : EnergyType) :
    typePairCovers attacker1 attacker2 defender = typePairCovers attacker2 attacker1 defender := by
  simp [typePairCovers, Bool.or_comm]

theorem typePairCovers_self (attacker defender : EnergyType) :
    typePairCovers attacker attacker defender = (typeMultiplier attacker defender == 2) := by
  simp [typePairCovers, Bool.or_self]

theorem typePairCoverage_member (attacker1 attacker2 defender : EnergyType) :
    TypeEffective attacker1 defender ∨ TypeEffective attacker2 defender →
    defender ∈ typePairCoverageList attacker1 attacker2 := by
  intro h
  have hMem : defender ∈ allEnergyTypes := by
    cases defender <;> simp [allEnergyTypes]
  have hCovers : typePairCovers attacker1 attacker2 defender = true := by
    cases h with
    | inl h1 =>
      have hOr : typeMultiplier attacker1 defender = 2 ∨ typeMultiplier attacker2 defender = 2 := by
        left
        simpa [TypeEffective] using h1
      simpa [typePairCovers] using hOr
    | inr h2 =>
      have hOr : typeMultiplier attacker1 defender = 2 ∨ typeMultiplier attacker2 defender = 2 := by
        right
        simpa [TypeEffective] using h2
      simpa [typePairCovers] using hOr
  exact (List.mem_filter.mpr ⟨hMem, by simpa [typePairCovers] using hCovers⟩)

theorem typePairCoverageList_nonempty (attacker1 attacker2 : EnergyType) :
    typePairCoverageList attacker1 attacker2 ≠ [] := by
  intro hEmpty
  have ⟨defender, hEff⟩ := typeEffective_exists attacker1
  have hMem := typePairCoverage_member attacker1 attacker2 defender (Or.inl hEff)
  exact (List.ne_nil_of_mem hMem) hEmpty

theorem typePairCoverageList_length_pos (attacker1 attacker2 : EnergyType) :
    0 < (typePairCoverageList attacker1 attacker2).length := by
  cases h : typePairCoverageList attacker1 attacker2 with
  | nil =>
    cases (typePairCoverageList_nonempty attacker1 attacker2) (by simp [h])
  | cons d rest =>
    simp

theorem typePairCoverageList_self_length_pos (attacker : EnergyType) :
    0 < (typePairCoverageList attacker attacker).length := by
  cases h : typePairCoverageList attacker attacker with
  | nil =>
    cases (typePairCoverageList_nonempty attacker attacker) (by simp [h])
  | cons d rest =>
    simp

-- ============================================================================
-- TEAM THEORY
-- ============================================================================

def DeckSubset (deck1 deck2 : List Card) : Prop :=
  ∀ card ∈ deck1, card ∈ deck2

theorem deckSubset_nil_left (deck : List Card) : DeckSubset [] deck := by
  intro card hMem
  cases hMem

theorem deckSubset_refl (deck : List Card) : DeckSubset deck deck := by
  intro card hMem
  exact hMem

theorem deckSubset_trans (deck1 deck2 deck3 : List Card)
    (h12 : DeckSubset deck1 deck2) (h23 : DeckSubset deck2 deck3) :
    DeckSubset deck1 deck3 := by
  intro card hMem
  exact h23 card (h12 card hMem)

theorem deckSubset_append_left (deck1 deck2 : List Card) :
    DeckSubset deck1 (deck1 ++ deck2) := by
  intro card hMem
  exact (List.mem_append.mpr (Or.inl hMem))

theorem deckSubset_append_right (deck1 deck2 : List Card) :
    DeckSubset deck2 (deck1 ++ deck2) := by
  intro card hMem
  exact (List.mem_append.mpr (Or.inr hMem))

theorem deckSubset_cons_iff (card : Card) (deck1 deck2 : List Card) :
    DeckSubset (card :: deck1) deck2 ↔ card ∈ deck2 ∧ DeckSubset deck1 deck2 := by
  constructor
  · intro h
    have hCard : card ∈ deck2 := h card (by simp)
    have hRest : DeckSubset deck1 deck2 := by
      intro c hMem
      exact h c (by simp [hMem])
    exact ⟨hCard, hRest⟩
  · intro h
    rcases h with ⟨hCard, hRest⟩
    intro c hMem
    have hMem' : c = card ∨ c ∈ deck1 := by simpa using hMem
    cases hMem' with
    | inl hEq =>
      simpa [hEq] using hCard
    | inr hIn =>
      exact hRest c hIn

def TeamCoverage (deck : List Card) (defender : EnergyType) : Prop :=
  ∃ card ∈ deck, TypeEffective card.energyType defender

theorem teamCoverage_of_mem (card : Card) (deck : List Card) (defender : EnergyType)
    (hMem : card ∈ deck) (hEff : TypeEffective card.energyType defender) :
    TeamCoverage deck defender := by
  exact ⟨card, hMem, hEff⟩

theorem teamCoverage_singleton (card : Card) (defender : EnergyType) :
    TeamCoverage [card] defender ↔ TypeEffective card.energyType defender := by
  constructor
  · intro h
    rcases h with ⟨c, hMem, hEff⟩
    have hEq : c = card := by simpa using hMem
    simpa [hEq] using hEff
  · intro h
    exact ⟨card, by simp, h⟩

theorem teamCoverage_cons (card : Card) (deck : List Card) (defender : EnergyType) :
    TeamCoverage (card :: deck) defender ↔
      TypeEffective card.energyType defender ∨ TeamCoverage deck defender := by
  constructor
  · intro h
    rcases h with ⟨c, hMem, hEff⟩
    have hMem' : c = card ∨ c ∈ deck := by simpa using hMem
    cases hMem' with
    | inl hEq =>
      left
      simpa [hEq] using hEff
    | inr hIn =>
      right
      exact ⟨c, hIn, hEff⟩
  · intro h
    cases h with
    | inl hEff =>
      exact ⟨card, by simp, hEff⟩
    | inr hCov =>
      rcases hCov with ⟨c, hIn, hEff⟩
      exact ⟨c, by simp [hIn], hEff⟩

theorem teamCoverage_append (deck1 deck2 : List Card) (defender : EnergyType) :
    TeamCoverage (deck1 ++ deck2) defender ↔
      TeamCoverage deck1 defender ∨ TeamCoverage deck2 defender := by
  constructor
  · intro h
    rcases h with ⟨c, hMem, hEff⟩
    have hMem' : c ∈ deck1 ∨ c ∈ deck2 := by
      simpa [List.mem_append] using hMem
    cases hMem' with
    | inl hIn =>
      exact Or.inl ⟨c, hIn, hEff⟩
    | inr hIn =>
      exact Or.inr ⟨c, hIn, hEff⟩
  · intro h
    cases h with
    | inl hCov =>
      rcases hCov with ⟨c, hIn, hEff⟩
      exact ⟨c, by simp [hIn], hEff⟩
    | inr hCov =>
      rcases hCov with ⟨c, hIn, hEff⟩
      exact ⟨c, by simp [hIn], hEff⟩

theorem teamCoverage_append_iff_left (deck1 deck2 : List Card) (defender : EnergyType) :
    TeamCoverage (deck1 ++ deck2) defender → deck2 = [] → TeamCoverage deck1 defender := by
  intro h hEmpty
  simpa [hEmpty] using h

theorem teamCoverage_append_left (deck1 deck2 : List Card) (defender : EnergyType) :
    TeamCoverage deck1 defender → TeamCoverage (deck1 ++ deck2) defender := by
  intro h
  exact (teamCoverage_append deck1 deck2 defender).2 (Or.inl h)

theorem teamCoverage_append_right (deck1 deck2 : List Card) (defender : EnergyType) :
    TeamCoverage deck2 defender → TeamCoverage (deck1 ++ deck2) defender := by
  intro h
  exact (teamCoverage_append deck1 deck2 defender).2 (Or.inr h)

theorem teamCoverage_pair (c1 c2 : Card) (defender : EnergyType) :
    TeamCoverage [c1, c2] defender ↔
      TypeEffective c1.energyType defender ∨ TypeEffective c2.energyType defender := by
  constructor
  · intro h
    have h' := (teamCoverage_cons c1 [c2] defender).1 h
    cases h' with
    | inl h1 => exact Or.inl h1
    | inr h2 =>
      exact Or.inr ((teamCoverage_singleton c2 defender).1 h2)
  · intro h
    cases h with
    | inl h1 =>
      exact (teamCoverage_cons c1 [c2] defender).2 (Or.inl h1)
    | inr h2 =>
      have h2' := (teamCoverage_singleton c2 defender).2 h2
      exact (teamCoverage_cons c1 [c2] defender).2 (Or.inr h2')

theorem teamCoverage_mono (deck1 deck2 : List Card) (defender : EnergyType)
    (hSub : DeckSubset deck1 deck2) :
    TeamCoverage deck1 defender → TeamCoverage deck2 defender := by
  intro h
  rcases h with ⟨card, hIn, hEff⟩
  exact ⟨card, hSub card hIn, hEff⟩

theorem teamCoverage_exists (deck : List Card) (hNonempty : deck ≠ []) :
    ∃ defender, TeamCoverage deck defender := by
  cases hDeck : deck with
  | nil =>
    cases hNonempty (by simp [hDeck])
  | cons card rest =>
    have ⟨defender, hEff⟩ := typeEffective_exists card.energyType
    exact ⟨defender, ⟨card, by simp, hEff⟩⟩

theorem teamCoverage_nonempty (deck : List Card) (defender : EnergyType) :
    TeamCoverage deck defender → deck ≠ [] := by
  intro hCov hEmpty
  rcases hCov with ⟨card, hMem, _⟩
  have : card ∈ ([] : List Card) := by simp [hEmpty] at hMem
  cases this

theorem teamCoverage_pair_symm (c1 c2 : Card) (defender : EnergyType) :
    TeamCoverage [c1, c2] defender ↔ TeamCoverage [c2, c1] defender := by
  constructor
  · intro h
    have h' := (teamCoverage_pair c1 c2 defender).1 h
    have h'' : TypeEffective c2.energyType defender ∨ TypeEffective c1.energyType defender := by
      simpa [Or.comm] using h'
    exact (teamCoverage_pair c2 c1 defender).2 h''
  · intro h
    have h' := (teamCoverage_pair c2 c1 defender).1 h
    have h'' : TypeEffective c1.energyType defender ∨ TypeEffective c2.energyType defender := by
      simpa [Or.comm] using h'
    exact (teamCoverage_pair c1 c2 defender).2 h''

theorem teamCoverage_pair_left (c1 c2 : Card) (defender : EnergyType)
    (h : TypeEffective c1.energyType defender) :
    TeamCoverage [c1, c2] defender := by
  exact (teamCoverage_pair c1 c2 defender).2 (Or.inl h)

theorem teamCoverage_pair_right (c1 c2 : Card) (defender : EnergyType)
    (h : TypeEffective c2.energyType defender) :
    TeamCoverage [c1, c2] defender := by
  exact (teamCoverage_pair c1 c2 defender).2 (Or.inr h)

theorem teamCoverage_swap (c1 c2 : Card) (defender : EnergyType) :
    TeamCoverage [c1, c2] defender ↔ TeamCoverage [c2, c1] defender := by
  exact teamCoverage_pair_symm c1 c2 defender

theorem teamCoverage_cons_left (card : Card) (deck : List Card) (defender : EnergyType)
    (h : TypeEffective card.energyType defender) :
    TeamCoverage (card :: deck) defender := by
  exact (teamCoverage_cons card deck defender).2 (Or.inl h)

theorem teamCoverage_cons_right (card : Card) (deck : List Card) (defender : EnergyType)
    (h : TeamCoverage deck defender) :
    TeamCoverage (card :: deck) defender := by
  exact (teamCoverage_cons card deck defender).2 (Or.inr h)
theorem typePairCoverage_symm (attacker1 attacker2 : EnergyType) :
    typePairCoverageList attacker1 attacker2 = typePairCoverageList attacker2 attacker1 := by
  ext defender
  simp [typePairCoverageList, Bool.or_comm]

theorem typePairCoverage_left (attacker1 attacker2 defender : EnergyType) :
    TypeEffective attacker1 defender → defender ∈ typePairCoverageList attacker1 attacker2 := by
  intro h
  have hMem : defender ∈ allEnergyTypes := by
    cases defender <;> simp [allEnergyTypes]
  have hOr : typeMultiplier attacker1 defender = 2 ∨ typeMultiplier attacker2 defender = 2 := by
    left
    simpa [TypeEffective] using h
  exact (List.mem_filter.mpr ⟨hMem, by
    simpa [typePairCoverageList] using hOr⟩)

theorem typePairCoverage_right (attacker1 attacker2 defender : EnergyType) :
    TypeEffective attacker2 defender → defender ∈ typePairCoverageList attacker1 attacker2 := by
  intro h
  have hMem : defender ∈ allEnergyTypes := by
    cases defender <;> simp [allEnergyTypes]
  have hOr : typeMultiplier attacker1 defender = 2 ∨ typeMultiplier attacker2 defender = 2 := by
    right
    simpa [TypeEffective] using h
  exact (List.mem_filter.mpr ⟨hMem, by
    simpa [typePairCoverageList] using hOr⟩)

-- ============================================================================
-- TURN ORDER & STAT STAGES
-- ============================================================================

/-- Action priority (higher acts first). -/
inductive MovePriority
  | veryLow
  | low
  | normal
  | high
  | veryHigh
  deriving Repr, BEq, DecidableEq

def priorityValue : MovePriority → Int
  | .veryLow => -2
  | .low => -1
  | .normal => 0
  | .high => 1
  | .veryHigh => 2

theorem priorityValue_ordered (p1 p2 : MovePriority) :
    priorityValue p1 < priorityValue p2 → p1 ≠ p2 := by
  intro h hEq
  cases hEq
  exact (Int.lt_irrefl _ h)

def winsPriority (p1 p2 : MovePriority) : Bool :=
  priorityValue p2 < priorityValue p1

theorem winsPriority_irreflexive (p : MovePriority) : winsPriority p p = false := by
  cases p <;> rfl

theorem winsPriority_swap (p1 p2 : MovePriority) :
    winsPriority p1 p2 = true → winsPriority p2 p1 = false := by
  intro h
  cases p1 <;> cases p2 <;> simp [winsPriority, priorityValue] at h ⊢


@[simp] theorem winsPriority_high_normal : winsPriority .high .normal = true := by
  simp [winsPriority, priorityValue]

@[simp] theorem winsPriority_normal_high : winsPriority .normal .high = false := by
  simp [winsPriority, priorityValue]

@[simp] theorem winsPriority_veryHigh_high : winsPriority .veryHigh .high = true := by
  simp [winsPriority, priorityValue]

@[simp] theorem winsPriority_low_normal : winsPriority .low .normal = false := by
  simp [winsPriority, priorityValue]
/-- Stat stage between -6 and 6 (bounded). -/
structure StatStage where
  val : Int
  lower : -6 ≤ val
  upper : val ≤ 6

def clampStage (stage : Int) : StatStage :=
  if hLow : stage < -6 then
    { val := -6
      lower := by simp
      upper := by simp }
  else if hHigh : stage > 6 then
    { val := 6
      lower := by simp
      upper := by simp }
  else
    { val := stage
      lower := by
        exact by omega
      upper := by
        exact by omega }

theorem clampStage_le (stage : Int) : (clampStage stage).val ≤ 6 := by
  unfold clampStage
  by_cases hLow : stage < -6
  · simp [hLow]
  · by_cases hHigh : stage > 6
    · simp [hLow, hHigh]
    · have hLe : stage ≤ 6 := by omega
      simp [hLow, hHigh, hLe]

theorem clampStage_ge (stage : Int) : -6 ≤ (clampStage stage).val := by
  unfold clampStage
  by_cases hLow : stage < -6
  · simp [hLow]
  · by_cases hHigh : stage > 6
    · simp [hLow, hHigh]
    · have hLe : -6 ≤ stage := by omega
      simp [hLow, hHigh, hLe]

theorem clampStage_id (stage : Int) (hLow : -6 ≤ stage) (hHigh : stage ≤ 6) :
    (clampStage stage).val = stage := by
  unfold clampStage
  have hLow' : ¬ stage < -6 := by
    exact (by omega)
  have hHigh' : ¬ stage > 6 := by
    exact (by omega)
  simp [hLow', hHigh']

def stageMultiplier (stage : StatStage) : Int :=
  stage.val + 6

theorem stageMultiplier_nonneg (stage : StatStage) : 0 ≤ stageMultiplier stage := by
  unfold stageMultiplier
  have h := Int.add_le_add_right stage.lower 6
  simpa using h

theorem stageMultiplier_le (stage : StatStage) : stageMultiplier stage ≤ 12 := by
  unfold stageMultiplier
  have h := Int.add_le_add_right stage.upper 6
  simpa using h

-- ============================================================================
-- GAME THEORY ASPECTS
-- ============================================================================

def bestResponseA {α β : Type} (u : α → β → Nat) (a : α) (b : β) : Prop :=
  ∀ a', u a' b ≤ u a b

def bestResponseB {α β : Type} (u : α → β → Nat) (a : α) (b : β) : Prop :=
  ∀ b', u a b' ≤ u a b

def nashEq {α β : Type} (u1 u2 : α → β → Nat) (a : α) (b : β) : Prop :=
  bestResponseA u1 a b ∧ bestResponseB u2 a b

theorem bestResponseA_of_const {α β : Type} (u : α → β → Nat) (a : α) (b : β)
    (hConst : ∀ a', u a' b = u a b) : bestResponseA u a b := by
  intro a'
  simp [hConst a']

theorem bestResponseB_of_const {α β : Type} (u : α → β → Nat) (a : α) (b : β)
    (hConst : ∀ b', u a b' = u a b) : bestResponseB u a b := by
  intro b'
  simp [hConst b']

theorem nashEq_of_const {α β : Type} (u1 u2 : α → β → Nat) (a : α) (b : β)
    (h1 : ∀ a', u1 a' b = u1 a b) (h2 : ∀ b', u2 a b' = u2 a b) :
    nashEq u1 u2 a b := by
  exact ⟨bestResponseA_of_const u1 a b h1, bestResponseB_of_const u2 a b h2⟩

def symmetricPayoff {α : Type} (u : α → α → Nat) : Prop :=
  ∀ a b, u a b = u b a

def nashSymmetric {α : Type} (u : α → α → Nat) (a b : α) : Prop :=
  bestResponseA u a b ∧ bestResponseB u a b

theorem nashSymmetric_swap {α : Type} (u : α → α → Nat) (a b : α)
    (hSym : symmetricPayoff u) :
    nashSymmetric u a b → nashSymmetric u b a := by
  intro h
  rcases h with ⟨hA, hB⟩
  constructor
  · intro a'
    have hB' := hB a'
    simpa [hSym a a', hSym a b] using hB'
  · intro b'
    have hA' := hA b'
    simpa [hSym b' b, hSym a b] using hA'

def dominates {α β : Type} (u : α → β → Nat) (a1 a2 : α) : Prop :=
  ∀ b, u a2 b ≤ u a1 b

theorem dominates_refl {α β : Type} (u : α → β → Nat) (a : α) : dominates u a a := by
  intro b
  exact Nat.le_refl _

theorem dominates_trans {α β : Type} (u : α → β → Nat) (a1 a2 a3 : α) :
    dominates u a1 a2 → dominates u a2 a3 → dominates u a1 a3 := by
  intro h12 h23 b
  exact Nat.le_trans (h23 b) (h12 b)

def riskRewardGap (reward risk : Nat) : Nat :=
  reward - risk

theorem riskRewardGap_self (reward : Nat) : riskRewardGap reward reward = 0 := by
  simp [riskRewardGap]

theorem riskRewardGap_zero_of_le (reward risk : Nat) (h : reward ≤ risk) :
    riskRewardGap reward risk = 0 := by
  exact Nat.sub_eq_zero_of_le h

theorem riskRewardGap_pos_of_lt (reward risk : Nat) (h : risk < reward) :
    riskRewardGap reward risk > 0 := by
  exact Nat.sub_pos_of_lt h

theorem riskRewardGap_le_reward (reward risk : Nat) : riskRewardGap reward risk ≤ reward := by
  simp [riskRewardGap, Nat.sub_le]

theorem riskRewardGap_mono_reward (reward reward' risk : Nat) (h : reward ≤ reward') :
    riskRewardGap reward risk ≤ riskRewardGap reward' risk := by
  simpa [riskRewardGap] using Nat.sub_le_sub_right h risk

def predictionPayoff (reward penalty : Nat) (correct : Bool) : Int :=
  if correct then Int.ofNat reward else - (Int.ofNat penalty)

theorem predictionPayoff_true (reward penalty : Nat) :
    predictionPayoff reward penalty true = Int.ofNat reward := by
  simp [predictionPayoff]

theorem predictionPayoff_false (reward penalty : Nat) :
    predictionPayoff reward penalty false = - (Int.ofNat penalty) := by
  simp [predictionPayoff]

theorem predictionPayoff_true_nonneg (reward penalty : Nat) :
    0 ≤ predictionPayoff reward penalty true := by
  simp [predictionPayoff]; omega

theorem predictionPayoff_false_nonpos (reward penalty : Nat) :
    predictionPayoff reward penalty false ≤ 0 := by
  simp [predictionPayoff]; omega

theorem predictionPayoff_zero_reward (penalty : Nat) :
    predictionPayoff 0 penalty true = 0 := by
  simp [predictionPayoff]

theorem predictionPayoff_zero_penalty (reward : Nat) :
    predictionPayoff reward 0 false = 0 := by
  simp [predictionPayoff]

theorem predictionPayoff_true_le_reward (reward penalty : Nat) :
    predictionPayoff reward penalty true ≤ Int.ofNat reward := by
  simp [predictionPayoff]

theorem predictionPayoff_false_ge_neg (reward penalty : Nat) :
    -(Int.ofNat penalty) ≤ predictionPayoff reward penalty false := by
  simp [predictionPayoff]

theorem predictionPayoff_abs_le (reward penalty : Nat) (correct : Bool) :
    Int.natAbs (predictionPayoff reward penalty correct) ≤ reward + penalty := by
  cases correct <;> simp [predictionPayoff, Nat.le_add_right, Nat.le_add_left]

def switchAdvantage (before after : Nat) : Nat :=
  before - after

theorem switchAdvantage_self (damage : Nat) : switchAdvantage damage damage = 0 := by
  simp [switchAdvantage]

theorem switchAdvantage_zero_of_le (before after : Nat) (h : before ≤ after) :
    switchAdvantage before after = 0 := by
  exact Nat.sub_eq_zero_of_le h

theorem switchAdvantage_mono_before (before before' after : Nat) (h : before ≤ before') :
    switchAdvantage before after ≤ switchAdvantage before' after := by
  simpa [switchAdvantage] using Nat.sub_le_sub_right h after

theorem switchAdvantage_le_before (before after : Nat) :
    switchAdvantage before after ≤ before := by
  simp [switchAdvantage, Nat.sub_le]

-- ============================================================================
-- DAMAGE CALCULATION EXTENSIONS
-- ============================================================================

/-- Same-Type Attack Bonus (STAB): 3/2 multiplier when types match. -/
def applySTAB (damage : Nat) (attackerType attackType : EnergyType) : Nat :=
  if attackerType = attackType then damage + damage / 2 else damage

/-- Critical hit doubles damage. -/
def applyCritical (damage : Nat) (isCrit : Bool) : Nat :=
  if isCrit then damage * 2 else damage

/-- Weather-based damage adjustment. -/
def applyWeather (damage : Nat) (attackerType : EnergyType) (weather : Weather) : Nat :=
  match weather with
  | .clear => damage
  | .sunny => if attackerType = .fire then damage * 2 else damage
  | .rain => if attackerType = .water then damage * 2 else damage
  | .sandstorm => if attackerType = .fighting then damage + 10 else damage
  | .hail => if attackerType = .water then damage + 10 else damage

/-- Extended damage formula with STAB, critical hits, and weather. -/
def calculateDamageExtended (attack : Attack) (attackerType attackType : EnergyType) (defender : Card)
    (isCrit : Bool) (weather : Weather) : Nat :=
  let base := calculateDamage attack attackerType defender
  let withStab := applySTAB base attackerType attackType
  let withCrit := applyCritical withStab isCrit
  applyWeather withCrit attackerType weather

theorem applySTAB_same (damage : Nat) (t : EnergyType) :
    applySTAB damage t t = damage + damage / 2 := by
  simp [applySTAB]

theorem applySTAB_diff (damage : Nat) (t1 t2 : EnergyType) (h : t1 ≠ t2) :
    applySTAB damage t1 t2 = damage := by
  simp [applySTAB, h]

theorem applySTAB_zero (t1 t2 : EnergyType) : applySTAB 0 t1 t2 = 0 := by
  simp [applySTAB]

theorem applySTAB_ge (damage : Nat) (t1 t2 : EnergyType) :
    damage ≤ applySTAB damage t1 t2 := by
  by_cases h : t1 = t2
  · simp [applySTAB, h, Nat.le_add_right]
  · simp [applySTAB, h]

theorem applySTAB_le_add_half (damage : Nat) (t1 t2 : EnergyType) :
    applySTAB damage t1 t2 ≤ damage + damage / 2 := by
  by_cases h : t1 = t2
  · simp [applySTAB, h]
  · simp [applySTAB, h, Nat.le_add_right]

theorem applyCritical_true (damage : Nat) : applyCritical damage true = damage * 2 := by
  simp [applyCritical]

theorem applyCritical_false (damage : Nat) : applyCritical damage false = damage := by
  simp [applyCritical]

theorem applyCritical_zero (isCrit : Bool) : applyCritical 0 isCrit = 0 := by
  cases isCrit <;> simp [applyCritical]

theorem applyCritical_ge (damage : Nat) (isCrit : Bool) :
    damage ≤ applyCritical damage isCrit := by
  cases isCrit with
  | false =>
    simp [applyCritical]
  | true =>
    have hPos : (0:Nat) < 2 := by decide
    simp [applyCritical]
    exact Nat.le_mul_of_pos_right damage hPos

theorem applyCritical_le (damage : Nat) (isCrit : Bool) :
    applyCritical damage isCrit ≤ damage * 2 := by
  cases isCrit with
  | false =>
    have hPos : (0:Nat) < 2 := by decide
    simp [applyCritical]
    exact Nat.le_mul_of_pos_right damage hPos
  | true =>
    simp [applyCritical]

theorem applyWeather_clear (damage : Nat) (t : EnergyType) :
    applyWeather damage t .clear = damage := by
  simp [applyWeather]

theorem applyWeather_zero_cases (t : EnergyType) (w : Weather) :
    applyWeather 0 t w = 0 ∨ applyWeather 0 t w = 10 := by
  cases w with
  | clear => simp [applyWeather]
  | sunny => simp [applyWeather]
  | rain => simp [applyWeather]
  | sandstorm =>
    by_cases h : t = .fighting
    · simp [applyWeather, h]
    · simp [applyWeather, h]
  | hail =>
    by_cases h : t = .water
    · simp [applyWeather, h]
    · simp [applyWeather, h]

theorem applyWeather_sunny_fire (damage : Nat) :
    applyWeather damage .fire .sunny = damage * 2 := by
  simp [applyWeather]

theorem applyWeather_sunny_nonfire (damage : Nat) (t : EnergyType) (h : t ≠ .fire) :
    applyWeather damage t .sunny = damage := by
  simp [applyWeather, h]

theorem applyWeather_rain_water (damage : Nat) :
    applyWeather damage .water .rain = damage * 2 := by
  simp [applyWeather]

theorem applyWeather_rain_nonwater (damage : Nat) (t : EnergyType) (h : t ≠ .water) :
    applyWeather damage t .rain = damage := by
  simp [applyWeather, h]

theorem applyWeather_sandstorm_fighting (damage : Nat) :
    applyWeather damage .fighting .sandstorm = damage + 10 := by
  simp [applyWeather]

theorem applyWeather_sandstorm_nonfighting (damage : Nat) (t : EnergyType) (h : t ≠ .fighting) :
    applyWeather damage t .sandstorm = damage := by
  simp [applyWeather, h]

theorem applyWeather_hail_water (damage : Nat) :
    applyWeather damage .water .hail = damage + 10 := by
  simp [applyWeather]

theorem applyWeather_hail_nonwater (damage : Nat) (t : EnergyType) (h : t ≠ .water) :
    applyWeather damage t .hail = damage := by
  simp [applyWeather, h]

theorem applyWeather_ge (damage : Nat) (t : EnergyType) (w : Weather) :
    damage ≤ applyWeather damage t w := by
  cases w with
  | clear =>
    simp [applyWeather]
  | sunny =>
    by_cases h : t = .fire
    · have hPos : (0:Nat) < 2 := by decide
      simpa [applyWeather, h] using Nat.le_mul_of_pos_right damage hPos
    · simp [applyWeather, h]
  | rain =>
    by_cases h : t = .water
    · have hPos : (0:Nat) < 2 := by decide
      simpa [applyWeather, h] using Nat.le_mul_of_pos_right damage hPos
    · simp [applyWeather, h]
  | sandstorm =>
    by_cases h : t = .fighting
    · simp [applyWeather, h, Nat.le_add_right]
    · simp [applyWeather, h]
  | hail =>
    by_cases h : t = .water
    · simp [applyWeather, h, Nat.le_add_right]
    · simp [applyWeather, h]

theorem calculateDamageExtended_ge_base (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) (isCrit : Bool) (weather : Weather) :
    calculateDamage attack attackerType defender ≤
      calculateDamageExtended attack attackerType attackType defender isCrit weather := by
  unfold calculateDamageExtended
  have h1 : calculateDamage attack attackerType defender ≤
      applySTAB (calculateDamage attack attackerType defender) attackerType attackType := by
    simpa using applySTAB_ge (calculateDamage attack attackerType defender) attackerType attackType
  have h2 : applySTAB (calculateDamage attack attackerType defender) attackerType attackType ≤
      applyCritical (applySTAB (calculateDamage attack attackerType defender) attackerType attackType) isCrit := by
    simpa using applyCritical_ge
      (applySTAB (calculateDamage attack attackerType defender) attackerType attackType) isCrit
  have h3 : applyCritical (applySTAB (calculateDamage attack attackerType defender) attackerType attackType) isCrit ≤
      applyWeather
        (applyCritical (applySTAB (calculateDamage attack attackerType defender) attackerType attackType) isCrit)
        attackerType weather := by
    simpa using applyWeather_ge
      (applyCritical (applySTAB (calculateDamage attack attackerType defender) attackerType attackType) isCrit)
      attackerType weather
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

theorem calculateDamageExtended_clear (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) (isCrit : Bool) :
    calculateDamageExtended attack attackerType attackType defender isCrit .clear =
      applyCritical (applySTAB (calculateDamage attack attackerType defender) attackerType attackType) isCrit := by
  simp [calculateDamageExtended, applyWeather]

theorem calculateDamageExtended_clear_no_crit (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) :
    calculateDamageExtended attack attackerType attackType defender false .clear =
      applySTAB (calculateDamage attack attackerType defender) attackerType attackType := by
  simp [calculateDamageExtended, applyWeather, applyCritical]

theorem calculateDamageExtended_clear_crit (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) :
    calculateDamageExtended attack attackerType attackType defender true .clear =
      applySTAB (calculateDamage attack attackerType defender) attackerType attackType * 2 := by
  simp [calculateDamageExtended, applyWeather, applyCritical]

theorem calculateDamageExtended_clear_no_crit_same (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) (h : attackerType = attackType) :
    calculateDamageExtended attack attackerType attackType defender false .clear =
      calculateDamage attack attackerType defender +
        calculateDamage attack attackerType defender / 2 := by
  simp [calculateDamageExtended, applyWeather, applyCritical, applySTAB, h]

theorem calculateDamageExtended_clear_no_crit_diff (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) (h : attackerType ≠ attackType) :
    calculateDamageExtended attack attackerType attackType defender false .clear =
      calculateDamage attack attackerType defender := by
  simp [calculateDamageExtended, applyWeather, applyCritical, applySTAB, h]

theorem calculateDamageExtended_clear_crit_same (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) (h : attackerType = attackType) :
    calculateDamageExtended attack attackerType attackType defender true .clear =
      (calculateDamage attack attackerType defender +
          calculateDamage attack attackerType defender / 2) * 2 := by
  simp [calculateDamageExtended, applyWeather, applyCritical, applySTAB, h]

theorem calculateDamageExtended_clear_crit_diff (attack : Attack) (attackerType attackType : EnergyType)
    (defender : Card) (h : attackerType ≠ attackType) :
    calculateDamageExtended attack attackerType attackType defender true .clear =
      calculateDamage attack attackerType defender * 2 := by
  simp [calculateDamageExtended, applyWeather, applyCritical, applySTAB, h]

-- ============================================================================
-- MATCHUP ANALYSIS FRAMEWORK
-- ============================================================================

/-- Matchup statistics. -/
structure MatchupStats where
  totalGames : Nat
  player1Wins : Nat
  player2Wins : Nat
  averageTurns : Nat
  deriving Repr

/-- Win rate as percentage (0-100). -/
def winRate (stats : MatchupStats) (player : PlayerId) : Nat :=
  if stats.totalGames == 0 then 50
  else match player with
    | .playerOne => Nat.min 100 ((stats.player1Wins * 100) / stats.totalGames)
    | .playerTwo => Nat.min 100 ((stats.player2Wins * 100) / stats.totalGames)

theorem winRate_playerOne_zero (stats : MatchupStats) (h : stats.totalGames = 0) :
    winRate stats .playerOne = 50 := by
  simp [winRate, h]

theorem winRate_playerTwo_zero (stats : MatchupStats) (h : stats.totalGames = 0) :
    winRate stats .playerTwo = 50 := by
  simp [winRate, h]

theorem winRate_zero_of_no_games (stats : MatchupStats) (player : PlayerId)
    (h : stats.totalGames = 0) :
    winRate stats player = 50 := by
  cases player <;> simp [winRate, h]

theorem winRate_playerOne_allWins (stats : MatchupStats) (hGames : stats.totalGames > 0)
    (hWins : stats.player1Wins = stats.totalGames) :
    winRate stats .playerOne = 100 := by
  have hPos : 0 < stats.totalGames := hGames
  have hNe : stats.totalGames ≠ 0 := Nat.ne_of_gt hPos
  have hDiv : stats.totalGames * 100 / stats.totalGames = 100 := by
    simpa [Nat.mul_comm] using Nat.mul_div_right 100 hPos
  simp [winRate, hWins, hNe, hDiv]



theorem winRate_playerTwo_allWins (stats : MatchupStats) (hGames : stats.totalGames > 0)
    (hWins : stats.player2Wins = stats.totalGames) :
    winRate stats .playerTwo = 100 := by
  have hPos : 0 < stats.totalGames := hGames
  have hNe : stats.totalGames ≠ 0 := Nat.ne_of_gt hPos
  have hDiv : stats.totalGames * 100 / stats.totalGames = 100 := by
    simpa [Nat.mul_comm] using Nat.mul_div_right 100 hPos
  simp [winRate, hWins, hNe, hDiv]

theorem winRate_bounds (stats : MatchupStats) (player : PlayerId) :
    winRate stats player ≤ 100 := by
  cases h : stats.totalGames with
  | zero =>
    have h50 : (50 : Nat) ≤ 100 := by decide
    cases player <;> simp [winRate, h, h50]
  | succ n =>
    cases player
    ·
      have hMin :
          Nat.min 100 ((stats.player1Wins * 100) / (n + 1)) ≤ 100 := by
        exact Nat.min_le_left _ _
      simpa [winRate, h] using hMin
    ·
      have hMin :
          Nat.min 100 ((stats.player2Wins * 100) / (n + 1)) ≤ 100 := by
        exact Nat.min_le_left _ _
      simpa [winRate, h] using hMin
/-- Determine advantage based on type matchup. -/
def typeAdvantage (attacker defender : EnergyType) : Int :=
  -- Simplified type chart
  match attacker, defender with
  | .fire, .grass => 1
  | .water, .fire => 1
  | .grass, .water => 1
  | .lightning, .water => 1
  | .fighting, .colorless => 1
  | .psychic, .fighting => 1
  | _, _ => 0

theorem typeAdvantage_self (t : EnergyType) : typeAdvantage t t = 0 := by
  cases t <;> simp [typeAdvantage]

theorem typeAdvantage_nonneg (attacker defender : EnergyType) : 0 ≤ typeAdvantage attacker defender := by
  cases attacker <;> cases defender <;> decide

theorem typeAdvantage_le_one (attacker defender : EnergyType) : typeAdvantage attacker defender ≤ 1 := by
  cases attacker <;> cases defender <;> decide

theorem typeAdvantage_bounds (attacker defender : EnergyType) :
    0 ≤ typeAdvantage attacker defender ∧ typeAdvantage attacker defender ≤ 1 := by
  exact ⟨typeAdvantage_nonneg attacker defender, typeAdvantage_le_one attacker defender⟩

/-- Estimate matchup advantage based on type chart. -/
def estimateMatchup (deck1 deck2 : List Card) : Int :=
  let types1 := deck1.map (·.energyType)
  let types2 := deck2.map (·.energyType)
  let advantages := types1.foldl (fun acc t1 =>
    acc + types2.foldl (fun acc2 t2 => acc2 + typeAdvantage t1 t2) 0) 0
  let disadvantages := types2.foldl (fun acc t2 =>
    acc + types1.foldl (fun acc1 t1 => acc1 + typeAdvantage t2 t1) 0) 0
  advantages - disadvantages

theorem foldl_const {α β : Type} (init : α) (xs : List β) :
    List.foldl (fun acc _ => acc) init xs = init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp [List.foldl, ih]

theorem estimateMatchup_nil_left (deck : List Card) : estimateMatchup [] deck = 0 := by
  simp [estimateMatchup, foldl_const]

theorem estimateMatchup_nil_right (deck : List Card) : estimateMatchup deck [] = 0 := by
  simp [estimateMatchup, foldl_const]

-- ============================================================================
-- EXAMPLE USAGE
-- ============================================================================

#eval findLethal
  { card := sampleCharmander, damage := 0, status := none, energy := [.fire] }
  { card := samplePikachu, damage := 40, status := none, energy := [.lightning] }

#eval solveNPly
  { card := sampleSquirtle, damage := 0, status := none, energy := [] }
  { card := sampleCharmander, damage := 0, status := none, energy := [.fire] }
  2

#eval checkWellFormed sampleCharmander

end PokemonLean.GameTheory
