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
    | .playerOne => (stats.player1Wins * 100) / stats.totalGames
    | .playerTwo => (stats.player2Wins * 100) / stats.totalGames

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

/-- Estimate matchup advantage based on type chart. -/
def estimateMatchup (deck1 deck2 : List Card) : Int :=
  let types1 := deck1.map (·.energyType)
  let types2 := deck2.map (·.energyType)
  let advantages := types1.foldl (fun acc t1 =>
    acc + types2.foldl (fun acc2 t2 => acc2 + typeAdvantage t1 t2) 0) 0
  let disadvantages := types2.foldl (fun acc t2 =>
    acc + types1.foldl (fun acc1 t1 => acc1 + typeAdvantage t2 t1) 0) 0
  advantages - disadvantages

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
