# PokemonLean

[![CI](https://github.com/[redacted]/PokemonLean/actions/workflows/ci.yml/badge.svg)](https://github.com/[redacted]/PokemonLean/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.x-blue)](https://lean-lang.org/lean4/doc/)

**PokemonLean** is a Lean 4 formal verification project for the Pokémon Trading Card Game (TCG). It encodes game objects, legal transitions, deck legality, solver behavior, and probabilistic mechanics, then machine-checks invariants and strategy results.

## Project snapshot

- **Lean modules:** 67 (`Main.lean`, `PokemonLean.lean`, `PokemonLean/**/*.lean`)
- **Lean lines:** 27,071
- **Theorems:** 1,927
- **Definitions (`def`):** 1,106

## Architecture overview

- **Root entry layer:** `Main` runs demonstrations; `PokemonLean` is the aggregate import root.
- **Core semantic layer:** `PokemonLean.Core.Types` and `PokemonLean.Core.Card` provide shared card/type foundations.
- **Feature/theorem layer:** 63 `PokemonLean.*` modules cover semantics, solver reasoning, deck systems, official rules, probability, simulation, replay validation, and game-theoretic analysis.

## Key results

- **Card conservation:** `reachable_card_conservation` (`PokemonLean.Semantics`), `stepProb_card_conservation` (`PokemonLean.StochasticSemantics`)
- **Win monotonicity:** `stepProb_win_monotonic` (`PokemonLean.StochasticSemantics`)
- **Progress:** `progress` (`PokemonLean.SemanticsDeep`), `legal_progress` (`PokemonLean.Semantics`)
- **Game termination:** `game_terminates` (`PokemonLean.SemanticsDeep`)
- **Solver soundness:** `solve_legal`, `solve_complete_lethal` (`PokemonLean.SolverSoundness`)
- **Deck legality:** `checkDeckLegal_iff` (`PokemonLean.DeckLegality`)
- **Official rules validation:** `spent_turn`, `ko_correct_prizes` (`PokemonLean.OfficialRules`)
- **Game-theoretic results:** `prize_trade_winner`, `first_player_advantage_bound` (`PokemonLean.GameTheoreticResults`)
- **Stochastic semantics:** `stepProb_deterministic_embedding`, `expected_damage_bounds_match_probability` (`PokemonLean.StochasticSemantics`)
- **Nash equilibrium:** `nashEq_of_const` (`PokemonLean.GameTheory`), `mixedNash_swap` (`PokemonLean.MixedStrategy`)

## Module catalog (all Lean modules)

| Module | Layer | Description |
|---|---|---|
| `Main` | Root | Executable entry point demonstrating solver-backed gameplay traces. |
| `PokemonLean` | Root | Root library module importing the full verified PokemonLean stack. |
| `PokemonLean.Core.Card` | PokemonLean.Core | Evolution stages in the Pokémon TCG. |
| `PokemonLean.Core.Types` | PokemonLean.Core | The 11 Pokémon types in the TCG. Note: Colorless is NOT a Pokémon type — it is an energy type only. |
| `PokemonLean.ACESpec` | PokemonLean | Named ACE SPEC trainer cards. |
| `PokemonLean.Abilities` | PokemonLean | types: AbilityType, Ability; defs: canPayAbilityCost, payAbilityCost; theorems: payAbilityCost_sound, payAbilityCost_energy_length |
| `PokemonLean.AbilitySystem` | PokemonLean | types: AbilityName, AbilityTrigger; defs: intimidateAbility, drizzleAbility; theorems: one_ability_or_none, not_both_ability_and_none |
| `PokemonLean.AncientTrait` | PokemonLean | types: TraitKind, BreakEvolution; defs: attackAllowance, attachmentAllowance; theorems: attackAllowance_pos, attackAllowance_le_two |
| `PokemonLean.ArchetypeMatchups` | PokemonLean | Matchup result: favorable, even, or unfavorable |
| `PokemonLean.Archetypes` | PokemonLean | The four fundamental deck archetypes |
| `PokemonLean.Basic` | PokemonLean | types: EnergyType, StatusCondition; defs: isTrainer, EffectStack; theorems: removeFirstEnergy_length, consumeEnergyCost_sound |
| `PokemonLean.BoardState` | PokemonLean | types: BoardPokemon, BoardState; defs: defaultBenchLimit, skyFieldBenchLimit; theorems: isSkyField_some_eq, benchLimit_no_stadium |
| `PokemonLean.CardEffects` | PokemonLean | Formalized iconic card effects with card-conservation proofs. |
| `PokemonLean.CardPool` | PokemonLean | Prize value when this card is KO'd. |
| `PokemonLean.Cards` | PokemonLean | defs: scatterbug, pineco |
| `PokemonLean.Corpus` | PokemonLean | defs: cardWellFormed, corpusWellFormed; theorems: corpusWellFormed_trivial |
| `PokemonLean.DamageCounters` | PokemonLean | Damage counters are placed in 10-point increments in the Pokémon TCG. |
| `PokemonLean.Deck` | PokemonLean | Count how many cards in `deck` have a given `name`. |
| `PokemonLean.DeckBuilding` | PokemonLean | High-level deck-building categories. |
| `PokemonLean.DeckConstraints` | PokemonLean | types: DeckCardKind, DeckEntry; defs: Deck, totalCards; theorems: totalCards_nil, totalCards_singleton |
| `PokemonLean.DeckLegality` | PokemonLean | Executable deck legality checker with soundness/completeness proofs. |
| `PokemonLean.Decks` | PokemonLean | types: DeckRules; defs: standardRules, isPokemon; theorems: pokemonCount_nil, trainerCount_nil |
| `PokemonLean.EnergyAcceleration` | PokemonLean | types: AccelerationState; defs: initialAccelerationState, markAcceleration; theorems: initialAccelerationState_manual_unused, initialAccelerationState_effects_zero |
| `PokemonLean.EnergyManagement` | PokemonLean | How many units of energy a special energy card provides |
| `PokemonLean.Evolution` | PokemonLean | A Pokémon can evolve if: 1. The evolution card's stage is the next stage of the current card 2. The evolution card's evolvesFrom matches the current card's name 3. The Pokémon was not played this turn (currentTurn > turnPlayed) 4. The Pokémon was not already evolved this turn (currentTurn > lastEvolvedTurn) |
| `PokemonLean.Format` | PokemonLean | types: TCGFormat, ReleaseDate; defs: releaseDateCode, releaseDateBeforeOrOn; theorems: releaseDateBeforeOrOn_refl, releaseDateBeforeOrOn_trans |
| `PokemonLean.GXAttacks` | PokemonLean | types: OncePerGameKind, OncePerGameState; defs: initialOncePerGame, canUseGX; theorems: initial_gx_available, initial_vstar_available |
| `PokemonLean.GameTheoreticResults` | PokemonLean | Prize-race, tempo, and deck-exhaustion theorems for strategy analysis. |
| `PokemonLean.GameTheory` | PokemonLean | Result of N-ply lookahead solver. |
| `PokemonLean.HandDisruption` | PokemonLean | Supporter cards that disrupt the opponent's hand |
| `PokemonLean.HandManagement` | PokemonLean | types: HandDisruptionEffect; defs: drawPhaseCount, professorsResearchCount; theorems: handSize_eq_length, drawCards_zero |
| `PokemonLean.LostZone` | PokemonLean | types: GameZone, LostZoneItem; defs: isRecoverableZone, ofPlayerState; theorems: isRecoverableZone_false_iff, isRecoverableZone_true_iff |
| `PokemonLean.LostZoneBox` | PokemonLean | types: LostZoneBoxDeck, GamePhase; defs: deckTotalCount, isValidLostZoneBoxDeck; theorems: standardLostBoxDeck_valid, standardLostBoxDeck_total |
| `PokemonLean.LostZoneCombos` | PokemonLean | defs: giratinaLostImpactDamage; theorems: flower_then_colress_lz, colress_then_flower_lz |
| `PokemonLean.LostZoneThresholds` | PokemonLean | types: LostZoneThreshold, ColressResult; defs: thresholdValue, thresholdMet; theorems: hasThresholdMet_iff, provision_le_mirageGate |
| `PokemonLean.Matchup` | PokemonLean | The four canonical TCG deck archetypes. |
| `PokemonLean.MixedStrategy` | PokemonLean | A mixed strategy is just a finite support of pure strategies. We measure its "totalWeight" as the size of the support. |
| `PokemonLean.Mulligan` | PokemonLean | A card is a basic Pokémon if it is not a trainer (i.e., it has attacks). |
| `PokemonLean.OfficialRules` | PokemonLean | Lean formalization of official turn, evolution, supporter, energy, and prize rules. |
| `PokemonLean.OptimalPlay` | PokemonLean | Micro-format minimax model proving optimal strategy existence and OHKO dominance. |
| `PokemonLean.Planner` | PokemonLean | defs: planOneTurn; theorems: planOneTurn_turnOneActions |
| `PokemonLean.PrizeCards` | PokemonLean | types: PokemonCategory, CategorizedPokemon; defs: prizesForCategory, initialPrizeCount; theorems: prizesForCategory_pos, basic_gives_one |
| `PokemonLean.PrizeDenial` | PokemonLean | Prize worth when a Pokemon is knocked out |
| `PokemonLean.Prizes` | PokemonLean | types: PrizeTier, PrizeCard; defs: prizeTierValue, prizeCardValue; theorems: prizeTierValue_pos, prizeTierValue_le_three |
| `PokemonLean.Probability` | PokemonLean | Discrete probability distributions and expected-value lemmas for coin-flip mechanics. |
| `PokemonLean.Replay` | PokemonLean | A single step in a game trace: the action taken and the resulting state. |
| `PokemonLean.ReplayValidation` | PokemonLean | Replay log validator with soundness/completeness and final-state winner checks. |
| `PokemonLean.RetreatMechanics` | PokemonLean | types: RetreatCost, SwitchEffect; defs: RetreatCost.free, RetreatCost.one; theorems: free_retreat_cost_zero, one_retreat_cost |
| `PokemonLean.Rotation` | PokemonLean | defs: discardRetreatEnergy, isFreeRetreat; theorems: discardRetreatEnergy_nil, discardRetreatEnergy_card |
| `PokemonLean.Semantics` | PokemonLean | types: Action, StepError; defs: benchLimit, playTrainer; theorems: step_activePlayer_endTurn, step_activePlayer_playPokemonToBench |
| `PokemonLean.SemanticsDeep` | PokemonLean | Metatheory for semantics: progress, determinism, and game termination. |
| `PokemonLean.Simulator` | PokemonLean | Fuel-bounded strategy simulation with reachability and invariant-preservation proofs. |
| `PokemonLean.Solver` | PokemonLean | types: TurnSolverResult, TwoPlyResult; defs: maxDamageFromAttacks, attackDamage; theorems: bestAttachmentFrom_optimal, bestAttachmentFrom_mem |
| `PokemonLean.SolverSoundness` | PokemonLean | Proof bridge showing solver outputs are legal, bounded, and complete. |
| `PokemonLean.SpecialConditions` | PokemonLean | Pokémon Tool items that can be attached (one per Pokémon). |
| `PokemonLean.Stadium` | PokemonLean | Stadium effects that modify the game field for both players. |
| `PokemonLean.StatusEffects` | PokemonLean | Result of a coin flip: heads = true, tails = false |
| `PokemonLean.StochasticSemantics` | PokemonLean | Probabilistic semantics preserving card counts, validity, and win monotonicity. |
| `PokemonLean.Switching` | PokemonLean | types: SwitchError; defs: removeAt, switchWithBenchIndex; theorems: removeAt, removeAt |
| `PokemonLean.Tournament` | PokemonLean | types: PlayerProfile, MatchResult; defs: winnerProfile, loserProfile; theorems: scoreDelta_nonneg, totalPoints_nil |
| `PokemonLean.TournamentRules` | PokemonLean | Official best-of-3 matches have at most three games. |
| `PokemonLean.TrainerCards` | PokemonLean | types: TrainerKind, TrainerEffect; defs: trainerName, isTrainerCard; theorems: supporterCount_le_length, itemCount_le_length |
| `PokemonLean.TrainerSystem` | PokemonLean | types: TrainerKind, TrainerName; defs: professorsResearch, bossOrders; theorems: professors_research_is_supporter, boss_orders_is_supporter |
| `PokemonLean.TurnStructure` | PokemonLean | types: TurnPhase, MainPhaseAction; defs: TurnPhase.toNat, emptyLog; theorems: draw_lt_main, main_lt_attack |
| `PokemonLean.TypeChart` | PokemonLean | Effectiveness multiplier represented as a scaled natural number (×10). So 0 = immune, 5 = not very effective, 10 = normal, 20 = super effective |
| `PokemonLean.VSTAR` | PokemonLean | types: RuleBoxKind, VMAXForm; defs: hasRuleBox, prizesForRuleBox; theorems: prizesForRuleBox_pos, prizesForRuleBox_le_three |
| `PokemonLean.Win` | PokemonLean | Standard number of prize cards per player. |

## Build and run

```bash
~/.elan/bin/lake build
~/.elan/bin/lake env lean --run Main.lean
```
