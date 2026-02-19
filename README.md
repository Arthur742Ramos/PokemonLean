# PokemonLean 🧠⚡

[![CI](https://github.com/Arthur742Ramos/PokemonLean/actions/workflows/ci.yml/badge.svg)](https://github.com/Arthur742Ramos/PokemonLean/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.x-blue)](https://lean-lang.org/lean4/doc/)

**PokemonLean** is a comprehensive Lean 4 formal verification project for the Pokémon Trading Card Game (TCG).  
It models game entities, legal actions, deck rules, format legality, matchup abstractions, and solver behavior, then proves key invariants and correctness properties over those models.

## Why formalize a card game? 🎯

Card games have rich rule interactions, hidden state, and exception-heavy mechanics — exactly the kind of domain where formal methods shine.
PokemonLean demonstrates how theorem proving can:

- make rules unambiguous and machine-checkable,
- detect contradictory assumptions early,
- validate solver/planner logic against the rules model,
- and provide reusable, auditable proof artifacts for competitive and academic analysis.

In short: it is both a **serious Lean engineering artifact** and a **playable rules-lab for TCG reasoning**.

## Project at a glance

- **105 Lean modules** under `PokemonLean/`.
- Two complementary layers:
  - `PokemonLean/*.lean`: gameplay systems, semantics, deck construction, strategy, and modern mechanics.
  - `PokemonLean/Core/*.lean`: foundational rule engines, canonical abstractions, and historical/format infrastructure.
- Executable demo in `Main.lean` with solver-backed battle traces.

## Key formalizations 🧩

PokemonLean formalizes:

- **Domain types**: Pokémon/card categories, energy systems, status conditions, rule boxes, trainer kinds, archetypes, formats, regulation marks.
- **State models**: board state, hands/decks/discard/lost zone/prize zones, turn phases, replay traces, tournament match state.
- **Operational semantics**: step functions for legal actions (`play`, `attach`, `retreat`, `endTurn`, evolution/tool/supporter/item usage).
- **Legality systems**: deck constraints (size, copy limits, basic requirements), ACE SPEC limits, format/rotation legality checks.
- **Mechanic-specific models**: Lost Zone thresholds/combos, GX/VSTAR once-per-game gates, stadium and ability interactions, special conditions, mulligans, prize mapping/denial.
- **Optimization/reasoning tools**: attack and attachment solver proofs, planner/game-theoretic abstractions, archetype matchup classification.

## Verified Properties ✅

Representative proven theorems across the codebase include:

- `bestAttack_optimal`, `maxDamage_complete` (`PokemonLean/Solver.lean`): solver outputs are complete/optimal for modeled damage search.
- `step_activePlayer_endTurn`, `step_activePlayer_attachEnergy` (`PokemonLean/Semantics.lean`): transition semantics preserve active-player discipline.
- `deckValidity_length`, `deckValidity_minPokemon` (`PokemonLean/Decks.lean`): legal decks satisfy structural constraints.
- `sixty_card_exact`, `cannot_have_61_cards` (`PokemonLean/DeckConstraints.lean`): total-card constraints are strict and exact.
- `aceSpecDeckConstraint_iff`, `deckValidWithAceSpec_hasSixtyCards` (`PokemonLean/ACESpec.lean`): ACE SPEC legality is enforced and linked to overall deck validity.
- `cannot_use_gx_after_use`, `gx_idempotent` (`PokemonLean/GXAttacks.lean`): once-per-game GX usage cannot be replayed.
- `prizesForRuleBox_le_three`, `vmax_prize_gt_v_prize` (`PokemonLean/VSTAR.lean`): rule-box prize semantics are bounded and ordered.
- `hasThresholdMet_iff`, `threshold_monotone` (`PokemonLean/LostZoneThresholds.lean`): Lost Zone thresholds are exact and monotone.
- `professors_research_is_supporter`, `no_double_supporter` (`PokemonLean/TrainerSystem.lean`): supporter classification and per-turn restrictions are proven.
- `draw_lt_main`, `main_lt_attack`, `phase_lt_trans` (`PokemonLean/TurnStructure.lean`): turn-phase ordering forms a coherent strict progression.
- `prizesForCategory_pos`, `prizesForCategory_le_three` (`PokemonLean/PrizeCards.lean`): prize awards are positive and bounded.
- `allAceSpecNames_nodup` (`PokemonLean/ACESpec.lean`): canonical ACE SPEC identity set is duplicate-free.

## Getting started 🚀

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean toolchain manager)
- Lean 4 (installed via elan)
- `lake` (ships with Lean 4 toolchains)

### Build

```bash
lake build
```

### Run demo

```bash
lake env lean --run Main.lean
```

## Project structure (every Lean module)

### Root gameplay/formalization modules (`PokemonLean/*.lean`)

- `PokemonLean/ACESpec.lean` — Named ACE SPEC trainer cards.
- `PokemonLean/Abilities.lean` — types: AbilityType, Ability; defs: canPayAbilityCost, payAbilityCost; theorems: payAbilityCost_sound, payAbilityCost_energy_length
- `PokemonLean/AbilitySystem.lean` — types: AbilityName, AbilityTrigger; defs: intimidateAbility, drizzleAbility; theorems: one_ability_or_none, not_both_ability_and_none
- `PokemonLean/AncientTrait.lean` — types: TraitKind, BreakEvolution; defs: attackAllowance, attachmentAllowance; theorems: attackAllowance_pos, attackAllowance_le_two
- `PokemonLean/ArchetypeMatchups.lean` — Matchup result: favorable, even, or unfavorable
- `PokemonLean/Archetypes.lean` — The four fundamental deck archetypes
- `PokemonLean/Basic.lean` — types: EnergyType, StatusCondition; defs: isTrainer, EffectStack; theorems: removeFirstEnergy_length, consumeEnergyCost_sound
- `PokemonLean/BoardState.lean` — types: BoardPokemon, BoardState; defs: defaultBenchLimit, skyFieldBenchLimit; theorems: isSkyField_some_eq, benchLimit_no_stadium
- `PokemonLean/CardPool.lean` — Prize value when this card is KO'd.
- `PokemonLean/Cards.lean` — defs: scatterbug, pineco
- `PokemonLean/Corpus.lean` — defs: cardWellFormed, corpusWellFormed; theorems: corpusWellFormed_trivial
- `PokemonLean/DamageCounters.lean` — Damage counters are placed in 10-point increments in the Pokémon TCG.
- `PokemonLean/Deck.lean` — Count how many cards in `deck` have a given `name`.
- `PokemonLean/DeckBuilding.lean` — High-level deck-building categories.
- `PokemonLean/DeckConstraints.lean` — types: DeckCardKind, DeckEntry; defs: Deck, totalCards; theorems: totalCards_nil, totalCards_singleton
- `PokemonLean/Decks.lean` — types: DeckRules; defs: standardRules, isPokemon; theorems: pokemonCount_nil, trainerCount_nil
- `PokemonLean/EnergyAcceleration.lean` — types: AccelerationState; defs: initialAccelerationState, markAcceleration; theorems: initialAccelerationState_manual_unused, initialAccelerationState_effects_zero
- `PokemonLean/EnergyManagement.lean` — How many units of energy a special energy card provides
- `PokemonLean/Evolution.lean` — A Pokémon can evolve if: 1. The evolution card's stage is the next stage of the current card 2. The evolution card's evolvesFrom matches the current card's name 3. The Pokémon was not played this turn (currentTurn > turnPlayed) 4. The Pokémon was not already evolved this turn (currentTurn > lastEvolvedTurn)
- `PokemonLean/Format.lean` — types: TCGFormat, ReleaseDate; defs: releaseDateCode, releaseDateBeforeOrOn; theorems: releaseDateBeforeOrOn_refl, releaseDateBeforeOrOn_trans
- `PokemonLean/GXAttacks.lean` — types: OncePerGameKind, OncePerGameState; defs: initialOncePerGame, canUseGX; theorems: initial_gx_available, initial_vstar_available
- `PokemonLean/GameTheory.lean` — Result of N-ply lookahead solver.
- `PokemonLean/HandDisruption.lean` — Supporter cards that disrupt the opponent's hand
- `PokemonLean/HandManagement.lean` — types: HandDisruptionEffect; defs: drawPhaseCount, professorsResearchCount; theorems: handSize_eq_length, drawCards_zero
- `PokemonLean/LostZone.lean` — types: GameZone, LostZoneItem; defs: isRecoverableZone, ofPlayerState; theorems: isRecoverableZone_false_iff, isRecoverableZone_true_iff
- `PokemonLean/LostZoneBox.lean` — types: LostZoneBoxDeck, GamePhase; defs: deckTotalCount, isValidLostZoneBoxDeck; theorems: standardLostBoxDeck_valid, standardLostBoxDeck_total
- `PokemonLean/LostZoneCombos.lean` — defs: giratinaLostImpactDamage; theorems: flower_then_colress_lz, colress_then_flower_lz
- `PokemonLean/LostZoneThresholds.lean` — types: LostZoneThreshold, ColressResult; defs: thresholdValue, thresholdMet; theorems: hasThresholdMet_iff, provision_le_mirageGate
- `PokemonLean/Matchup.lean` — The four canonical TCG deck archetypes.
- `PokemonLean/MixedStrategy.lean` — A mixed strategy is just a finite support of pure strategies. We measure its "totalWeight" as the size of the support.
- `PokemonLean/Mulligan.lean` — A card is a basic Pokémon if it is not a trainer (i.e., it has attacks).
- `PokemonLean/Planner.lean` — defs: planOneTurn; theorems: planOneTurn_turnOneActions
- `PokemonLean/PrizeCards.lean` — types: PokemonCategory, CategorizedPokemon; defs: prizesForCategory, initialPrizeCount; theorems: prizesForCategory_pos, basic_gives_one
- `PokemonLean/PrizeDenial.lean` — Prize worth when a Pokemon is knocked out
- `PokemonLean/Prizes.lean` — types: PrizeTier, PrizeCard; defs: prizeTierValue, prizeCardValue; theorems: prizeTierValue_pos, prizeTierValue_le_three
- `PokemonLean/Replay.lean` — A single step in a game trace: the action taken and the resulting state.
- `PokemonLean/RetreatMechanics.lean` — types: RetreatCost, SwitchEffect; defs: RetreatCost.free, RetreatCost.one; theorems: free_retreat_cost_zero, one_retreat_cost
- `PokemonLean/Rotation.lean` — defs: discardRetreatEnergy, isFreeRetreat; theorems: discardRetreatEnergy_nil, discardRetreatEnergy_card
- `PokemonLean/Semantics.lean` — types: Action, StepError; defs: benchLimit, playTrainer; theorems: step_activePlayer_endTurn, step_activePlayer_playPokemonToBench
- `PokemonLean/Solver.lean` — types: TurnSolverResult, TwoPlyResult; defs: maxDamageFromAttacks, attackDamage; theorems: bestAttachmentFrom_optimal, bestAttachmentFrom_mem
- `PokemonLean/SpecialConditions.lean` — Pokémon Tool items that can be attached (one per Pokémon).
- `PokemonLean/Stadium.lean` — Stadium effects that modify the game field for both players.
- `PokemonLean/StatusEffects.lean` — Result of a coin flip: heads = true, tails = false
- `PokemonLean/Switching.lean` — types: SwitchError; defs: removeAt, switchWithBenchIndex; theorems: removeAt, removeAt
- `PokemonLean/Tournament.lean` — types: PlayerProfile, MatchResult; defs: winnerProfile, loserProfile; theorems: scoreDelta_nonneg, totalPoints_nil
- `PokemonLean/TournamentRules.lean` — Official best-of-3 matches have at most three games.
- `PokemonLean/TrainerCards.lean` — types: TrainerKind, TrainerEffect; defs: trainerName, isTrainerCard; theorems: supporterCount_le_length, itemCount_le_length
- `PokemonLean/TrainerSystem.lean` — types: TrainerKind, TrainerName; defs: professorsResearch, bossOrders; theorems: professors_research_is_supporter, boss_orders_is_supporter
- `PokemonLean/TurnStructure.lean` — types: TurnPhase, MainPhaseAction; defs: TurnPhase.toNat, emptyLog; theorems: draw_lt_main, main_lt_attack
- `PokemonLean/TypeChart.lean` — Effectiveness multiplier represented as a scaled natural number (×10). So 0 = immune, 5 = not very effective, 10 = normal, 20 = super effective
- `PokemonLean/VSTAR.lean` — types: RuleBoxKind, VMAXForm; defs: hasRuleBox, prizesForRuleBox; theorems: prizesForRuleBox_pos, prizesForRuleBox_le_three
- `PokemonLean/Win.lean` — Standard number of prize cards per player.

### Core foundational modules (`PokemonLean/Core/*.lean`)

- `PokemonLean/Core/Abilities.lean` — Pokémon types for ability interactions.
- `PokemonLean/Core/AbilityInteraction.lean` — Unique identifier for a Pokémon in play.
- `PokemonLean/Core/AbilityTiming.lean` — When an ability can activate.
- `PokemonLean/Core/AttackCost.lean` — Pokémon energy types.
- `PokemonLean/Core/AttackResolution.lean` — Coin flip.
- `PokemonLean/Core/BattleStyles.lean` — The four battle style categories in Sword & Shield.
- `PokemonLean/Core/BenchMechanics.lean` — Unique identifier for a Pokémon in play.
- `PokemonLean/Core/Card.lean` — Evolution stages in the Pokémon TCG.
- `PokemonLean/Core/CardDatabase.lean` — Pokémon types in the TCG.
- `PokemonLean/Core/CharizardDeck.lean` — [T1] Charmander HP is 70.
- `PokemonLean/Core/CoinFlip.lean` — A coin flip result.
- `PokemonLean/Core/ControlDeck.lean` — A player loses by deck-out when required to draw from an empty deck.
- `PokemonLean/Core/DamageCalc.lean` — Pokémon energy types (TCG).
- `PokemonLean/Core/DeckChecker.lean` — Card category in a deck.
- `PokemonLean/Core/EnergySystem.lean` — Pokémon types relevant to energy.
- `PokemonLean/Core/EnergySystemDeep.lean` — The 11 Pokémon TCG energy types. Note: Colorless is an energy type but has no corresponding basic energy card — any basic energy satisfies a colorless requirement.
- `PokemonLean/Core/Evolution.lean` — Evolution stage in Pokémon TCG.
- `PokemonLean/Core/FormatChecker.lean` — Regulation marks printed on modern Pokémon TCG cards.
- `PokemonLean/Core/GameLoop.lean` — Player identifier.
- `PokemonLean/Core/GameState.lean` — The zones (locations) where cards can exist during a game.
- `PokemonLean/Core/HistoricalFormats.lean` — Major eras of the Pokémon TCG, in chronological order.
- `PokemonLean/Core/Interaction.lean` — Pokémon types in the TCG.
- `PokemonLean/Core/ItemAndTool.lean` — Unique identifier for a Pokémon in play.
- `PokemonLean/Core/LiveFormat.lean` — Standard deck size (same as physical TCG).
- `PokemonLean/Core/LostZoneDeck.lean` — Key Lost Zone Box cards.
- `PokemonLean/Core/MatchupAnalysis.lean` — Competitive deck families used in this module.
- `PokemonLean/Core/Metagame.lean` — Core competitive archetypes in the Pokémon TCG metagame.
- `PokemonLean/Core/MulliganSetup.lean` — Card category for setup purposes.
- `PokemonLean/Core/Paradox.lean` — Paradox classification for Pokémon cards.
- `PokemonLean/Core/Pocket.lean` — Pokémon types in TCG Pocket (subset of physical TCG).
- `PokemonLean/Core/PocketBattle.lean` — Pokémon types.
- `PokemonLean/Core/PrizeMapping.lean` — KO target classes relevant to prize mapping.
- `PokemonLean/Core/PrizeTrade.lean` — The different kinds of Pokémon in the TCG, classified by prize value.
- `PokemonLean/Core/ResourceManagement.lean` — Draw one card if possible; if deck is empty, nothing changes.
- `PokemonLean/Core/Retreat.lean` — Special conditions in the Pokémon TCG.
- `PokemonLean/Core/Rotation.lean` — Regulation marks printed on modern Pokémon TCG cards (Sword & Shield era onward). Pre-mark cards are grouped by era.
- `PokemonLean/Core/RuleBox.lean` — TCG eras for rule box Pokémon.
- `PokemonLean/Core/RulingEdgeCases.lean` — Pokémon types.
- `PokemonLean/Core/ScarletViolet.lean` — Pokémon types in the TCG.
- `PokemonLean/Core/Setup.lean` — Card classification for setup purposes.
- `PokemonLean/Core/SideDeck.lean` — Standard deck size in Pokémon TCG.
- `PokemonLean/Core/Solver.lean` — Pokémon types in the TCG.
- `PokemonLean/Core/SpecialConditions.lean` — Coin flip result.
- `PokemonLean/Core/SpecialMechanics.lean` — The four Ancient Traits from XY era.
- `PokemonLean/Core/StadiumCards.lean` — Stadium cards modeled in this module.
- `PokemonLean/Core/Strategy.lean` — Deck archetypes.
- `PokemonLean/Core/SupporterCards.lean` — Supporter cards represented in this module.
- `PokemonLean/Core/Tournament.lean` — Outcome of a single game.
- `PokemonLean/Core/Trainers.lean` — The six kinds of trainer cards in the TCG (across all eras).
- `PokemonLean/Core/TurnLoop.lean` — Coin flip.
- `PokemonLean/Core/TurnStructure.lean` — types: Coin, Phase; defs: Phase.ord, Phase.next; theorems: draw_ord, main_ord
- `PokemonLean/Core/Types.lean` — The 11 Pokémon types in the TCG. Note: Colorless is NOT a Pokémon type — it is an energy type only.
- `PokemonLean/Core/WinCondition.lean` — Pokémon card classification for prize values.

## Contributing 🤝

Contributions are welcome, especially in rule coverage, theorem strengthening, and proof refactoring.

1. Fork the repository and create a feature branch.
2. Add or update Lean modules with accompanying theorem statements/proofs.
3. Run:
   ```bash
   lake build
   ```
4. Keep proofs readable (named lemmas, small helper results, clear structure).
5. Open a PR summarizing new formalized rules + verified properties.

Suggested contribution directions:

- Expand card/mechanic coverage while preserving existing invariants.
- Strengthen executable semantics with additional preservation/progress-style lemmas.
- Add deeper solver correctness statements tied to richer game state.
- Improve API/doc comments for theorem discoverability.

## License 📄

This repository currently has no populated top-level license text (`paper/LICENSE.md` exists but is empty).  
Until an explicit license is added, assume standard “all rights reserved” defaults.
