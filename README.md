# PokemonLean

A formal verification project for Pokémon TCG game mechanics in Lean 4.

## Overview

This project bridges formal verification and game theory by building a verified model of Pokémon TCG mechanics to prove "Meta-Safety" invariants.

## Project Structure

- `PokemonLean/Basic.lean` - Core types, game logic, and theorems
- `PokemonLean/Cards.lean` - Auto-generated card definitions from TCG API
- `PokemonLean/Solver.lean` - Verified damage optimization solver
- `Main.lean` - CLI demo application
- `scripts/fetch_cards.py` - Python scraper for Pokémon TCG API

## Implemented Features

### Phase 1: Type-Safe Foundation ✅
- **EnergyType**: Fire, Water, Grass, Lightning, Psychic, Fighting, Dark, Metal, Fairy, Dragon, Colorless
- **Card**: HP, EnergyType, Attacks, Weakness, Resistance
- **GameState**: Complete board state with players, decks, hands, bench, active, discard, prizes
- **Data Pipeline**: Python scraper fetches real cards from Pokémon TCG API

### Phase 2: Operational Semantics ✅
- **applyAction**: Transition function for game state changes
- **calculateDamage**: Base → Weakness (×2) → Resistance (-30) pipeline
- Verified outputs: Pikachu→Charmander = 20 damage, Squirtle→Charmander = 40 damage

### Phase 3: Formal Verification ✅
Proof checklist:
| Theorem | Location | Status |
| --- | --- | --- |
| `damage_nonneg` | `PokemonLean/Basic.lean` | ✅ |
| `weakness_bounded` | `PokemonLean/Basic.lean` | ✅ |
| `resistance_reduces` | `PokemonLean/Basic.lean` | ✅ |
| `endTurn_preserves_cards` | `PokemonLean/Basic.lean` | ✅ |
| `removeFirst_length` | `PokemonLean/Basic.lean` | ✅ |
| `foldl_add_shift` | `PokemonLean/Basic.lean` | ✅ |
| `bench_card_count` | `PokemonLean/Basic.lean` | ✅ |
| `playCard_preserves_player_cards` | `PokemonLean/Basic.lean` | ✅ |
| `turnActions_attachEnergyCount_le_one` | `PokemonLean/Semantics.lean` | ✅ |
| `turnActions_supporterCount_le_one` | `PokemonLean/Semantics.lean` | ✅ |
| `turnActions_ends_turn` | `PokemonLean/Semantics.lean` | ✅ |
| `stepMany_activePlayer_turn` | `PokemonLean/Semantics.lean` | ✅ |
| `legal_playSupporterDraw_iff` | `PokemonLean/Semantics.lean` | ✅ |
| `legal_playItemHeal_iff` | `PokemonLean/Semantics.lean` | ✅ |
| `legal_evolveActive_iff` | `PokemonLean/Semantics.lean` | ✅ |
| `legal_evolveActive_iff` (HP monotonic) | `PokemonLean/Semantics.lean` | ✅ |
| `legal_useAbilityHeal_iff` | `PokemonLean/Semantics.lean` | ✅ |
| `legal_useAbilityDraw_iff` | `PokemonLean/Semantics.lean` | ✅ |
| `step_prizes_nonincreasing` | `PokemonLean/Semantics.lean` | ✅ |
| `step_preserves_hasWon` | `PokemonLean/Semantics.lean` | ✅ |
| `stepMany_preserves_hasWon` | `PokemonLean/Semantics.lean` | ✅ |
| `runEffectStack_empty` | `PokemonLean/Semantics.lean` | ✅ |
| `runEffectStack_terminates` | `PokemonLean/Semantics.lean` | ✅ |
| `runEffectStack_append` | `PokemonLean/Semantics.lean` | ✅ |
| `runEffectStack_deterministic` | `PokemonLean/Semantics.lean` | ✅ |
| `globalZonesDisjoint_trivial` | `PokemonLean/Semantics.lean` | ✅ |
| `reachable_card_conservation` | `PokemonLean/Semantics.lean` | ✅ |
| `reachable_valid_initial` | `PokemonLean/Semantics.lean` | ✅ |
| `reachable_zones_disjoint` | `PokemonLean/Semantics.lean` | ✅ |
| `nextFlip`/`GameRand` (randomness model) | `PokemonLean/Semantics.lean` | ✅ |
| `legal_playItem_iff` (trainer typing) | `PokemonLean/Semantics.lean` | ✅ |
| `legal_playSupporter_iff` (trainer typing) | `PokemonLean/Semantics.lean` | ✅ |
| `legal_playTool_iff` (trainer typing) | `PokemonLean/Semantics.lean` | ✅ |
| `step_error_iff_not_legal` | `PokemonLean/Semantics.lean` | ✅ |
| `step_total_for_legal` | `PokemonLean/Semantics.lean` | ✅ |
| `no_turn_one_win` | `PokemonLean/Basic.lean` | ✅ |
| `bestAttack_sound` | `PokemonLean/Solver.lean` | ✅ |
| `bestAttack_optimal` | `PokemonLean/Solver.lean` | ✅ |
| `solve_sound` | `PokemonLean/Solver.lean` | ✅ |
| `solve_optimal` | `PokemonLean/Solver.lean` | ✅ |
| `maxDamage_complete` | `PokemonLean/Solver.lean` | ✅ |
| `hasEnergyCost_iff_consume` | `PokemonLean/Basic.lean` | ✅ |

Proven theorems:
- `damage_nonneg`: Damage is always ≥ 0
- `weakness_bounded`: Weakness multiplies damage correctly
- `resistance_reduces`: Resistance reduces damage (bounded by Nat.sub)
- `endTurn_preserves_cards`: Turn switching preserves card count
- `removeFirst_length`: List removal decreases length by 1
- `foldl_add_shift`: Foldl addition commutes with initialization
- `bench_card_count`: Bench card count equals list length
- `playCard_preserves_player_cards`: **PROVEN** - Card conservation invariant
- `turnActions_attachEnergyCount_le_one`: At most one energy attachment per turn
- `turnActions_supporterCount_le_one`: At most one supporter per turn
- `turnActions_ends_turn`: Every turn ends with attack or endTurn
- `stepMany_activePlayer_turn`: Turn action sequences flip the active player
- `legal_playSupporterDraw_iff`: Supporter draw is legal iff card in hand and enough cards in deck
- `legal_playItemHeal_iff`: Item heal is legal iff card in hand and active Pokemon exists
- `legal_evolveActive_iff`: Evolution is legal iff active exists and evolution card in hand
- `legal_useAbilityHeal_iff`: Ability heal is legal iff active exists
- `legal_useAbilityDraw_iff`: Ability draw is legal iff enough cards in deck
- `step_prizes_nonincreasing`: Prize counts never increase across steps
- `step_preserves_hasWon`: Win status is preserved by steps
- `stepMany_preserves_hasWon`: Win status is preserved across turn sequences
- `runEffectStack_append`: Effect resolution is compositional over stack concatenation
- `runEffectStack_deterministic`: Effect resolution is deterministic
- `reachable_card_conservation`: Card conservation holds for all reachable states
- `reachable_valid_initial`: Validity invariants hold for all reachable states
- `reachable_zones_disjoint`: Zone disjointness holds for all reachable states
- `step_error_iff_not_legal`: Steps error iff action is illegal
- `step_total_for_legal`: Legal actions always step successfully

Additional proven theorems:
- `no_turn_one_win`: No T1 win from standard starting state
- `bestAttack_sound`: Solver returns valid indices
- `bestAttack_optimal`: Solver returns damage-maximal legal attack
- `solve_sound`: Solver result is legal and matches computed damage
- `solve_optimal`: Solver maximizes damage among legal attacks
- `maxDamage_complete`: Solver finds true maximum
- `hasEnergyCost_iff_consume`: Energy cost is satisfiable iff it can be consumed from energy list

### Phase 4: Scaling, Tooling & Integration ✅
- **Verified Solver**: `solve` function finds optimal attack with damage prediction
- **CLI Application**: Interactive demo with battle simulations
- **Python Integration**: Card data pipeline from official API
- **Corpus Check**: Solver runs across the sample card corpus (`PokemonLean.Cards.corpus`)

## Building & Running

```bash
# Build the project
lake build

# Run the CLI demo
.lake/build/bin/pokemonlean

# Fetch cards from TCG API
python3 scripts/fetch_cards.py --set sv1 --limit 20 --output PokemonLean/Cards.lean
```

## Example Output

```
╔══════════════════════════════════════════════════════╗
║   PokemonLean - Verified TCG Damage Calculator       ║
╚══════════════════════════════════════════════════════╝

Battle Simulation: Squirtle (💧) vs Charmander (🔥)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Charmander: 70 HP, weak to Water
Squirtle: 60 HP, Water Gun (20 base)

Solver Result (Formally Verified):
  Best Attack Index: 0
  Expected Damage: 40 (2x weakness!)
  Is Knockout: false

✓ All calculations verified by Lean 4 type system
```

## Roadmap to Publication Readiness

- **M1: Energy Cost Rules** ✅ — formalize energy requirements, validate costs in `applyAction`, prove energy conservation.
- **M2: Trainer Rule Coverage** ✅ — add Items/Supporters/Tools with per-turn limits (items unlimited, supporter once), plus draw/heal trainer effects.
- **Top 3 Next Features (Highest ROI)**:
  1. **Action Language + Small-step Semantics** — define `Action` variants (PlayPokemonToBench, AttachEnergy, Attack i, Retreat, EndTurn, optional DrawCard) plus `step : GameState → Action → Except Error GameState` and `Legal : GameState → Action → Prop/Decidable`. Target proofs: determinism of execution, progress/preservation, and no-crash for legal actions.
  2. **Reachability + Global Invariants (Meta-Safety)** — define `Reachable`, then prove global invariants for all reachable states: state validity preserved, zone conservation, boundedness (bench ≤ 5, prizes ∈ [0,6], HP bounds), and turn discipline.
  3. **Certified Strategy Procedure (Optimal Solver)** — formalize a per-turn optimization objective and implement `bestAttack` with soundness + optimality theorems (legal index in bounds and damage maximal among legal attacks), with optional stability/monotonicity lemmas.
- **M2: Prize & Win Invariants** ✅ — prize counts are nonincreasing and `hasWon` is preserved by `step`/`stepMany`.
- **M3: Rule Coverage Expansion** ✅ — trainer/ability/evolution actions are implemented with legality and preservation proofs.
- **M4: Solver Generalization** ✅ — effect stacking semantics included in damage bounds; solver remains general across card lists.
- **M5: Formal Proof Artifact** — compile a reproducible proof checklist + artifact guide, ensure theorem index is complete, add CI proof badge.
- **M6: Submission Package** — finalize paper draft, artifact packaging, and CI verification for ITP/FormaliSE.

### M5 Execution Plan
1. **Proof Checklist** — enumerate all headline theorems with file/line references and status.
2. **Artifact Guide** — reproducible steps: build, run demos, regenerate cards, and check theorem index.
3. **CI Alignment** — verify `lake build` and add status badge to README.
