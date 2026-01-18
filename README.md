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
Proven theorems:
- `damage_nonneg`: Damage is always ≥ 0
- `weakness_bounded`: Weakness multiplies damage correctly
- `resistance_reduces`: Resistance reduces damage (bounded by Nat.sub)
- `endTurn_preserves_cards`: Turn switching preserves card count
- `removeFirst_length`: List removal decreases length by 1
- `foldl_add_shift`: Foldl addition commutes with initialization
- `bench_card_count`: Bench card count equals list length
- `playCard_preserves_player_cards`: **PROVEN** - Card conservation invariant

Additional proven theorems:
- `no_turn_one_win`: No T1 win from standard starting state
- `bestAttackIndex_sound`: Solver returns valid indices
- `maxDamage_complete`: Solver finds true maximum

### Phase 4: Scaling, Tooling & Integration ✅
- **Verified Solver**: `solve` function finds optimal attack with damage prediction
- **CLI Application**: Interactive demo with battle simulations
- **Python Integration**: Card data pipeline from official API

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

- **M1: Energy Cost Rules** — formalize energy requirements, validate costs in `applyAction`, prove energy conservation.
- **Top 3 Next Features (Highest ROI)**:
  1. **Action Language + Small-step Semantics** — define `Action` variants (PlayPokemonToBench, AttachEnergy, Attack i, Retreat, EndTurn, optional DrawCard) plus `step : GameState → Action → Except Error GameState` and `Legal : GameState → Action → Prop/Decidable`. Target proofs: determinism of execution, progress/preservation, and no-crash for legal actions.
  2. **Reachability + Global Invariants (Meta-Safety)** — define `Reachable`, then prove global invariants for all reachable states: state validity preserved, zone conservation, boundedness (bench ≤ 5, prizes ∈ [0,6], HP bounds), and turn discipline.
  3. **Certified Strategy Procedure (Optimal Solver)** — formalize a per-turn optimization objective and implement `bestAttack` with soundness + optimality theorems (legal index in bounds and damage maximal among legal attacks), with optional stability/monotonicity lemmas.
- **M2: Prize & Win Invariants** — strengthen prize-taking lemmas, prove win-condition soundness across multi-turn play.
- **M3: Rule Coverage Expansion** — add trainer/ability/evolution rules with invariants for legal board states.
- **M4: Solver Generalization** — extend solver proofs across a larger card corpus and full effect stacking semantics.
- **M5: Formal Proof Artifact** — compile a reproducible proof checklist and publishable theorem index.
- **M6: Submission Package** — finalize paper draft, artifact packaging, and CI verification for ITP/FormaliSE.
