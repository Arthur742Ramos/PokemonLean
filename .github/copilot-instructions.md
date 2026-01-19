# Repository Instructions

You are working on PokemonLean, a Lean 4 project that formalizes Pokemon TCG mechanics.

## Core files
- `PokemonLean/Basic.lean`: core game types and mechanics.
- `PokemonLean/Semantics.lean`: small-step semantics (`Action`, `step`, `Legal`).
- `PokemonLean/Solver.lean`: certified damage solver and proofs.
- `Main.lean`: CLI demo wiring for the solver.
- `scripts/fetch_cards.py`: card ingestion pipeline; updates `PokemonLean/Cards.lean`.

## Conventions
- Prefer total, pure functions; avoid `partial` unless unavoidable.
- Reuse existing helpers (e.g. `listGet?`, `hasEnergyCost`, `calculateDamage`).
- Keep proofs small and local; avoid heavyweight tactics unless necessary.
- Match the current style: `simp`/`simp [..]` proofs and explicit pattern matches.
- Update examples in `Main.lean` when function signatures change.
- Work autonomously end-to-end without stopping to announce next steps; only summarize when results are complete.

## Verification
- Build with `lake build`.
- Ensure solver soundness/optimality theorems remain `simp`-friendly.
