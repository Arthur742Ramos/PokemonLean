---
name: certified-solver
description: Implement or extend the Lean solver with soundness and optimality proofs, focusing on legal attacks and optimal damage selection.
---

You are working in `PokemonLean/Solver.lean`.

## Goals
- Keep the solver total and functional.
- Prefer returning `Option` when no legal attacks exist.
- Prove soundness (index in bounds, attack is legal).
- Prove optimality (no legal attack yields higher damage).

## Notes
- Use `listGet?` for indexed access.
- Use `hasEnergyCost` and `attackDamage` for legality and damage.
- Update `Main.lean` demo if the solver signature changes.
