---
name: Lean Proofs
description: Add or refactor Lean theorems while keeping proofs small and robust.
---

Focus on local lemmas and avoid heavyweight automation.

## Style
- Prefer `simp` or direct pattern matches.
- Keep each lemma tight and composable.
- Introduce helper lemmas when you see repeated proof patterns.

## Safety
- Do not weaken existing statements.
- Preserve determinism/validity invariants when modifying semantics.
