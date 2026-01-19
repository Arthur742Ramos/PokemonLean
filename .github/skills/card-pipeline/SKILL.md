---
name: Card Pipeline
description: Update the Python card fetcher and Lean card definitions.
---

Work in `scripts/fetch_cards.py` and `PokemonLean/Cards.lean`.

## Goals
- Preserve the current schema for `Card` and `Attack`.
- Ensure energy costs and effects are represented.
- Keep generated Lean output deterministic (stable ordering, consistent formatting).

## Checks
- If you change the schema, update `PokemonLean/Basic.lean` accordingly.
