# Contributing to PokemonLean

Thanks for helping improve PokemonLean. This project formalizes Pokemon TCG mechanics in Lean 4, so every contribution should prioritize correctness, explicitness, and proof completeness.

## Development setup

1. Install [elan](https://leanprover.github.io/elan-init.sh):
   ```bash
   curl https://leanprover.github.io/elan-init.sh -sSf | sh
   ```
2. Clone the repository and enter it:
   ```bash
   git clone https://github.com/<your-org>/PokemonLean.git
   cd PokemonLean
   ```
3. Build:
   ```bash
   ~/.elan/bin/lake build
   ```
   If `lake` is on your PATH, `lake build` is equivalent.

## Coding style (Lean 4 conventions)

- Follow existing Lean 4 style in this repo: small definitions, explicit types, and descriptive names.
- Keep theorem/lemma names in `snake_case` (for example, `damage_nonneg`, `removeFirst_length`).
- Prefer structured proofs (`by`, `intro`, `cases`, `simp`, `rw`) and keep proof steps readable.
- Avoid wildcard imports; add explicit `import` lines as needed.
- Keep code in the appropriate namespace/module (for example, `namespace PokemonLean.Cards`).
- Respect project options in `lakefile.lean` (notably `autoImplicit := false`), so write binders explicitly.

## Pull request process

1. Create a focused branch from `main`.
2. Make minimal, scoped commits with clear messages.
3. Run all required checks locally (see Testing below).
4. Open a PR that includes:
   - A short summary of what changed
   - Why the change is needed
   - Any proof or model assumptions you introduced
5. Respond to review feedback and keep the branch up to date.

## Testing and proof completeness requirements

Before opening a PR, all of the following must hold:

1. Build succeeds:
   ```bash
   ~/.elan/bin/lake build
   ```
2. No placeholder or untrusted proof shortcuts are introduced:
   ```bash
   rg -n "\b(sorry|admit|axiom)\b" PokemonLean Core Main.lean
   ```
   This command should return no matches for committed code.

## Adding new card formalizations

Card definitions live in `PokemonLean/Cards.lean` under `namespace PokemonLean.Cards`.

### Preferred path (generated data)

Use the provided script to regenerate card definitions from the API:

```bash
python3 scripts/fetch_cards.py --set sv1 --limit 20 --output PokemonLean/Cards.lean
```

### Manual path

If you add cards by hand:

1. Add `def <card_name> : Card := ...` entries in `PokemonLean/Cards.lean`.
2. Add new cards to `def corpus : List Card`.
3. Update proofs or checks that enumerate the corpus (for example `PokemonLean/Corpus.lean` and `corpusWellFormed_trivial`).
4. Re-run `~/.elan/bin/lake build`.

## Adding new theorems

1. Put the theorem in the module that owns the related definitions.
2. State assumptions explicitly and use descriptive theorem names.
3. Prove the statement fully (no `sorry`, `admit`, or `axiom`).
4. If you add a new module file, import it from `PokemonLean.lean` so it is part of the library build.
5. Rebuild with `~/.elan/bin/lake build` and include relevant notes in your PR description.
