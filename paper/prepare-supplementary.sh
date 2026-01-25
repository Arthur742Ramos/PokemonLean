#!/bin/bash
# Prepare anonymized supplementary material for ITP 2026 submission

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_ROOT/supplementary"

echo "Creating anonymized supplementary material..."

# Clean and create output directory
rm -rf "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR"

# Copy Lean source files (anonymized)
mkdir -p "$OUTPUT_DIR/src"
cp "$PROJECT_ROOT/PokemonLean.lean" "$OUTPUT_DIR/src/"
cp -r "$PROJECT_ROOT/PokemonLean" "$OUTPUT_DIR/src/"

# Copy build files
cp "$PROJECT_ROOT/lakefile.toml" "$OUTPUT_DIR/" 2>/dev/null || cp "$PROJECT_ROOT/lakefile.lean" "$OUTPUT_DIR/" 2>/dev/null || true
cp "$PROJECT_ROOT/lean-toolchain" "$OUTPUT_DIR/" 2>/dev/null || true
cp "$PROJECT_ROOT/lake-manifest.json" "$OUTPUT_DIR/" 2>/dev/null || true

# Create anonymized README
cat > "$OUTPUT_DIR/README.md" << 'EOF'
# Supplementary Material: Formalizing Pokémon TCG in Lean 4

## Contents

- `src/` - Lean 4 source files
  - `PokemonLean/Basic.lean` - Core types and game logic
  - `PokemonLean/Semantics.lean` - Small-step semantics and legality
  - `PokemonLean/Solver.lean` - Certified damage solver
  - `PokemonLean/GameTheory.lean` - Extended strategy features
  - `PokemonLean/Cards.lean` - Sample card corpus
- `lakefile.toml` - Build configuration
- `lean-toolchain` - Lean version specification

## Building

Requires Lean 4.26.0 or later.

```bash
lake build
```

## Verifying Proofs

All theorems compile without `sorry` axioms:

```bash
lake build 2>&1 | grep -E "(error|sorry)" || echo "All proofs verified!"
```

## Key Theorems

| Theorem | File | Description |
|---------|------|-------------|
| `bestAttack_sound` | Solver.lean | Solver returns legal attack |
| `bestAttack_optimal` | Solver.lean | Solver returns damage-maximal attack |
| `reachable_card_conservation` | Semantics.lean | Card count invariant |
| `reachable_valid_initial` | Semantics.lean | Validity preserved |
| `no_turn_one_win` | Basic.lean | No T1 win possible |
| `step_total_for_legal` | Semantics.lean | Legal actions always succeed |
EOF

# Create zip archive
cd "$PROJECT_ROOT"
zip -r supplementary.zip supplementary -x "*.DS_Store"

echo "Created: $PROJECT_ROOT/supplementary.zip"
echo "Contents:"
unzip -l "$PROJECT_ROOT/supplementary.zip"
