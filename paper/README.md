# ITP 2026 Submission: PokemonLean

## Paper: "Formalizing Pokémon TCG in Lean 4: Semantics, Invariants, and a Certified Solver"

**Type:** Short Paper (6 pages max, excluding references)

### Files

- `paper.tex` - Main LaTeX source
- `references.bib` - Bibliography
- `lipics-v2021.cls` - LIPIcs document class (v2021.1.3)
- `build.sh` - Build script

### Building

```bash
./build.sh
```

Or manually:
```bash
pdflatex paper.tex
bibtex paper
pdflatex paper.tex
pdflatex paper.tex
```

### ITP 2026 Submission Requirements

| Requirement | Status |
|-------------|--------|
| LIPIcs v2021.1.3 format | ✅ |
| Anonymous mode enabled | ✅ |
| "Short paper" subtitle | ✅ |
| Max 6 pages (excl. refs) | ✅ |
| No appendix | ✅ |
| Supplementary material | See `../` |

### Important Dates

- **Abstract deadline:** February 12, 2026 (AOE)
- **Paper submission deadline:** February 19, 2026 (AOE)
- **Author notification:** April 26, 2026
- **Camera-ready:** May 24, 2026
- **Conference:** July 26-29, 2026 (Lisbon, Portugal)

### Submission URL

https://submissions.floc26.org/itp/
