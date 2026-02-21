# Revision v4 — 2026-02-20

Prose-only edits addressing remaining reviewer feedback (all three: Weak Accept).

## Changes

1. **Edit 1 (§III-B, line ~242): Soften bridge language.**
   Replaced "not a modeling artifact" claim with explicit "correlational consistency check" framing, clarifying this is not a causal derivation.

2. **Edit 2 (§III-B, line ~287): Soften bridge chain claim.**
   Replaced "formal chain the reviewers asked for" with precise language: correlational consistency given domain-expert type assignments, 83% directional agreement.

3. **Edit 3 (§III-B, after Edit 2): Add null model baseline.**
   New sentence: random assignments → ~50% by symmetry; observed 83% (15/18) gives p < 0.001 under binomial null.

4. **Edit 4 (§I, line ~113): Reframe practical value.**
   Added sentence after "reproducibility infrastructure" paragraph clarifying the contribution is methodological, not competitive-tactical.

5. **Edit 5 (§IX-C, line ~866): Expand native_decide trust boundary.**
   Replaced single-paragraph subsection with detailed discussion: 244/2500 theorems use native_decide, structural preclusion of `decide` (Fin.foldl opacity + failed sumFin reformulation), explicit trust implications (no kernel-checked proof term, correlated failure risk, no defense in depth), and mitigation notes.

6. **Edit 6 (§VI-B, line ~638): Trim behavioral-economics section.**
   Condensed two-sentence bounded-rationality paragraph into one sentence with consolidated citations.

7. **Edit 7 (§IX-E, before "Human Review"): Add baseline comparison table.**
   New subsection "Cost-Benefit: Formal Verification vs. Alternatives" with Table comparing spreadsheet (~50 cells), Python+scipy (~100 LoC), and Lean 4 (~30K LoC) approaches on LoC, runtime, and guarantee level.

## Verification

- Braces: 565/565 balanced ✓
- Environments: 40/40 balanced ✓
- No code changes required
