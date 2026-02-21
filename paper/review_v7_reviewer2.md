# IEEE Transactions on Games — Reviewer Report

**Submission #753 (v7):** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Reviewer:** Reviewer 2 (Formal Methods Specialist)  
**Date:** 2026-02-20

---

## Summary

The paper presents a 30K-line Lean 4 artifact that formalizes metagame analysis of the competitive Pokémon TCG, encoding a 14×14 matchup matrix from Trainer Hill tournament data and proving game-theoretic properties including a "popularity paradox" (the most-played deck is suboptimal), a machine-checked Nash equilibrium, replicator dynamics classifications, and robustness bounds. Version 7 adds `SkillSensitivity.lean` and `StepSizeInvariance.lean` modules addressing prior reviewer concerns about confounding and discretization artifacts.

---

## Scores

| Criterion        | Score | Comment |
|-------------------|-------|---------|
| **Novelty**       | 4/5   | First formally verified metagame analysis at this scale; the methodology template is genuinely new |
| **Technical Soundness** | 3/5 | Sound within stated trust boundary, but that boundary is wider than acknowledged in places |
| **Significance**  | 3/5   | Methodological contribution is clear; domain impact is limited by temporal locality |
| **Clarity**       | 4/5   | Well-written; trust boundary discussion is the best I've seen in a v7 revision cycle |
| **Reproducibility** | 4/5 | `lake build` workflow is strong; sensitivity analysis in external Python weakens end-to-end story |

---

## Detailed Assessment

### 1. Trust Boundary: `native_decide` vs Kernel-Checked `decide`

The authors are commendably transparent about the `native_decide` dependency: 207 call sites (I count more than the paper's stated 244 — possibly the paper counts unique theorem names while grep counts invocations, including the `optimize_proof` macro alias). The discussion of why `decide` fails (opaque `Fin.foldl` in the Lean 4 kernel reducer) is technically accurate and honest.

However, I have two concerns:

**(a) Concentration risk is understated.** The paper notes that a hypothetical code-generation bug could "simultaneously invalidate all 244 `native_decide` proofs," but then waves this away with "no such bugs have been reported in practice." This is true as of writing, but the argument proves too much — one could use it to justify `native_decide` for anything. The real issue is that **every headline result** (Nash equilibrium, replicator dynamics, skill sensitivity, step-size invariance, type-advantage bridge) passes through this single trust gate. There is no diversity of proof technique for the core claims. A more honest framing would be: "the artifact is verified modulo the Lean 4 compiler's native code generation for rational arithmetic on `Fin`-indexed structures."

**(b) The `optimize_proof` macro.** Aliasing `native_decide` as `optimize_proof` in `EvolutionaryDynamics.lean` and `SharePerturbation.lean` is a readability antipattern. A reader grepping for `native_decide` to audit the trust boundary will miss these. The macro name misleadingly suggests performance optimization rather than a trust-boundary crossing. I note a second alias `optimize_proof_native` in `SharePerturbation.lean` — this proliferation of synonyms is poor proof engineering hygiene.

### 2. Proof Engineering Quality and Patterns

**Strengths:**
- The `NashEquilibrium.lean` module is well-structured: clean separation of game definition (`FiniteGame`), strategy validity (`IsMixedStrategy`), equilibrium definition (`NashEquilibrium`), and verification. The bimatrix formulation with independent row/column best-response checks is mathematically correct and cleanly implemented.
- `FullReplicator.lean` provides a complete 14-deck classification (5 growers, 9 shrinkers) with individual theorems for each deck — excellent for traceability.
- The `RealMetagame.lean` data layer is admirably explicit: every matchup value is a named pattern match, making data-entry errors immediately visible in diffs.
- The `Decidable` instance scaffolding (`decidableForallFin`, `decidableExistsFin`) is correctly constructed via induction on `n`.

**Weaknesses:**
- **Redundant proof structure.** `StepSizeInvariance.lean` contains 145 lines proving trivially that `sign(x_i * dt * (f_i - f̄)) = sign(f_i - f̄)` for three concrete values of `dt`. The algebraic insight is stated in the docstring ("sign depends only on f_i − f_avg for dt > 0") but not proven generically. A single parametric theorem `∀ dt > 0, ...` would be stronger and shorter. The current approach proves the instance three times via brute force rather than proving the lemma once.
- **Data duplication.** The 14×14 matchup matrix appears in at least three places: `RealMetagame.lean` (as `matchupWR` pattern match), `NashEquilibrium.lean` (as `realMatchupData` array), and `SymmetricNash.lean` (symmetrized). There is no machine-checked theorem that `realMatchupData` in `NashEquilibrium.lean` equals the `matchupWR` function in `RealMetagame.lean`, creating a silent consistency risk. If a data-entry error appears in one but not the other, theorems over the two representations could diverge without detection.
- **4-deck subcycle artifacts.** `EvolutionaryDynamics.lean` contains extensive 4-deck and 5-deck subcycle analysis (Sections 11–19, ~400 lines) that appears to be vestigial from earlier versions. With `FullReplicator.lean` now providing full 14-deck results, the subcycle analysis is strictly dominated. The paper doesn't cite these subcycle results — they should be clearly marked as superseded or removed.

### 3. Artifact Structure (30K Lines, 80 Files)

The module organization is reasonable at the top level (Core, GameTheory, RealMetagame, etc.), but the artifact has breadth-without-depth issues:

- **Infrastructure bloat.** Files like `AncientTrait.lean` (489 lines), `VSTAR.lean` (403 lines), `GXAttacks.lean` (323 lines), and `LostZone.lean` (936 lines) formalize game mechanics not referenced in the paper's analysis. While they contribute to the "rules formalization" framing, they account for ~40% of total lines and create a misleading impression of the artifact's depth. The paper's claims rest on perhaps 6–8 core files totaling ~3,500 lines.
- **Import structure.** The dependency chain is linear and clean: `Core.Types` → `RealMetagame` → `NashEquilibrium` → `EvolutionaryDynamics` → `FullReplicator` → `SkillSensitivity` / `StepSizeInvariance`. This is good engineering.

### 4. Verification Claims: Scope

The paper carefully states "verified modulo native code generation" in the abstract and Section 8.3, which is appropriate. However:

- **The sensitivity analysis is unverified.** Table 1 (10,000-iteration Nash sensitivity) is produced by an external Python script, not by Lean. The paper acknowledges this but Table 1 is presented with the same visual weight as the verified results. A clearer visual separation (e.g., a distinct marking for "externally computed, not formally verified") would prevent readers from conflating the two trust levels.
- **Wilson intervals are not verified.** The confidence interval discussion in Section 5 is purely prose mathematics. Given that the whole point of the paper is formal verification, the gap is notable.
- **"No sorry, no admit, no custom axioms" is accurately stated** — my grep confirms zero instances of `sorry` or `admit` in proof positions, and no `axiom` declarations.

### 5. New Modules: `SkillSensitivity.lean` and `StepSizeInvariance.lean`

**SkillSensitivity.lean (91 lines):** This module directly addresses a prior reviewer concern about player-skill confounding. The approach is clean: model a uniform skill-bias correction `b` added to all Dragapult matchups, then find the threshold `b` where Dragapult reaches 50% (b=3.4pp) and where it matches Grimmsnarl (b=6.1pp). The tight upper/lower bounds (e.g., 33/1000 < threshold ≤ 34/1000) are a nice touch that demonstrates the precision advantage of formal methods.

**Limitation:** The uniform-bias model is restrictive. In practice, skill confounding would differentially affect matchups (a weak pilot loses more in complex matchups). A sensitivity analysis with per-matchup bias vectors would be more convincing, though admittedly the combinatorial explosion makes full verification harder.

**StepSizeInvariance.lean (145 lines):** Addresses the step-size sensitivity concern. As noted above, this is proven by brute-force enumeration at three `dt` values rather than by the obvious algebraic argument. The algebraic fact — that `replicatorStep` preserves sign of `(f_i - f̄)` for all `dt > 0` — follows from a one-line calculation, and proving it generically would be a stronger result. The current approach verifies three instances but doesn't actually prove step-size invariance; it proves step-size invariance *at three specific step sizes*.

### 6. Minor Issues

- The identifier `GrimssnarlFroslass` (double-s, single-m) is acknowledged in a footnote but persists across the entire codebase. This is a minor professionalism issue for a journal publication.
- `Planner.lean` is 16 lines and appears to be a stub.
- The `Corpus.lean` file is 28 lines. Several files under 100 lines could be consolidated.

---

## Overall Recommendation

### **Weak Accept**

The paper makes a genuine methodological contribution: it demonstrates, for the first time, that proof-carrying analytics is feasible for real competitive game ecosystems at the scale of a full tournament metagame. The formal artifact is real, builds, and proves what it claims (modulo `native_decide`). The v7 revisions meaningfully address prior concerns about skill confounding and step-size sensitivity.

The weaknesses are: (1) the `native_decide` concentration risk with no defense-in-depth, (2) data duplication across modules without cross-consistency theorems, and (3) the step-size invariance proof that proves instances rather than the general algebraic fact. None of these is fatal, but (2) in particular undermines the paper's own argument that formal verification catches data-entry errors that spreadsheets miss.

---

## Must-Do Revisions

**M1. Add a cross-consistency theorem linking the three representations of the matchup matrix.** `RealMetagame.matchupWR`, `NashEquilibrium.realMatchupData`, and the `SymmetricNash.symMatchupData` derivation must be formally connected. A theorem of the form `∀ i j, realMatchupData[i]![j]! = (matchupWR (Deck.ofFin i) (Deck.ofFin j) : Rat)` is straightforward and closes a real gap. Without this, the paper's data-integrity argument has an ironic hole.

**M2. Eliminate or unify the `optimize_proof` / `optimize_proof_native` macro aliases for `native_decide`.** These obscure the trust boundary. Either use `native_decide` directly everywhere (preferred), or if a macro is desired, name it `trust_native_decide` or similar to make the trust implication explicit. This is a proof-engineering hygiene issue that directly impacts the paper's reproducibility and auditability claims.

**M3. Visually distinguish verified vs. unverified results in the paper.** Table 1 (Python sensitivity analysis) and the Wilson interval discussion should be clearly marked with a symbol (e.g., †) indicating they are not part of the verified artifact. Currently, a reader must carefully parse prose caveats to determine which claims are machine-checked.

---

## Questions for Authors

**Q1.** Have you attempted to prove step-size invariance generically (i.e., `∀ dt > 0, sign(replicatorStep ... dt i - x_i) = sign(fitness ... i - avgFitness ...)`)? If so, what blocked the proof? If not, why enumerate instances when the algebraic argument is trivial?

**Q2.** The matchup matrix in `NashEquilibrium.realMatchupData` is a raw `Array (Array Rat)` accessed via `[i]!` (panicking indexing). Have you considered using `Fin`-indexed `Vector` types instead, which would provide compile-time bounds checking and eliminate the implicit trust in correct array dimensions?

**Q3.** Your 4-deck and 5-deck subcycle analyses in `EvolutionaryDynamics.lean` (Sections 11–19) are not referenced in the paper and are strictly superseded by `FullReplicator.lean`. Are these retained for pedagogical reasons in the artifact, or are they vestigial? If the former, please document this clearly; if the latter, please remove them to reduce artifact maintenance burden and avoid confusion about which results are canonical.

---

*Reviewer 2 — Formal Methods*
