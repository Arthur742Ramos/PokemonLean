# Review of Submission #753 (v8)

**"From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"**

**Reviewer 2 — Formal Methods Specialist**
**Date:** 2026-02-20

---

## Summary

The paper presents a ~30,000-line Lean 4 artifact that formalizes metagame analysis for the Pokémon TCG, encoding a 14×14 matchup matrix from Trainer Hill tournament data and proving a "popularity paradox" (the most-played deck is suboptimal), Nash equilibrium certification, and replicator dynamics predictions. V8 replaces 63 instances of a project-local `optimize_proof` macro with direct `native_decide` calls, adds `MatrixConsistency.lean` to cross-check matrix representations, and adds `DragapultDominated.lean` proving strict suboptimality of Dragapult against the Nash column mix.

---

## Scores

| Criterion        | Score | Comment |
|------------------|:-----:|---------|
| **Novelty**      | 4/5   | First proof-carrying metagame analytics pipeline for a real TCG. The methodological template is genuinely new and portable. |
| **Technical Soundness** | 3/5 | Core game-theoretic results are well-structured but the entire computational core rests on `native_decide` with no defense in depth. The trust boundary is honestly disclosed but remains a real limitation. |
| **Significance** | 3/5   | Strong methodological contribution; domain-specific results are illustrative rather than broadly impactful. The gap between "what formal verification adds" and "what a Python script gives" narrows once `native_decide` is the sole proof engine. |
| **Clarity**      | 4/5   | Well-written; the trust boundary discussion (Sec. 8.3) is unusually candid. Some structural redundancy between 4-deck subcycle and full 14-deck results in `EvolutionaryDynamics.lean`. |
| **Reproducibility** | 5/5 | Exemplary. `lake build` with no `sorry`/`admit`/custom axioms. Data provenance, build instructions, and version pinning are all present. |

---

## Detailed Assessment

### 1. Trust Boundary Transparency (V8 improvement)

The replacement of `optimize_proof` with raw `native_decide` is a genuine improvement. The earlier macro obscured the proof strategy behind an opaque name; now every call site is explicit and grep-able. The paper's Section 8.3 is commendably honest about the implications: no kernel-checked proof term is produced, a single codegen bug could invalidate all 244 `native_decide` proofs simultaneously, and there is no defense-in-depth for the game-theoretic core.

**However**, the paper slightly undersells the severity. The claim "verified modulo native code generation" appears in the abstract and conclusion, but the practical meaning is that *none* of the headline results (Nash equilibrium, replicator dynamics, popularity paradox inequality) have been independently checked by the Lean kernel. The paper correctly explains that `Fin.foldl` opacity is a structural blocker, not a time-out issue, which is valuable. But the honest framing should be: this is a *computationally certified* analysis, not a *formally verified* one in the strongest sense. The distinction matters for an IEEE venue where readers may not know Lean internals.

**Recommendation:** The abstract should say "certified by Lean 4's native decision procedure" rather than just "formally verified," and a parenthetical "(modulo native code generation)" should appear at first use in the abstract, not only in Section 8.3. Currently the qualification appears too late for a reader who stops at the abstract.

### 2. MatrixConsistency.lean — Adequacy for Data Duplication Concern

This is the most important V8 addition from a formal-methods perspective. The file proves two theorems:

1. `matrix_consistency`: entry-by-entry agreement between `realMatchupMatrix14` (array-based, used in `NashEquilibrium.lean`) and `matchupWR` (function-based, used in `RealMetagame.lean` and `FullReplicator.lean`).
2. `game_matrix_consistency`: agreement between the two `FiniteGame` wrappers built from these representations.

**Assessment:** This is *necessary and sufficient* for eliminating the data-duplication concern between the Nash and replicator modules. It closes the previously open question of whether the two parallel matrix representations could silently diverge. The proof is clean: a single `native_decide` over all 196 cells. 

**Remaining gap:** There is a *third* data copy — the 4-deck subcycle matrix `realCyclePayoff` in `EvolutionaryDynamics.lean`, which manually re-encodes a 4×4 submatrix with payoffs shifted by −500. `MatrixConsistency.lean` does not cover this representation. While the 4-deck results are now superseded by the full 14-deck `FullReplicator.lean` analysis, the paper still cites 4-deck theorems (e.g., `popularity_paradox`, `dragapult_worst_fitness_in_cycle`). A consistency check between `realCyclePayoff` and the corresponding 4×4 subblock of `fullPayoff` (shifted by 500) would close this residual gap.

### 3. DragapultDominated.lean — Proof Quality

This file is well-structured and proves a genuinely useful result: Dragapult is not just absent from the *particular* equilibrium found, but is *strictly* suboptimal against the Nash column mix, ruling it out of *any* best-response support to that column strategy. The combined theorem `dragapult_excluded_from_equilibrium` bundles all four results cleanly.

**Minor concern:** The claim "cannot appear in any Nash equilibrium that uses this column strategy as a best response" (line in the docstring) is slightly stronger than what's proven. What's proven is that Dragapult cannot be a best response to `realNashCol` specifically. If there exist other Nash equilibria with different column strategies, Dragapult could in principle appear there. The symmetric Nash result (`dragapult_zero_symmetric`) strengthens the case, but the docstring should be more precise. The paper text (Section 7) handles this more carefully than the code comments.

### 4. Proof Engineering Quality

**Strengths:**
- The `FiniteGame` / `NashEquilibrium` / `MixedStrategy` abstractions are clean and well-factored.
- `Decidable` instances are provided for all key predicates, enabling the `native_decide` strategy.
- The `EvolutionaryDynamics.lean` → `FullReplicator.lean` → `StepSizeInvariance.lean` dependency chain is well-layered.
- Step-size invariance is proven concretely at three step sizes, which is the right approach given the `native_decide` methodology (symbolic proofs over parameterized `dt` would require different tooling).

**Weaknesses:**
- `EvolutionaryDynamics.lean` still contains the vestigial `optimize_proof` macro definition (line ~18) even though it is no longer used. This is confusing — it should be deleted or the comment should say "retained for backward compatibility."
- The 4-deck subcycle analysis in `EvolutionaryDynamics.lean` (Sections 11–19 in the file) is ~250 lines of theorems that are entirely superseded by `FullReplicator.lean`. The paper cites both. This creates unnecessary proof surface area. Either the 4-deck results should be clearly marked as pedagogical scaffolding (and not cited in the paper's main claims), or they should be removed.
- The `NashEquilibrium.lean` file conflates game-theoretic infrastructure (RPS examples, grid search, 2×2 minimax) with the real 14×14 result. This is a modularity concern: the RPS material is pedagogical, while the real Nash result is the paper's core contribution. Splitting into `GameTheory/Base.lean` and `GameTheory/RealNash.lean` would improve maintainability.
- The Nash equilibrium definition uses a saddle-point formulation (row payoffs ≤ value ≤ column payoffs), which is *stronger* than standard bimatrix Nash for general games. The paper acknowledges this but does not prove the implication formally (saddle-point → bimatrix Nash). For a constant-sum game this is classical, but since the paper emphasizes that the matrix is *not* exactly constant-sum, a brief formal argument or citation would strengthen the claim.

### 5. Verification Claims vs. Actual Verification Scope

The paper claims ~2,500 theorems. Approximately 180 "directly verify empirical claims" and 244 use `native_decide`. The gap between 180 and 244 suggests ~64 `native_decide` uses are in infrastructure/pedagogical material (RPS, 3-deck examples, etc.). This is fine but the paper should make the decomposition clearer. The reader needs to know: of the 180 empirical-claim theorems, how many use `native_decide` vs. kernel-checked tactics?

### 6. Sensitivity Analysis Trust Boundary

The 10,000-iteration sensitivity analysis (Table I) is conducted in Python and explicitly marked as external to the Lean artifact. This is appropriately disclosed. However, the paper draws significant qualitative conclusions from it (core trio inclusion rates, Dragapult zero-weight frequency). Since these results are *not* machine-checked, they occupy an awkward middle ground: important enough to feature prominently but unverified. The paper's own methodology argues that unverified claims are suspect. A brief acknowledgment of this tension would be intellectually honest.

---

## Must-Do Revisions

1. **Qualify "formally verified" in the abstract.** The current abstract says "formally verified modulo native code generation" but this phrasing buries the qualification. Change to "computationally certified using Lean 4's `native_decide` procedure (which trusts the compiler's code generation)" or similar, so that the trust boundary is immediately clear to readers unfamiliar with Lean. The distinction between kernel-checked and native-decide-checked verification is the single most important methodological caveat and should not require reading to Section 8.3 to discover.

2. **Extend `MatrixConsistency.lean` to cover the 4-deck subcycle matrix**, or remove all paper citations to 4-deck results (Sections that reference `realCyclePayoff`, `popularity_paradox` from `EvolutionaryDynamics.lean`). Currently the paper claims matrix consistency is machine-checked, but one of three matrix representations used in cited theorems is not covered by the consistency proof. This is exactly the class of error the consistency module was designed to prevent.

3. **Remove the vestigial `optimize_proof` macro definition** from `EvolutionaryDynamics.lean`. V8's stated goal was to replace `optimize_proof` with `native_decide` for transparency. Retaining the macro definition (even unused) contradicts this goal and will confuse artifact reviewers. If backward compatibility is needed, move it to a clearly-labeled legacy file.

---

## Questions for Authors

1. **On the saddle-point ↔ bimatrix Nash gap:** Your `NashEquilibrium` definition uses a saddle-point condition that is equivalent to Nash equilibrium only for (exactly) zero-sum games. You explicitly note the matrix is *not* exactly constant-sum. Can you provide a formal proof (or a brief argument) that the saddle-point condition you verify implies bimatrix Nash equilibrium for your specific matrix? The current text says it "implies Nash equilibrium in both the zero-sum and general bimatrix senses" but this is stated without proof.

2. **On `Fin.foldl` opacity:** You state that reformulating `sumFin` with structural recursion still fails kernel reduction. Did you attempt a `List`-based fold over an explicit enumeration `[0, 1, ..., 13]` rather than `Fin.foldl`? This pattern has succeeded in other Lean 4 projects for enabling `decide` over small finite domains. If attempted and failed, a brief note would help future proof engineers.

3. **On the Python sensitivity analysis:** The 10,000-iteration resampling is the only evidence for robustness of the Nash support set (Table I). Have you considered implementing even a simplified version in Lean — e.g., verifying that the Nash equilibrium remains valid for a small number of perturbed matrices at the boundary of the Wilson intervals? This would bring at least some robustness evidence inside the trust boundary.

---

## Recommendation

**Weak Accept.**

The paper makes a genuine methodological contribution: this is the first proof-carrying metagame analytics pipeline applied to real tournament data, and the artifact quality is high. The V8 changes (transparent `native_decide`, `MatrixConsistency.lean`, `DragapultDominated.lean`) address prior review concerns substantively. The trust boundary is honestly documented. However, the remaining gap between the paper's verification rhetoric and the actual `native_decide` trust model, the incomplete matrix consistency coverage, and the vestigial macro are concrete issues that should be fixed before publication. None are fatal; all are addressable in a minor revision.
