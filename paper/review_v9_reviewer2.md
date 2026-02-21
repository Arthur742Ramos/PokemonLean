# Review of Submission #753 v9 — Reviewer 2 (Formal Methods Specialist)

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"  
**Venue:** IEEE Transactions on Games  
**Version:** 9 (12 pages)  
**Review date:** 2026-02-20

---

## Summary

The paper presents a Lean 4 artifact (~30K LoC, ~2,500 theorems) that formalizes metagame analysis of the competitive Pokémon TCG. Using Trainer Hill tournament data (Jan–Feb 2026) for 14 archetypes and their full pairwise matchup matrix, the authors prove a "popularity paradox" (the most-played deck, Dragapult, has sub-50% expected win rate), compute and verify a Nash equilibrium assigning Dragapult 0% weight, run full 14-deck replicator dynamics, and provide robustness/sensitivity analysis. V9 removes all `optimize_proof` macros, adds a general symbolic step-size invariance proof, abstracts the `native_decide` caveat, tightens the multiplicity argument, contextualizes skill thresholds, and marks the Python sensitivity analysis as unverified.

---

## Scores

| Criterion         | Score | Comment |
|--------------------|-------|---------|
| **Novelty**        | 4/5   | First proof-carrying metagame analytics pipeline for a real TCG. The methodology-over-domain framing is well-argued. Loses a point because the game-theoretic machinery (Nash via LP, replicator dynamics) is textbook; the novelty is in the *verification*, not the *theory*. |
| **Technical**      | 3/5   | StepSizeGeneral.lean is a proper symbolic proof and a real improvement. But the game-theoretic core rests entirely on `native_decide` with no defense in depth—see below. The trust boundary is now *transparent* but remains *wide*. |
| **Significance**   | 3/5   | Demonstrates feasibility convincingly. Impact is limited by the single-snapshot, single-game scope and by the fact that the verified claims (weighted averages, saddle-point checks) are arithmetically simple enough that the risk of silent error in an unverified pipeline is low. The paper would benefit from a harder verification target. |
| **Clarity**        | 4/5   | Well-structured and unusually honest about limitations. Section IX's trust-boundary discussion is exemplary. Minor: the paper still oscillates between "the rules layer generates falsifiable predictions" and "correlational consistency check"—pick one framing and commit. |
| **Reproducibility**| 5/5   | `lake build` on published sources, ~10 min on M-series. Zero sorry/admit/axiom. MatrixConsistency.lean cross-checks dual representations. Data provenance is explicit. This is the gold standard for artifact-backed game analysis papers. |

---

## Assessment of V9 Changes

### 1. Is the trust boundary now fully transparent?

**Largely yes.** Section IX now explicitly states: (a) `native_decide` trusts the compiler end-to-end, (b) no kernel-checked proof term is produced, (c) 244 theorems share this single trust root, and (d) `decide` is structurally precluded by `Fin.foldl` opacity. The explanation of *why* `decide` fails (not just that it does) is a significant improvement over v8. The paper also correctly notes that a hypothetical codegen bug could simultaneously invalidate the entire game-theoretic core.

**Remaining gap:** The paper does not quantify the *conditional* risk. How many distinct `Fin.foldl`-over-`Rat` evaluation paths does the artifact exercise? If all 244 theorems reduce to the same small set of foldl instantiations, one bug invalidates everything. If they exercise diverse code paths (different matrix sizes, different strategy vectors), the empirical confidence is higher. A brief paragraph characterizing the diversity of the native evaluation workload would close this gap.

### 2. Is StepSizeGeneral.lean a proper symbolic proof?

**Yes.** This is the cleanest file in the artifact. The proof works over `Int`, uses no `native_decide`, and establishes the sign-invariance of `x_i · dt · (f_i − f̄)` via elementary lemmas (`pos_of_mul_pos_of_pos_pos`, `neg_of_mul_neg_of_pos_pos`, `mul_neg_of_pos_pos_neg`). Both the growth and decline directions are covered (`replicator_sign_independent_of_dt`, `replicator_decline_independent_of_dt`). The proof is fully parametric over `xi`, `dt₁`, `dt₂`, and `fiMinusFbar`, with the only hypotheses being positivity of `xi` and both step sizes.

**One concern:** The connection between this symbolic result and the concrete replicator computations is still informal. StepSizeGeneral.lean works over `Int`; the actual dynamics in EvolutionaryDynamics.lean work over `Rat`. The paper says "rational dynamics are recovered by clearing denominators" (comment in StepSizeGeneral.lean) but there is no bridging lemma that formally instantiates the general theorem at the concrete fitness residuals from the 14-deck game. The three concrete dt values in StepSizeInvariance.lean provide empirical confirmation but not a formal link. This is a minor gap—the mathematical argument is obviously correct—but in a paper whose *raison d'être* is eliminating "obviously correct" reasoning, it deserves at least a sentence.

### 3. Is the artifact clean?

**Substantially yes.** V9 improvements:
- All `optimize_proof` macros removed; call sites use `native_decide` directly. This eliminates a layer of indirection that previously obscured what tactic was actually closing each goal.
- No sorry, admit, or custom axioms (verified by grep in prior review round).
- MatrixConsistency.lean formally links the two matrix representations.
- Python sensitivity analysis is now explicitly marked as external and unverified ("produced by an external Python script; these results complement but do not inherit the formal guarantees of the Lean artifact").

**Residual issues:**
- The `GrimssnarlFroslass` typo (acknowledged in a footnote) propagates through the entire artifact. While renaming would be trivial, consistency is the right call for a submission artifact.
- EvolutionaryDynamics.lean is 450+ lines and mixes abstract RPS theory, a 4-deck subcycle, and a 5-deck Ceruledge extension. The full 14-deck results are in a *separate* file (FullReplicator.lean, not provided for review). The modular structure could be tighter.
- NashEquilibrium.lean contains pedagogical 2×2 and 3×3 examples alongside the real 14×14 verification. This is fine for an artifact but bloats the file that contains the paper's central result.

---

## Detailed Technical Comments

### Nash Equilibrium Verification
The verification is sound *within the `native_decide` trust boundary*. The `NashEquilibrium` predicate correctly encodes the saddle-point condition (row best-response ≤ value ≤ column best-response for all pure strategies), which implies Nash equilibrium for both zero-sum and general bimatrix games. The asymmetric and symmetric equilibria are independently verified. The `DragapultDominated.lean` file correctly separates "zero weight in this equilibrium" from "strictly suboptimal against this column mix" (the latter being the stronger, equilibrium-selection-independent claim).

### Sensitivity Analysis Trust
The 10,000-iteration sensitivity analysis (Table I) is now clearly marked as Python-only. The paper appropriately notes that embedding it in Lean is future work. However, the headline claim "core support decks appear in >96% of resampled equilibria" is *not* machine-checked and carries only the trust level of the Python script. The paper should avoid citing these numbers alongside verified results without explicit disambiguation in every instance—currently, Section IV mixes them freely.

### Replicator Dynamics
The full 14-deck results (referenced in the paper but living in FullReplicator.lean) are the strongest evolutionary claims. The 4-deck and 5-deck subcycle analyses in EvolutionaryDynamics.lean are pedagogically useful but technically redundant once the full 14-deck results exist. The paper could better explain *why* both are retained (historical artifact? reader accessibility?).

### SkillSensitivity.lean
Well-designed. The tight bracket style (b ∈ (33, 34] for break-even, b ∈ (60, 61] for Grimmsnarl-matching) provides exact integer thresholds rather than approximate bounds. The contextualization in Section X ("within-tournament skill differentials typically range from 2–5 percentage points") is appropriate and new in v9. Minor: the 2–5pp range is stated without citation. This is a factual claim about competitive TCG skill differentials and needs a reference or explicit "based on our estimate" qualification.

### SharePerturbation.lean
The `paradox_independent_of_popularity` theorem (Dragapult sub-50% for all share values 1–30%) is a clean structural result. The tier-flip L1 bound (`conservativeTierFlipL1Bound > 3/100`) is a nice robustness metric. Both use `native_decide`.

---

## Three Must-Do Revisions

1. **Formally bridge StepSizeGeneral.lean to the concrete dynamics.** Either add a lemma in FullReplicator.lean that instantiates `replicator_sign_independent_of_dt` at the actual fitness residuals of each of the 14 decks (clearing denominators from `Rat` to `Int`), or add a paragraph explicitly stating this connection is left informal and why. The current artifact has a symbolic proof and concrete verifications but no formal link between them. For a paper that claims formal verification as its core contribution, this is a visible seam.

2. **Disambiguate verified vs. unverified results at every point of use.** Table I (sensitivity analysis) is cited in Section IV (Data) alongside Wilson intervals and then again in Section VII (Nash). Add a consistent visual or textual marker (e.g., "†" superscript for unverified-Python results) so that readers never mistake Python-computed sensitivity ranges for Lean-verified bounds. Currently, the disclaimer appears once when the table is introduced but is not repeated when the numbers are reused in the Nash discussion or the conclusion.

3. **Characterize `native_decide` code-path diversity.** Section IX should include a brief analysis of how many *structurally distinct* `Fin.foldl`-over-`Rat` instantiations the 244 `native_decide` theorems exercise. If the answer is "essentially one pattern at three different matrix sizes (3×3, 4×4, 14×14)," say so—it's honest and helps readers calibrate trust. If the answer is "diverse" (different fold functions, different field types), that strengthens the empirical confidence argument.

---

## Three Questions for the Authors

1. **Why not verify the Python LP solution path at the type level?** The Nash weights are large rationals with a shared denominator of 338,129,962,783. These were obtained by `scipy.optimize.linprog` and then converted to exact rationals. Could you instead formalize the LP dual feasibility conditions directly in Lean (dual variables, complementary slackness), providing a *certificate* that the LP was solved correctly? This would eliminate the "discovery tool is untrusted" caveat entirely and would be a stronger methodological contribution than the current verify-the-answer approach.

2. **What is the actual `lake build` time for FullReplicator.lean specifically?** The paper reports ~10 min total. If the full 14-deck `native_decide` proofs dominate build time, this suggests the native evaluator is working hard on large rational folds—relevant to the trust-boundary discussion. If they're fast, that's also informative (small proof terms, less surface area for codegen bugs).

3. **Have you tested the artifact against a second Lean toolchain version?** Reproducing all 244 `native_decide` results on, e.g., Lean 4.x.0 and 4.y.0 with different compiler backends would provide empirical evidence that the native evaluation is consistent across codegen implementations, substantially mitigating the single-point-of-failure concern. If you have done this, report it. If not, consider it for the camera-ready.

---

## Recommendation: **Weak Accept**

The paper presents a genuinely novel methodology—proof-carrying metagame analytics—with an impressively clean artifact. V9 has addressed the major concerns from prior rounds: `optimize_proof` opacity is gone, the `native_decide` trust boundary is now transparent and honestly discussed, StepSizeGeneral.lean provides a proper symbolic proof, and the Python sensitivity analysis is correctly marked as external. The reproducibility standard is exemplary.

The remaining weaknesses are: (a) the symbolic-to-concrete bridge gap in the step-size argument, (b) insufficient disambiguation of verified vs. unverified results throughout the text, and (c) the `native_decide` monoculture in the game-theoretic core, which the paper discusses honestly but cannot currently mitigate. None of these are fatal, but (a) and (b) should be fixed before publication. The paper makes a credible case that formal verification is feasible and valuable for empirical game analysis, even if the specific domain results (Dragapult is overplayed) are not themselves surprising.

The contribution is primarily methodological, and the methodology is sound within its stated trust boundary. With the three must-do revisions, this is a publishable contribution to IEEE Transactions on Games.
