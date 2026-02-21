# Review of Submission #753 v10 — Reviewer 2 (Formal Methods Specialist)

**IEEE Transactions on Games**

**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game

**Reviewer expertise:** Formal verification, proof assistants (Lean/Coq/Isabelle), certified decision procedures, trust boundaries in mechanized proofs.

---

## Summary

The paper presents a ~30,000-line Lean 4 artifact that encodes Pokémon TCG metagame data and formally verifies game-theoretic claims over a 14×14 matchup matrix derived from Trainer Hill tournament data. The headline result is a "popularity paradox"—Dragapult (15.5% meta share) has sub-50% expected win rate while Grimmsnarl (5.1% share) achieves the highest. A six-deck Nash equilibrium excluding Dragapult is machine-checked, along with full 14-deck replicator dynamics. V10 improvements include direct `native_decide` usage (removing `optimize_proof` macro), honest framing of skill-bias estimates, paragraph-level verified/unverified evidence labeling, and documentation of the Int↔Rat bridge.

---

## Detailed Assessment

### 1. Trust Boundary (`native_decide`)

The paper's treatment of the `native_decide` trust boundary is the most thorough I have seen in an applied Lean 4 paper. The authors:

- Quantify exposure: 244 of ~2,500 theorems use `native_decide`.
- Explain *why* `decide` is structurally precluded (`Fin.foldl` opacity to the kernel reducer), not merely slow—a crucial distinction that shows they actually attempted the alternative.
- Acknowledge the single-point-of-failure risk: a code-generator bug affecting `Rat` arithmetic over `Fin.foldl` would invalidate the entire game-theoretic core simultaneously.
- Note the absence of defense in depth for the core results.

**Assessment:** Adequate for publication, but not fully addressed. The paper correctly identifies the risk but proposes no mitigation beyond "future kernel improvements." Two concrete mitigations are feasible now and should be discussed: (a) cross-checking a representative subset of `native_decide` results against an independent implementation (e.g., Python `fractions.Fraction` with exact rational arithmetic—they already have the Python LP solver), and (b) testing with multiple Lean toolchain versions to reduce correlated code-gen failure probability. The absence of even a sentence acknowledging these cheap mitigations is a gap.

**Severity:** Minor. The trust boundary is honestly stated; the gap is in mitigation strategy, not disclosure.

### 2. Int↔Rat Bridge

This is the most technically interesting gap in the artifact and where v10 makes the weakest improvement.

**What exists:**
- `StepSizeGeneral.lean` proves step-size sign invariance over `Int`: if `x_i > 0` and `dt > 0`, then `sign(x_i * dt * (f_i - f̄))` depends only on `sign(f_i - f̄)`. This is clean, well-structured, and fully formal.
- A `StepSizeGeneralBridge` namespace contains a **comment-level** argument that the `Int` result transfers to `Rat` because `Lean.Rat` denominators are always positive, so `sign(a * b * c) = sign(c)` when `a, b > 0` over rationals follows from the integer case after clearing denominators.
- The comment defers to `StepSizeInvariance.lean` for concrete `native_decide` checks at `dt = 1/10, 1/100, 1`.

**What is missing:**
- There is **no formal lemma** bridging `Int` sign reasoning to `Rat` sign reasoning. The `StepSizeGeneralBridge` namespace is empty of theorems—it contains only comments. This means the composition claimed in the paper ("the symbolic and computational proofs compose end-to-end") is a prose claim, not a machine-checked one.
- The paper states: "A bridging corollary extends this result from integers to the rational arithmetic used by the concrete replicator implementation." This is misleading. No such corollary exists as a Lean theorem. The "bridging" is: (a) a natural-language argument in comments, and (b) concrete `native_decide` checks at three specific step sizes. Neither constitutes a formal bridging corollary.
- The informal argument is *correct*—the transfer is straightforward once you have `Rat.mul_pos` and `Rat.pos_of_num_pos`—but the fact that `Lean.Rat` (as opposed to Mathlib's `Rat`) lacks the ordering/multiplication lemmas needed to state this is itself worth noting as a limitation.

**Assessment:** The gap between what the paper claims ("bridging corollary") and what exists (comments + concrete checks) is the single most significant intellectual honesty issue remaining in v10. The concrete `native_decide` checks at three step sizes are sufficient *evidence* but they are not the *general* bridge the paper implies. The paper should either (a) state a formal `Rat`-level lemma (even if it requires importing a few Mathlib facts), or (b) downgrade the language from "bridging corollary" to "verified at three concrete step sizes with informal argument for generality."

**Severity:** Moderate. The mathematical content is sound, but the paper overclaims the formalization status of this specific result.

### 3. Verified vs. Unverified Evidence Separation

V10 introduces paragraph-level labels (`Formally verified evidence` / `Complementary unverified evidence`), visible in Section VII (Nash Equilibrium). This is a genuine improvement over v9. The separation is clear where it appears.

However, the labeling is inconsistent across sections:
- Section VI (Popularity Paradox): No explicit verified/unverified labels, though the content is predominantly verified.
- Section V (Data): The Wilson interval discussion is unverified (computed externally) but not labeled as such until a parenthetical note on the sensitivity analysis table.
- Section VIII (Tournament Strategy): Bo3 amplification is verified; Swiss probability claims appear to be unverified. No labels.

**Assessment:** The principle is right; the execution is incomplete. Either apply the labeling convention uniformly or state upfront that *all* claims without a `\texttt{theorem}` citation are unverified complements.

**Severity:** Minor.

### 4. Nash Equilibrium Verification

The core Nash verification is well-structured:
- `NashEquilibrium` is defined as a proper saddle-point condition (row best-response ≤ value ≤ column best-response for all pure strategies).
- The equilibrium weights are sourced externally (Python `linprog`) and verified internally (Lean `native_decide` over all 14 best-response checks per player).
- `MatrixConsistency.lean` cross-checks array-based vs. function-based matrix representations.
- `DragapultDominated.lean` proves strict suboptimality, not just zero weight.
- Both asymmetric and symmetric (constant-sum) formulations are verified.

This is the strongest part of the artifact. The discovery/verification separation is cleanly documented. The `MatrixConsistency` module eliminates an entire class of representation-mismatch bugs.

**One concern:** The `NashEquilibrium` definition uses a saddle-point condition that is *stronger* than bimatrix Nash for general games but *equivalent* only for zero-sum/constant-sum games. The paper acknowledges the matrix is not exactly constant-sum. The saddle-point condition still implies bimatrix Nash (since row-can't-improve + column-can't-improve → Nash), but the converse doesn't hold. The paper should clarify that the verified property is *sufficient* for Nash in the general bimatrix sense, which it does in prose—but the Lean definition is named `NashEquilibrium` without qualification, which could mislead readers into thinking it captures the standard bimatrix definition exactly.

### 5. Replicator Dynamics

The evolutionary dynamics are verified at both 4-deck subcycle and full 14-deck scales. The step-size invariance argument (sign depends only on `f_i - f̄`) is algebraically obvious but the formal proof is clean. The predictive validation (2/3 directional predictions confirmed, with the Grimmsnarl failure explained by multi-step cascade effects) is refreshingly honest.

**Gap:** The replicator dynamics use Euler discretization but the paper does not bound the discretization error or discuss whether the discrete dynamics preserve any invariant of the continuous system (e.g., the share product as a Lyapunov function). The Lyapunov analysis in `EvolutionaryDynamics.lean` is verified only for the 3-deck RPS toy model, not for the real 14-deck system. This is not a fatal gap—the directional claims are step-size independent—but the paper could be clearer that the Lyapunov results do not transfer to the real metagame analysis.

### 6. Skill-Bias Sensitivity

V10 reframes the 2–5pp skill-bias estimate as "based on the authors' competitive experience and available tournament analytics." This is honest framing—no false precision. The machine-checked thresholds (3.4pp to reach 50%, 6.1pp to match Grimmsnarl) are the right way to handle this: compute the *required* confound magnitude and let the reader judge plausibility.

### 7. Artifact Quality

- Zero `sorry`, zero `admit`, zero custom axioms—verified by inspection.
- `optimize_proof` macro fully removed; all call sites use `native_decide` directly.
- Module structure is logical and well-documented.
- Cross-file consistency checking (`MatrixConsistency.lean`) is a best practice I haven't seen in comparable artifacts.

---

## Scores

| Criterion        | Score | Comment |
|------------------|-------|---------|
| **Novelty**      | 4/5   | First proof-carrying metagame analytics pipeline for a real TCG. Novel methodological contribution. Not 5/5 because the game-theoretic tools (Nash, replicator) are standard. |
| **Technical**    | 3/5   | Sound but with the Int↔Rat bridge overclaim and incomplete trust-boundary mitigation. The `native_decide` dependency is correctly disclosed but unmitigated. Core verification structure is strong. |
| **Significance** | 3/5   | Demonstrates feasibility of formal methods for empirical game analysis. Limited competitive-tactical impact (acknowledged by authors). Significance depends on whether the methodology is adopted. |
| **Clarity**      | 4/5   | Well-written, well-structured. Verified/unverified labeling is a good innovation but inconsistently applied. The paper is long but the density is justified by the methodological contribution. |
| **Reproducibility** | 5/5 | Exemplary. Full source, build instructions, `lake build` in ~10 min. Cross-file consistency theorems. One-to-one mapping between paper claims and named theorems. This is the gold standard for reproducibility in formal methods papers. |

---

## Recommendation: **Weak Accept**

The paper makes a genuine methodological contribution—proof-carrying metagame analytics—and the artifact quality is high. The trust boundary disclosure is among the best I've seen for `native_decide`-heavy Lean 4 work. The remaining gaps (Int↔Rat bridge overclaim, incomplete verified/unverified labeling, no trust-boundary mitigation strategy) are addressable in a minor revision. The reproducibility is exemplary and the domain application is novel.

The paper does not quite reach Accept because the Technical score reflects a real gap between claimed and actual formalization status of the bridge result, and because the `native_decide` concentration without any cross-validation strategy leaves the game-theoretic core more fragile than the paper's framing suggests.

---

## 3 Must-Do Revisions

1. **Fix the Int↔Rat bridge claim.** Either (a) provide an actual Lean theorem (even a thin wrapper using `native_decide` for the general `Rat` case, or import minimal Mathlib `Rat` ordering lemmas) that formally states the bridge, or (b) change "A bridging corollary extends this result" to accurately describe what exists: a comment-level argument verified concretely at three step sizes. The current wording implies a formal lemma that does not exist. This is the most important revision.

2. **Add a trust-boundary mitigation paragraph.** The disclosure of `native_decide` risk is excellent, but the paper proposes zero mitigation. Add: (a) a statement about whether any subset of the 244 `native_decide` results were cross-checked against an independent implementation (the Python LP solver already provides partial cross-validation for Nash), and (b) whether the artifact was tested against multiple Lean toolchain versions. If neither was done, state that explicitly as future work.

3. **Uniform verified/unverified labeling.** Either (a) extend the paragraph-level `Formally verified evidence` / `Complementary unverified evidence` labels to all sections containing mixed evidence (especially Sections V, VI, VIII), or (b) add a single upfront statement (e.g., in Section IX) that all claims not accompanied by a `\texttt{theorem}` reference are unverified complements, and remove the per-paragraph labels. The current inconsistency—labels in Section VII but not elsewhere—suggests the labeling was retrofitted locally rather than applied as a systematic design principle.

---

## 3 Questions for the Authors

1. **On the bridge:** You state that `Lean.Rat` "currently lacks general ordering/multiplication lemmas." Have you considered importing `Mathlib.Data.Rat.Order` to state the bridge lemma formally? The required lemmas (`Rat.mul_pos`, `Rat.sign_mul`) exist in Mathlib. If there is a specific technical obstacle (e.g., `Lean.Rat` vs. Mathlib `Rat` incompatibility), please document it—this would be valuable to the Lean community.

2. **On equilibrium uniqueness:** You verify *a* Nash equilibrium and show Dragapult is strictly suboptimal against that equilibrium's column strategy. But you explicitly note this "does not logically preclude Dragapult from equilibria with different column strategies." Have you considered proving uniqueness of the equilibrium support (e.g., via non-degeneracy of the support submatrix), or is the bimatrix structure too far from constant-sum for standard uniqueness arguments to apply? The sensitivity analysis (Dragapult excluded in 77.9% of resampled equilibria) suggests non-uniqueness is a real concern—in 22.1% of perturbations, Dragapult *does* enter the support.

3. **On the `NashEquilibrium` definition:** Your definition uses the saddle-point / minimax formulation (∀ i, rowPurePayoff ≤ value ∧ ∀ j, value ≤ colPurePayoff). For the non-constant-sum bimatrix game you actually have, the standard Nash definition would be: ∀ i, expectedPayoff(e_i, s2) ≤ expectedPayoff(s1, s2) ∧ ∀ j, expectedPayoff(s1, e_j) ≤ expectedPayoff(s1, s2) (for column player's *own* payoff matrix). Since you verify both row and column best-response conditions against the *same* payoff matrix, you are implicitly assuming the game is zero-sum. Is this intentional? If so, does the tie-convention-induced deviation from constant-sum affect the validity of interpreting the result as a Nash equilibrium of the actual bimatrix game?

---

*Reviewed: 2026-02-20*
*Reviewer: #2 (Formal Methods)*
*Submission: #753 v10*
