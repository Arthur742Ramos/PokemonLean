# IEEE Transactions on Games — Review

**Submission:** #753 v10
**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game
**Reviewer Expertise:** Verification Engineering, Software Engineering, Proof Assistants

---

## Scores

| Criterion        | Score |
|------------------|-------|
| Novelty          | 4/5   |
| Technical Soundness | 4/5 |
| Significance     | 3/5   |
| Clarity          | 4/5   |
| Reproducibility  | 5/5   |

**Recommendation: Accept**

---

## Summary

This paper presents a ~30,000-line Lean 4 artifact that formally verifies game-theoretic metagame analysis for the competitive Pokémon Trading Card Game. Using real tournament data (Trainer Hill, Jan–Feb 2026), the authors encode a 14×14 matchup matrix and prove: (1) a "popularity paradox" where the most-played deck (Dragapult, 15.5% share) has sub-50% expected win rate while Grimmsnarl (5.1% share) achieves the highest fitness; (2) a machine-checked Nash equilibrium with six-deck support assigning Dragapult 0% weight, plus a symmetrized constant-sum Nash with seven-deck support confirming this; (3) full 14-deck replicator dynamics classifying 5 growing and 9 shrinking archetypes; and (4) robustness bounds including skill-sensitivity analysis and share-perturbation theorems. The primary contribution is methodological: demonstrating that proof-carrying analytics is feasible and valuable for real competitive game ecosystems.

---

## Strengths

### S1: Exemplary Proof Engineering Discipline and Transparency

The artifact demonstrates outstanding engineering standards. Zero `sorry`, zero `admit`, zero custom axioms — verified by inspection across all 80+ files. The `native_decide` trust boundary is not only disclosed but thoroughly analyzed (Section IX), including a frank admission that `Fin.foldl` opacity structurally precludes kernel-checked `decide`, and that all ~244 `native_decide` uses share a single failure mode. This level of self-criticism regarding trust assumptions is rare in verification papers and sets a high bar for the field. The `StepSizeGeneral.lean` file is particularly well-crafted: a clean symbolic proof over `Int` followed by a principled `Int↔Rat` bridge with only a single `native_decide` for the trivial `(0 : Rat).num = 0` fact — demonstrating that the authors understand *where* to push for stronger guarantees and where computational verification is acceptable.

### S2: Compositional Architecture with Cross-Module Consistency

The module structure is well-designed for maintainability and correctness. The `MatrixConsistency.lean` file — which machine-checks entry-by-entry agreement between the array-based matrix (used for Nash verification) and the function-based `matchupWR` (used for replicator dynamics) — eliminates an entire class of copy-paste and representation-mismatch errors that plague multi-module formal developments. The dependency chain (`NashEquilibrium.lean` → `EvolutionaryDynamics.lean` → `FullReplicator.lean` → `SkillSensitivity.lean`) is cleanly layered, with each module importing only what it needs. The separation between discovery (external Python LP solver) and certification (Lean best-response checks) is a well-established and sound verification pattern. The `FiniteGame` structure with decidable `NashEquilibrium` predicate is clean and reusable.

### S3: Comprehensive Sensitivity and Robustness Engineering

The robustness analysis is unusually thorough for a verification paper. The artifact provides machine-checked bounds across multiple threat vectors: (a) `Robustness.lean` gives worst-case bounds for the unmodeled 30.5% of the field; (b) `SharePerturbation.lean` proves the paradox holds across all Dragapult share levels from 1–30%; (c) `SkillSensitivity.lean` establishes tight integer thresholds (3.4pp break-even, 6.1pp Grimmsnarl-matching) for a uniform skill confound to reverse conclusions; (d) the 10,000-iteration sensitivity analysis (external Python, correctly disclaimed) shows 96%+ core support inclusion. The two-sided tightness pattern (`threshold_breakeven` paired with `threshold_breakeven_tight`) is excellent proof engineering practice — it establishes the exact boundary rather than merely a sufficient condition.

---

## Weaknesses

### W1: Heavy Reliance on `native_decide` Concentrates Trust Risk

The paper honestly acknowledges this, but the practical implication deserves emphasis: approximately 244 of the ~2,500 theorems — including *all* of the game-theoretic core (Nash equilibrium verification, replicator dynamics, matchup consistency, skill sensitivity) — rely on `native_decide`. This means the entire strategic analysis layer shares a single, unmitigated trust dependency on Lean 4's compiler pipeline. The authors explain that `Fin.foldl` opacity makes kernel-checked `decide` structurally impossible, but they do not explore alternative formulations (e.g., `List`-based fold with `Decidable` instances, or `Vector`-based recursion) that might enable at least partial kernel-level verification. The `StepSizeGeneral.lean` bridge demonstrates that the authors *can* write kernel-checked proofs when they choose to; the question is whether more of the game-theoretic core could be similarly lifted. A brief exploration or negative result documenting attempted alternatives would significantly strengthen the trust story.

### W2: Large Infrastructure-to-Core Ratio Raises Proportionality Questions

Of the ~30,000 lines and 2,510 theorems, approximately 180 directly verify empirical claims. The remaining ~93% is characterized as "infrastructure" — rules formalization, card effects, type effectiveness, deck legality, probability theory, etc. While the paper argues this infrastructure "future-proofs" the framework for counterfactual analysis, the connection between the rules layer and the strategic analysis is thin: it consists primarily of type-advantage alignment checks (Section III.A) showing that Dark attackers beat Psychic defenders 83% of the time — a correlational check, not a causal derivation. The deck legality checker (`checkDeckLegal_iff`) is mentioned but never actually invoked in the analytical pipeline. Similarly, card conservation theorems (e.g., `professorsResearchEffect_preserves_cards`) and energy economy bounds (`ENERGY_BOTTLENECK`) do not feed into any matchup or equilibrium computation. The paper should more clearly delineate which infrastructure modules are *load-bearing* for the headline claims versus aspirational for future extensions, and whether a lighter artifact focused on the game-theoretic core would sacrifice any verified guarantee.

### W3: Equilibrium Uniqueness Not Addressed; Sensitivity Analysis External

The verified Nash equilibria are *a* Nash equilibrium, not *the* Nash equilibrium. While uniqueness is not claimed (correctly noted in Table IV and V captions), this creates an interpretive gap: the statement "Dragapult receives 0% Nash weight" is verified for one specific equilibrium, but the paper's narrative reads as if this is a general property. The `DragapultDominated.lean` theorem `dragapult_strictly_suboptimal` partially addresses this by proving Dragapult is strictly suboptimal *against the verified Nash column strategy*, but this does not rule out equilibria with different column strategies where Dragapult might participate. The grid-search uniqueness approach (demonstrated for 3×3 games in `NashEquilibrium.lean` lines 163–234) does not scale to 14×14. More critically, the 10,000-iteration sensitivity analysis — which provides the strongest robustness evidence (77.9% Dragapult exclusion) — is entirely external Python, not verified in Lean. The authors correctly disclaim this, but it means the paper's strongest argument for robustness stands outside its formal framework. The gap between what is formally verified and what is rhetorically relied upon should be made more explicit in the abstract and conclusion.

---

## Minor Issues

1. **Identifier inconsistency:** `GrimssnarlFroslass` (single-m, double-s) vs. "Grimmsnarl" in prose. The footnote on p.5 acknowledges this but it creates friction for artifact auditors. Consider a `notation` alias.

2. **Paper line 734–735:** The sentence about concrete verification at dt = 1/10, 1/100, and 1 is duplicated verbatim.

3. **EvolutionaryDynamics.lean** is 40KB and contains both abstract 3-archetype theory and concrete 14-deck setup. Consider splitting for clarity, especially since `FullReplicator.lean` already factors out the 14-deck analysis.

4. **Missing Lean version pinning in paper:** The paper specifies "Lean 4" but does not state the exact toolchain version (e.g., `leanprover/lean4:v4.x.0`). Given the `native_decide` dependency, toolchain version matters for reproducibility.

5. **`FiniteGame` structure** has an unused `payoff` field (`fun _ _ => 0` in all instantiations). The `n` field (number of players) is also always 2. Consider simplifying to a `TwoPlayerGame` with only `m` and `matrix`.

6. **Bo3 amplification** (Section VIII) uses a parametric formula but only verifies concrete instances (55%–95% in 5pp steps). A symbolic proof that Bo3 amplifies for all p ∈ (0.5, 1) would be natural and more informative.

---

## Questions for Authors

1. Have you attempted `List`-based or structurally-recursive `sumFin` variants that might pass kernel reduction for `decide`? If so, what specifically failed?

2. The `realNashDenom` is a 12-digit integer (338129962783). How was this exact rational equilibrium computed from the LP solver output? Is there a verified rational reconstruction step, or manual exact-fraction entry?

3. Could the type-advantage alignment analysis (83% directional accuracy) be strengthened to a formal statistical test within Lean (e.g., exact binomial p-value computation)?

4. What is the build time breakdown? The paper says ~10 min total; how much is `native_decide` on the 14×14 matrix versus infrastructure compilation?

---

## Verdict

This is a well-executed methodological contribution that convincingly demonstrates proof-carrying analytics for competitive game ecosystems. The proof engineering quality is high, the trust boundaries are honestly documented, the robustness analysis is unusually thorough, and the artifact is clearly reproducible. The main weaknesses — concentrated `native_decide` trust, large infrastructure overhead, and the gap between verified and external robustness claims — are real but do not undermine the core contribution. The paper would benefit from tighter scoping of which infrastructure is load-bearing, a brief negative result on `decide` alternatives, and more careful language around equilibrium uniqueness. Overall, the work makes a solid case that formal verification is feasible and valuable for empirical game-theoretic analysis at realistic scale, and the methodology is portable to other strategic domains with discrete strategies and measurable payoffs.

**Recommendation: Accept** with minor revisions addressing the duplicated sentence, identifier inconsistency cleanup, and clearer delineation of verified vs. external claims in the abstract.
