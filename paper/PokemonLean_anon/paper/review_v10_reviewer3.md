# IEEE Transactions on Games — Review of Submission #753 (v10)

**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game

**Reviewer:** R3 (Empirical Game Theory / Esports Analytics)
**Date:** 2026-02-20

---

## Summary

The paper presents a Lean 4 formalization (~30K lines, ~2,500 theorems, zero `sorry`) coupling Pokémon TCG rules, a 14×14 empirical matchup matrix from Trainer Hill tournament data (Jan–Feb 2026), and downstream game-theoretic analysis: expected win rates, machine-checked Nash equilibrium, replicator dynamics, and Bo3/Swiss considerations. The headline finding is a "popularity paradox" (Dragapult: 15.5% share / 46.7% expected WR; Grimmsnarl: 5.1% / 52.7%). V10 improvements include honest labeling of the skill-sensitivity thresholds as author estimates, clear separation of verified vs. unverified evidence, and documentation of the Int↔Rat bridge.

---

## Overall Assessment

**V10 is honest and transparent.** The paper now carefully delineates what is machine-checked (Nash best-response conditions, replicator fitness signs, skill thresholds) from what is external (Python sensitivity analysis, behavioral interpretation, skill-magnitude estimates). The `native_decide` trust boundary is documented with unusual candor, including the structural impossibility of `decide` due to `Fin.foldl` opacity—something most Lean papers would silently omit. The skill-bias thresholds (3.4pp break-even, 6.1pp Grimmsnarl-matching) are now labeled as reflecting "the authors' competitive experience and available tournament analytics," not sourced empirical fact. This is the correct epistemic posture.

The remaining issues are real but, in my judgment, **not publication-blocking**. They are addressable via minor revisions or camera-ready edits.

---

## Scores

| Criterion | Score (1–5) | Notes |
|---|---|---|
| **Novelty** | 4 | First proof-carrying metagame analytics pipeline for a real TCG. The methodology—coupling rules formalization with empirical payoff verification—is genuinely new. Deducted 1 point because the game-theoretic tools themselves (LP-based Nash, discrete replicator) are standard. |
| **Technical** | 4 | The Lean artifact is impressive in scope and discipline. The Nash certification via 14×14 best-response checks is sound. Deducted 1 for: (a) entire game-theoretic core rests on `native_decide` with no defense-in-depth, (b) sensitivity analysis is Python-only, creating a verified/unverified seam right at the robustness claim. |
| **Significance** | 3 | Methodological contribution is clear but the audience overlap between formal verification practitioners and esports analysts is small. The specific metagame findings (Dragapult is overplayed) are timely but ephemeral. Impact depends on whether the template is adopted for other games. |
| **Clarity** | 4 | Well-structured, honest about limitations, good use of tables and the scatter plot. The paper is dense at 12 pages but reads well. Minor: the index-mapping paragraph (Section VII) is hard to parse; a visual mapping or table footnote would help. |
| **Reproducibility** | 5 | Exemplary. `lake build` reproduces all claims. Data provenance is explicit. The cross-file `MatrixConsistency.lean` check eliminating copy-paste errors between modules is a best practice other formal verification papers should adopt. |

---

## Detailed Comments

### Strengths

1. **Epistemic discipline.** The verified/unverified boundary is now cleanly drawn. Table I labels sensitivity ranges as "not frequentist confidence intervals." The behavioral-economic interpretation (Section VI-C) is explicitly flagged as hypothesis, not proven consequence. This is a model for how empirical game theory papers should present mixed-evidence claims.

2. **The SkillSensitivity.lean file is excellent.** Tight integer thresholds (33 < b ≤ 34 for break-even; 60 < b ≤ 61 for matching Grimmsnarl) provide a crisp, falsifiable answer to the reviewer question "how big must the confound be?" The prose now correctly frames the 3.4pp and 6.1pp values as author judgment, not sourced calibration.

3. **StepSizeGeneral.lean provides a clean symbolic proof** that replicator direction is algebraically dt-independent, with an honest bridge comment explaining that Lean.Rat lacks the ordering lemmas needed for a fully general Rat proof, so the Int result is composed with concrete `native_decide` checks. This is exactly the right level of transparency.

4. **The symmetric Nash cross-check** (Table V, `SymmetricNash.lean`) with game value exactly 500 and 7-deck support substantially strengthens the Dragapult-exclusion claim. Having two independent equilibrium formulations agree on zero Dragapult weight is more convincing than either alone.

5. **DragapultDominated.lean** cleanly separates the claim "zero weight in our computed equilibrium" from the stronger "strictly suboptimal against the Nash column mix." The paper text (Section VII) now explicitly notes this does not logically preclude Dragapult from equilibria with different column strategies. Good.

### Weaknesses

1. **The "Other" 30.5% remains a gap.** The worst-case bounds (Dragapult needs 57.6% vs. Other to break even) are informative but the paper still lacks any empirical estimate of what Dragapult's win rate against unmodeled decks actually is. Even a rough aggregate from the Trainer Hill data would help readers assess whether the worst case is plausible.

2. **The type-advantage bridge (Section III-A) overstates its epistemic weight.** The 83% alignment (15/18) uses manually assigned primary attack/defense types. The binomial p-value (p < 0.001 under random assignment) is valid but the null hypothesis is weak—random type assignment is not a serious competing model. A more informative comparison would be against a naive "most popular attack type" heuristic. As it stands, the bridge demonstrates internal consistency of the authors' type assignments, not an independent validation of the rules→matchup causal chain.

3. **Predictive validation (Section VII-B) is thin.** One day of post-window data, 2/3 correct directional predictions, and a post-hoc explanation for the miss (Grimmsnarl suppressed by rising Absol). This is below the standard for predictive claims. Either expand to multiple windows or downgrade the language from "predictive validation" to "illustrative consistency check."

---

## 3 Must-Do Revisions

1. **Rename Section VII-B from "Predictive Validation" to "Preliminary Directional Check" (or similar).** A single post-window observation with a 2/3 hit rate and a post-hoc rationalization for the miss does not constitute validation. The current title overpromises. Alternatively, add rolling-window backtesting across 3+ disjoint windows before claiming any validation.

2. **Provide an empirical estimate (even rough) for Dragapult's win rate against the "Other" 30.5%.** The worst-case analysis is already verified in Lean, but readers need a point estimate to assess how close to the worst case reality is. If Trainer Hill exposes aggregate performance against non-top-14 decks, report it with appropriate caveats. If not, state this data gap explicitly rather than leaving readers to wonder.

3. **Soften the type-advantage bridge's statistical claim.** Replace "the observed 83% corresponds to p < 0.001 under a binomial null, confirming that the alignment is not coincidental" with language acknowledging that the null (random type assignment) is deliberately weak and that the test demonstrates internal consistency of the authors' archetype type assignments rather than independent causal validation. The formalization is valuable as a correlational check; it should not be dressed as causal confirmation.

---

## 3 Questions for the Authors

1. **What is the wall-clock time for `native_decide` on the Nash equilibrium theorem specifically?** The paper reports ~10 min total build time. If the Nash verification dominates (say, 8 of 10 minutes), this has implications for scaling to larger matrices (e.g., 20+ archetypes). Have you profiled this?

2. **The sensitivity analysis shows the exact Nash support is recovered in only 2.1% of iterations, yet core decks appear in >96%.** Does this mean the equilibrium is practically unique in its core but has a high-dimensional manifold of near-equilibria differing only in the tail? If so, what does this imply for competitive advice—should a player choose the core trio and randomize among the remainder?

3. **You note that `Fin.foldl` opacity structurally prevents `decide`.** Have you considered reformulating `sumFin` as a recursive function over `List (Fin n)` or `Vector`, which might be kernel-reducible? If this was tried and failed, a brief note in the paper would be valuable for the Lean community.

---

## Recommendation

**Weak Accept.**

The paper makes a genuine methodological contribution (proof-carrying metagame analytics), is unusually honest about its trust boundaries and limitations, and the artifact is exemplary in reproducibility. The game-theoretic content is standard but competently applied; the novelty is in the verification methodology. V10 has addressed the most serious concerns from earlier rounds (skill-bias labeling, verified/unverified separation, Int↔Rat bridge). The three must-do items above are minor revisions, not structural problems. The paper is suitable for IEEE Transactions on Games after these revisions.

---

*Reviewer 3 — Empirical Game Theory / Esports Analytics*
