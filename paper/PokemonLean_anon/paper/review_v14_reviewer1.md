# IEEE Transactions on Games — Review of Submission #753 (v14)

**Reviewer:** 1  
**Expertise:** Game theory, equilibrium computation, evolutionary dynamics  
**Revision round:** 4 (v14)  
**Date:** 2026-02-20  

---

## Summary of Changes in v14

The authors have made three categories of revision since v13:

1. **Nash uniqueness gap (my primary v13 concern):** The paper now explicitly discusses Avis–Fukuda vertex enumeration as future work and notes that the game's approximate constant-sum structure (deviations <3% from $M_{ij}+M_{ji}=1000$) makes uniqueness "plausible but not guaranteed." The existential/universal distinction is stated clearly: "there exists a Nash equilibrium excluding Dragapult, not that all equilibria do so."

2. **NEW Table VIII (assurance breakdown):** A detailed kernel-vs-compiler theorem census (~2,256 kernel-level vs ~244 compiler-level) makes the trust boundary quantitatively transparent.

3. **Replicator language softening:** "predict decline/dominance" → "indicate downward/upward fitness pressure"; "single-step replicator dynamics" used consistently. This addresses my v12 concern about overclaiming from one-step Euler discretizations.

---

## Assessment of v14 Changes Against Prior Concerns

### Nash Uniqueness Gap: Adequately Addressed (for publication)

This was my main v13 sticking point. The v14 treatment is honest and technically correct:

- The existential-vs-universal distinction is now front-and-center in the Nash section, not buried in a caveat.
- The Avis–Fukuda citation is appropriate. For a 14×14 bimatrix game, vertex enumeration is computationally feasible (the Lemke–Howson or support enumeration methods would also work here), so flagging this as "future work" rather than "intractable" is accurate.
- The plausibility argument via approximate constant-sum structure is well-calibrated: in exact constant-sum games, the Nash equilibrium strategy set is convex (both players' equilibrium sets are faces of the strategy simplex), which strongly constrains multiplicity. The <3% deviation makes uniqueness plausible without making it certain.
- The complementary Python evidence (Dragapult excluded in 77.9% of 10,000 resampled equilibria) provides useful robustness context, with the unverified status clearly flagged.

**What would have been stronger:** Actually running Avis–Fukuda (or `lrslib`) on the 14×14 matrix and reporting whether multiple equilibria exist. This is a straightforward computation (minutes at most for this matrix size) and would have converted the plausibility argument into a definitive answer. I do not require this for acceptance, but I note it would have been easy to do and would have strengthened the paper materially.

**Remaining gap:** The paper's prescriptive conclusion—that Dragapult exclusion is "equilibrium-consistent"—is weaker than "equilibrium-necessary." For the methodological contribution, this is acceptable. For competitive advice, this matters. The paper correctly frames itself as methodological, so the residual gap is within acceptable bounds.

### Table VIII (Assurance Breakdown): Valuable Addition

The kernel/compiler split is now quantified rather than merely described. The ~90/10 ratio (kernel/compiler by theorem count) is reassuring, and the category-level granularity (12 Nash, 38 replicator, 25 bridge, 42 sensitivity, ~127 other matrix) makes it easy to assess exposure. This table should have been present from v11; better late than never.

One observation: the 244 compiler-level theorems include *all* the empirically interesting claims. The 2,256 kernel-level theorems are infrastructure—correct, but not what readers cite. This concentration risk is inherent and well-documented; I flag it for reader awareness, not as a deficiency.

### Replicator Language: Fully Resolved

The "single-step replicator dynamics" framing and "indicate pressure" language are exactly right. The v13 language occasionally slipped into predictive mode; v14 is disciplined throughout. The preliminary directional check (Section VII) honestly reports the Grimmsnarl misprediction and correctly attributes it to multi-step cascade effects beyond the single-step model's scope.

---

## Detailed Scores

### Novelty: 4/5 (unchanged from v13)

The combination remains unprecedented: Lean 4 + real tournament data + Nash certification + replicator dynamics over a complete empirical matchup matrix. The Avis–Fukuda discussion adds methodological awareness but not novelty per se. The core game theory is textbook; the novelty is in the verified empirical application.

### Technical Soundness: 4/5 (unchanged)

**Strengths carried forward:**
- Saddle-point Nash verification with all 14 best-response checks per player.
- Symmetric Nash on constant-sum symmetrization (game value exactly 500) as robustness check.
- Step-size sign invariance proved symbolically (kernel-level, no `native_decide`).
- Causal sufficiency inequality: Dark losses alone sufficient for sub-50% fitness, using symbolic reasoning over parameterized win rates.

**Residual concerns (not new to v14):**
- Wilson intervals are not propagated through the Nash LP. The Python sensitivity analysis is a reasonable substitute but breaks the verification chain.
- The single-step replicator limitation is fundamental to the discrete-time Euler approach. The Grimmsnarl misprediction demonstrates this is not merely theoretical.
- Equilibrium uniqueness remains unproven. As noted above, this is now honestly stated but still limits the strength of the Dragapult-exclusion claim.

None of these are v14 regressions, and all are adequately discussed.

### Significance: 3/5 (unchanged)

The methodological contribution (proof-carrying metagame analytics) is real and the marginal-cost argument (200 LOC to update for new data) strengthens practical relevance. However:
- Three-week empirical window limits lasting value of specific findings.
- No second domain demonstrated.
- The audience intersection (formal methods ∩ competitive TCG ∩ game theory) remains narrow.

I note that significance is the hardest criterion to improve through revision; it reflects the scope of the contribution, which is inherently a proof-of-concept.

### Clarity: 4/5 (slight improvement from v13)

The v14 revisions improve clarity in three specific ways:
1. The abstract now leads with the `native_decide` trust boundary, preventing readers from assuming kernel-level assurance throughout.
2. The existential/universal Nash distinction is stated in the paragraph immediately following the verification, not deferred to threats-to-validity.
3. Table VIII provides a scannable summary of what is and isn't kernel-checked.

Minor remaining issues:
- The `GrimssnarlFroslass` typo, while footnoted, still appears dozens of times in theorem names cited in the paper. This is a cosmetic annoyance, not a technical issue.
- The CausalChain module name remains despite the paper acknowledging the chains are "conjunctions of independently verified facts" rather than causal derivations. The "named for historical reasons" disclaimer is adequate but slightly awkward.

### Reproducibility: 5/5 (unchanged)

Exemplary. `lake build`, ~10 min, zero-sorry, zero-admit, no custom axioms. Data provenance explicit. Python sensitivity script included. MatrixConsistency cross-check. This remains the paper's strongest dimension.

---

## What Would Push Me from Weak Accept to Accept

After four revision rounds, I want to be specific about the remaining gap:

1. **Run equilibrium enumeration.** The Avis–Fukuda / `lrslib` computation on a 14×14 matrix is trivial (I estimate <1 minute wall time). If all equilibria exclude Dragapult, the existential result becomes universal and the headline claim is substantially stronger. If some equilibria include Dragapult, the paper should report this honestly—it would actually be an interesting finding about equilibrium multiplicity in approximately constant-sum games. Either outcome improves the paper. This is the single most impactful change remaining, and it requires minimal effort.

2. **Alternatively (or additionally):** A second metagame window (even a brief one) demonstrating the framework's reuse would address the significance concern. The marginal-cost argument claims 200 LOC; demonstrating it on a second snapshot would be compelling.

Neither of these is strictly *required* for the paper's methodological contribution to merit publication, which is why I remain at Weak Accept rather than Reject. But either would tip the balance.

---

## Minor Issues (new in v14)

1. **Table VIII row "Other matrix computations (~127)":** This is a large bucket. A one-sentence description of what these 127 theorems cover would help readers assess whether they're substantive or boilerplate.

2. **Avis–Fukuda citation [avis1992pivoting]:** The standard reference is Avis & Fukuda (1992) "A pivoting algorithm for convex hulls and vertex enumeration of arrangements and polyhedra," but the Nash enumeration application is better attributed to Avis, Rosenberg, Savani & von Stengel (2010) or the `lrslib` documentation. Consider adding the more specific reference.

3. **"Approximate constant-sum structure makes uniqueness plausible":** This inference deserves one more sentence of justification. In exact constant-sum (zero-sum) games, the equilibrium *strategy set* is convex but equilibria can still form a continuum (e.g., matching pennies with redundant strategies). The claim should note that uniqueness of the equilibrium *payoff* is guaranteed in zero-sum games (minimax theorem), and that the <3% deviation bounds the payoff perturbation, making strategy-set perturbation arguments applicable.

4. **Preliminary directional check (Section VII):** The 2-of-3 success rate is reported but not statistically contextualized. With 3 predictions and a naive base rate of 50% (random direction), 2/3 is not significant ($p = 0.5$ under binomial). This is fine—the check is "preliminary"—but the paper should note that the sample is too small for statistical conclusions.

---

## Overall Assessment

v14 is the strongest version I have reviewed. The Nash uniqueness gap—my primary v13 concern—is now honestly characterized with appropriate technical context (Avis–Fukuda, approximate constant-sum plausibility, existential/universal distinction). The assurance breakdown table and replicator language corrections are welcome. The paper's core strengths (unprecedented verified metagame pipeline, exemplary reproducibility, honest threat analysis) remain intact.

The gap to Accept is narrow but real: the equilibrium enumeration computation is both easy and impactful, and its absence feels like a missed opportunity rather than an inherent limitation. The significance score (3/5) reflects the proof-of-concept nature of the work, which revision cannot fully address.

---

## Recommendation: **Weak Accept**

The paper makes a genuine and novel methodological contribution, now with appropriately calibrated claims about equilibrium properties. The v14 revisions adequately address my v13 concerns. The remaining gap (equilibrium enumeration, second-domain demonstration) would strengthen the paper but is not fatal to the contribution. The work merits publication as a proof-of-concept for formally verified competitive game analysis.

**Score Summary:**

| Criterion        | v13 | v14 | Δ   |
|------------------|-----|-----|-----|
| Novelty          | 4/5 | 4/5 | —   |
| Technical Sound. | 4/5 | 4/5 | —   |
| Significance     | 3/5 | 3/5 | —   |
| Clarity          | 4/5 | 4/5 | (+) |
| Reproducibility  | 5/5 | 5/5 | —   |

*Clarity shows qualitative improvement within the 4/5 band but not enough to cross to 5/5.*

**Overall: Weak Accept** (unchanged from v11, v12, v13)

---

## Questions for Authors

1. Have you attempted running `lrslib` or any vertex enumeration tool on the 14×14 matrix? If so, what were the results? If not, what prevents this?

2. The ~127 "other matrix computations" at compiler trust level—could you provide a brief categorization? Are these matchup-level facts, ranking comparisons, or something else?

3. The preliminary directional check uses a one-day-after snapshot. Have you considered a systematic backtesting protocol (e.g., weekly rolling windows with prediction scoring) to assess the replicator framework's predictive calibration over time?
