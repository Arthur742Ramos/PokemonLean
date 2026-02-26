# IEEE Transactions on Games — Reviewer 2 Report

**Submission #753:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Reviewer expertise:** Empirical game theory, metagame analysis, competitive esports analytics

---

## Summary

The paper presents a Lean 4–verified metagame analysis of the competitive Pokémon TCG, using Trainer Hill tournament data (Jan–Feb 2026) to establish a "popularity paradox": the most-played deck (Dragapult, 15.5% share) has a sub-50% field-weighted expected win rate, while a less popular deck (Grimmsnarl, 5.1%) achieves the highest expected win rate (52.7%). The artifact (~30K lines, 2,500 theorems) also certifies a Nash equilibrium excluding Dragapult, computes replicator dynamics over the full 14-deck game, and verifies Bo3 amplification effects. The primary contribution is methodological—demonstrating proof-carrying analytics for real competitive game ecosystems.

---

## Scores

| Criterion | Score | Comments |
|---|---|---|
| **Novelty** | 4 | The coupling of a real tournament dataset to machine-checked Nash equilibrium certification in Lean 4 is genuinely new. The idea of formal verification for metagame analytics is original and well-motivated. Docked one point because the game-theoretic analysis itself (Nash LP, replicator dynamics) is completely standard. |
| **Technical Soundness** | 3 | The formal artifact appears solid within its stated trust boundary, and the authors are commendably transparent about limitations. However, several methodological concerns reduce confidence (detailed below). |
| **Significance** | 3 | The methodological template is interesting and potentially influential, but the specific results (popularity paradox, Nash support) are narrow in scope—a three-week snapshot of one game. The practical competitive insight is limited. |
| **Clarity** | 4 | Well-organized and generally well-written. The v12 revisions addressing the causal chain framing and Nash uniqueness are substantive improvements. Some sections remain dense. |
| **Reproducibility** | 4 | The `lake build` workflow and artifact availability are strong. The Python sensitivity analysis being external is a minor gap. Data provenance from Trainer Hill is adequately documented. |

---

## Overall Recommendation: **Weak Accept**

The paper makes a genuine methodological contribution in an underexplored area. The v12 revisions address several prior concerns substantively. However, remaining issues with the empirical methodology and some framing choices prevent a stronger recommendation. I would accept with minor revisions addressing the concerns below.

---

## Detailed Comments

### 1. "Algebraic Sufficiency" Framing (Replacing "Causal Chains")

The v12 reframing from "causal chains" to "algebraic sufficiency" is a significant improvement and largely appropriate. The inequality showing that Dark-type weakness *alone* is algebraically sufficient to drag Dragapult below 50% (even granting 50% against all non-Dark opponents) is a clean, well-scoped claim. This is honest mathematical reasoning rather than causal overclaiming.

**Minor concern:** The narrative around this result still uses language like "the formal connection runs: *rules* → *type assignments* → *empirical confirmation* → *weighted drag*" (Section III-A), which reads like a causal chain even if the authors have relabeled it. The arrow notation suggests directionality that the formal result doesn't establish. The correlation between the type chart and empirical matchups could be driven by confounders (e.g., deckbuilding conventions that respect type matchups, player expectations creating self-fulfilling prophecies). I'd recommend softening this passage to emphasize that these are *consistent layers* rather than a directed derivation.

**Positive note:** The explicit acknowledgment that "type advantage is a necessary structural factor but not sufficient on its own" and the treatment of N's Zoroark exceptions are well-handled.

### 2. Nash Uniqueness Caveat

The Nash uniqueness caveat is now prominently and clearly stated. The paper includes:
- A dedicated paragraph in Section VII ("Formally verified evidence") clearly distinguishing ∃ from ∀
- The sentence "uniqueness of this equilibrium is not proven" in both Table IV caption and body text
- Explicit acknowledgment that "other Nash equilibria... could in principle assign Dragapult positive weight"
- A separate "Complementary unverified evidence" paragraph for the sensitivity analysis

This is sufficient. The distinction between "equilibrium-consistent" and "equilibrium-necessary" is well-articulated and limits prescriptive overclaiming appropriately.

**One suggestion:** Consider whether the abstract should also qualify the Nash result. The current abstract says "A machine-checked Nash equilibrium with six-deck support assigns Dragapult 0% weight"—this is technically correct but could be read as implying uniqueness by a casual reader. A parenthetical "(one verified equilibrium among potentially many)" would be maximally transparent.

### 3. CausalChain.lean as "Integration Tests"

The reframing of CausalChain.lean from compositional derivations to "cross-module integration tests" is honest and clear. The paper now explicitly states:

> "These are conjunctions of independently verified facts from different modules, serving as cross-module integration tests rather than compositional derivations where one module's output feeds as input to the next."

This is a mature and accurate description. The distinction between conjoining facts and composing derivations is important and correctly drawn. The paper further identifies the algebraic sufficiency inequality as the *one* theorem where module outputs are arithmetically combined rather than merely conjoined. This level of precision is commendable.

**Minor note:** The name `CausalChain.lean` is now somewhat misleading given the reframing. While the authors note they "retain the original identifier for artifact consistency," a future revision should consider renaming this module to something like `IntegrationTests.lean` or `CrossModuleBridge.lean` to match the paper's own characterization.

### 4. Type Assignment Methodology

The v12 treatment of type assignments is adequate but could be stronger. The paper now includes:
- A dedicated paragraph ("Type assignment methodology") acknowledging these are "domain-expert modeling choices, not formally derived from deck composition"
- Acknowledgment that multi-type decks "require judgment"
- The note that "the 83% alignment rate... would change if borderline assignments were revised"

**Remaining concern:** The paper does not provide a sensitivity analysis for the type assignments themselves. The 83% alignment is presented as impressive (with a binomial null p < 0.001), but the relevant question is not "are these assignments better than random?" but "how sensitive are the downstream conclusions to borderline assignments?" For instance, if Dragapult Charizard were classified differently, would the Dark→Psychic alignment count change materially? The authors should either (a) enumerate the borderline cases and show robustness, or (b) more explicitly scope the type-alignment analysis as illustrative rather than load-bearing—since the popularity paradox and Nash results don't actually *depend* on the type-alignment bridge.

This is important because the type-alignment bridge is rhetorically central (it's the "structural explanation for the popularity paradox") but analytically optional—the paradox is established purely from the matchup matrix and share data, without any reference to types.

### 5. Empirical Methodology

This is where I have the most significant concerns.

**5a. Data sourcing and potential biases.** The authors acknowledge Trainer Hill as a third-party aggregator and note potential biases (self-selection, platform effects, 50-player threshold). However, the treatment is too brief for a journal publication. Key questions:

- What fraction of total competitive Pokémon TCG events in this window are captured? If Trainer Hill captures only a subset of Limitless events, there may be systematic selection effects.
- Are online and in-person events pooled? If so, is there evidence that matchup win rates differ by platform? This is a known issue in esports analytics.
- The 50-player threshold is stated but not justified. Why 50? How many events are excluded, and do excluded events have systematically different metagame compositions?

**5b. Sample sizes and statistical adequacy.** The paper reports sample sizes for a few matchup pairs (Dragapult mirror: 2,845; Gholdengo vs Dragapult: 2,067) but does not provide the full sample-size matrix. For a 14×14 matrix, many off-diagonal cells likely have much smaller counts. The smallest matchups involve low-share decks (Ceruledge at 2.3% vs Kangaskhan at 2.5%)—these cells may have only tens of games, making the point estimates unreliable.

The Wilson interval analysis partially addresses this, but the reported intervals are selective (only largest and smallest matchups). I would want to see:
- The full distribution of sample sizes across all 196 cells
- The number of cells with fewer than 50 games (a common adequacy threshold)
- Whether any conclusions depend on cells with wide confidence intervals

**5c. Sensitivity analysis methodology.** The 10,000-iteration sensitivity analysis is useful but has methodological issues:

- Sampling "uniformly from the Wilson 95% confidence interval" is not the correct Bayesian posterior or frequentist resampling procedure. The posterior for a binomial proportion is Beta-distributed, not uniform. Uniform sampling from a confidence interval overweights the tails relative to the posterior and underweights the center. This likely inflates the variance of the Nash weight estimates.
- The sensitivity analysis resamples each cell independently, ignoring the constraint that $M_{ij} + M_{ji}$ should be approximately 1000 (minus tie effects). Independent resampling can generate implausible matrices.
- The "2.1% exact support recovery" is potentially alarming—it means the specific equilibrium is extremely fragile. The paper frames this positively (core trio has >96% inclusion), but the instability of the full support set deserves more discussion.

**5d. Tie convention.** The $T/3$ convention is stated but its impact is not thoroughly analyzed. The paper says "our robustness analysis shows the headline results are insensitive to this choice" but I could not find a formal or quantitative statement of this claim. How do the expected win rates change under alternative tie weights ($T/2$, $T = 0$)?

### 6. Additional Technical Comments

**6a. Replicator dynamics scope.** The paper correctly notes that discrete-time Euler steps establish directional pressure rather than convergence. The step-size independence proof is a nice touch. However, the "preliminary directional check" (Section VII-B) reveals a fundamental limitation: single-step replicator predictions failed for Grimmsnarl due to cascade effects. This undermines the practical utility of the replicator analysis and deserves more prominent discussion. The paper should either (a) present multi-step simulation results or (b) more explicitly scope the replicator analysis as establishing instantaneous pressure only.

**6b. Two-player model.** The paper models deck selection as a two-player game, which is standard but worth scrutinizing. In a large Swiss tournament, each player faces a sequence of opponents drawn from the field distribution, not a single strategic opponent. The two-player model is a mean-field approximation that ignores pairing correlations (e.g., Swiss pairing tends to match players with similar records, creating skill-stratified subfields). The paper acknowledges this ("does not capture all competitive incentives") but understates the issue.

**6c. "Other" category.** Excluding 30.5% of the field is a significant modeling choice. The robustness analysis (Dragapult needs 57.6% vs Other to reach 50% overall) is helpful but assumes uniform performance against an undifferentiated mass. In reality, "Other" contains many distinct archetypes with varying matchup profiles, and some may be concentrated counter-picks against specific modeled decks.

**6d. native_decide trust boundary.** The discussion of native_decide limitations is thorough and honest. The structural preclusion argument (Fin.foldl opacity) is well-explained. One question: have the authors verified any subset of the 244 native_decide theorems via alternative means (e.g., independent Python computation of the same quantities)? Cross-validation against an independent implementation would strengthen confidence even if it doesn't provide formal guarantees.

### 7. Minor Issues

- The identifier typo `GrimssnarlFroslass` (double-s, single-m) is acknowledged but distracting. Consider fixing the source and noting the change.
- Table I (sensitivity analysis) lists Gholdengo with "---" for point estimate but 40.5% inclusion. Clarify why no point estimate is given (presumably 0% in the verified equilibrium but nonzero in many resampled ones).
- The binomial test for type alignment (p < 0.001) uses a null of 50% alignment, but a more appropriate null would account for the base rate of type-effectiveness relationships in the type chart. If many type pairs have effectiveness relationships, the expected alignment under random assignment would be higher than 50%.
- Figure 3 (interaction motif) is a nice visualization but only shows 4 of 14 decks. Consider expanding or explicitly noting the selection criteria.

### 8. Questions for the Authors

1. What is the total number of games across all 196 matchup cells? What is the median cell count?
2. Have you considered using the Beta posterior rather than uniform sampling for the sensitivity analysis?
3. Can you provide the replicator trajectory over multiple steps (e.g., 100 steps) to assess whether the dynamics converge to the Nash support?
4. Is there any evidence that the tie convention ($T/3$) versus alternatives ($T/2$, $T = 0$) affects the Nash support composition, not just the game value?

---

## Summary of Requested Revisions

**Required (for acceptance):**
1. Provide summary statistics for the full sample-size distribution across the matchup matrix (min, median, quartiles, number of cells below 50 games).
2. Address the uniform-vs-Beta sampling issue in the sensitivity analysis, or justify the uniform choice.
3. Soften the arrow-notation causal language in Section III-A to match the correlational framing elsewhere.

**Recommended:**
4. Qualify the Nash result in the abstract.
5. Discuss the type-alignment bridge as illustrative rather than load-bearing, or provide type-assignment sensitivity analysis.
6. Add a quantitative statement about tie-convention robustness.
7. Expand the replicator dynamics discussion to address the Grimmsnarl prediction failure more prominently.
8. Cross-validate native_decide results against independent computation.

---

*Reviewer 2, IEEE Transactions on Games*
*Date: February 20, 2026*
