# IEEE Transactions on Games — Submission #753
## Review by Reviewer 1 (Game Theory / Equilibrium Computation)

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Version:** v12

**Date:** 2026-02-20

---

## Summary

The paper presents a Lean 4 formalization (~30K lines, 2,500 theorems) of metagame analysis for the Pokémon Trading Card Game, using real tournament data from Trainer Hill (Jan–Feb 2026). The core empirical finding is a "popularity paradox": the most-played deck (Dragapult, 15.5% share) has only 46.7% expected win rate against the field, while Grimmsnarl (5.1%) achieves 52.7%. The authors compute a Nash equilibrium (verified by best-response checks over all 14 strategies), run replicator dynamics on the full 14-deck game, and perform sensitivity analysis. The primary claim is methodological: formal verification is feasible and valuable for competitive game analytics.

---

## Scores

| Criterion | Score (1–5) | Comments |
|---|---|---|
| **Novelty** | 4 | Novel combination of formal verification with real tournament metagame data. The idea of "proof-carrying analytics" for competitive games is original and well-motivated. |
| **Technical Soundness** | 3 | Core equilibrium verification is correct modulo `native_decide`. Several framing and modeling choices require more careful treatment (see detailed comments). |
| **Significance** | 3 | The methodological contribution is genuine but the cost-benefit remains debatable for the game theory community. The specific metagame results are illustrative rather than deep. |
| **Clarity** | 3 | Generally well-organized. Some sections are forthright about limitations; others conflate verified and unverified claims or use framing that slightly oversells the formal guarantees. |
| **Reproducibility** | 4 | Excellent artifact discipline (no sorry, no admit, `lake build` instructions). The `native_decide` trust boundary and Python sensitivity analysis are clearly delineated. |

---

## Detailed Comments

### 1. "Algebraic Sufficiency" Framing (replacing "causal chains")

The v12 paper has clearly improved its framing. The key inequality—showing that Dark-type losses *alone* are algebraically sufficient to drag Dragapult below 50% even granting 50% against all non-Dark opponents—is a clean, well-defined mathematical claim and is appropriately labeled "algebraic sufficiency." This is a genuine contribution: it isolates a sufficient condition from the data and proves it formally. The framing is appropriate.

**However, I have concerns about residual causal language.** The paper still refers to a "structural explanation" for the popularity paradox and describes the chain as running from "rules" through "type assignments" to "empirical confirmation" to "weighted drag." This is correlational—the paper acknowledges this—but the directional arrow notation (→) and the word "explanation" carry causal connotations that the formal machinery does not support. The type chart does not *cause* matchup outcomes in any formally verified sense; it merely *correlates* with them at 83% alignment given domain-expert type assignments. I would recommend replacing "structural explanation" with "structural consistency" or "structural association" throughout.

The algebraic sufficiency theorem itself is clean and I have no objections to it. It is the strongest single theorem in the paper.

### 2. Nash Uniqueness Caveat

**This is now handled well.** The paper explicitly states:

> "Importantly, uniqueness of this equilibrium is not proven: other Nash equilibria of the same game could in principle assign Dragapult positive weight."

The table caption says "Uniqueness is not proven." The discussion explicitly distinguishes "equilibrium-consistent" from "equilibrium-necessary." This is a significant improvement over what I would expect in earlier versions. 

**Minor remaining issue:** The abstract says the Nash equilibrium "assigns Dragapult 0% weight" without the uniqueness qualifier. At least a parenthetical "(in the verified equilibrium)" would be appropriate, since the abstract is the most-read part of the paper and readers may not reach the caveat in Section VII.

**Substantive concern:** For the 14×14 bimatrix game (which is *not* exactly zero-sum due to the tie convention), the Nash equilibrium set could be complex. The paper verifies *one* equilibrium per formulation (asymmetric and symmetric). Given the sensitivity analysis shows exact support recovery in only 2.1% of resampled matrices, this suggests the equilibrium landscape is quite fragile. The paper should discuss whether the LP solver's equilibrium is a vertex equilibrium of the feasible polytope and whether other vertices might include Dragapult. The 77.9% exclusion rate from sensitivity analysis is reassuring but is unverified (Python).

### 3. CausalChain.lean as "Integration Tests"

The paper now describes CausalChain.lean theorems as "conjunctions of independently verified facts from different modules, serving as cross-module integration tests rather than compositional derivations where one module's output feeds as input to the next."

**This is honest and I commend the clarification.** Having examined the file, the theorems are indeed large conjunctions resolved by `decide` or `native_decide`. They verify that multiple independently-stated facts are simultaneously true, but they do not demonstrate that the output of one module is *consumed* as input by the next in a compositionally typed way. The one exception—the algebraic sufficiency inequality—is correctly identified as the theorem where module outputs are arithmetically combined.

**Remaining concern:** Despite the honest characterization in the paper text, the Lean file itself still uses the module name `CausalChain` and doc-comments describing a "causal pipeline: Rules → Types → Damage → Matchups → Expected WR → Nash → Dynamics → Tournament." The file header claims these demonstrate the modules "are NOT disconnected components but form an integrated causal pipeline." If this file is part of the reviewed artifact, there is a disconnect between the paper's careful framing and the artifact's more assertive framing. Renaming the module to `IntegrationTests.lean` or `CrossModuleBridge.lean` and updating doc-comments would align the artifact with the paper's claims.

Additionally, the "Grand Causal Chain" theorem (`grand_causal_chain`) and "The Complete Story" (`the_complete_story`) are effectively proof-of-concept demonstrations that several facts coexist, not derivations. A conjunction of 11 facts, each independently `decide`-able, does not establish a logical dependency chain. The arrows in the doc-comments (→) are misleading even within the Lean source.

### 4. Type Assignment Methodology

The paper now includes a dedicated paragraph:

> "The primary attack/defense type assignments are domain-expert modeling choices, not formally derived from deck composition or card data."

**This is adequate and I appreciate the transparency.** The paper correctly notes that multi-type decks require judgment calls, that all assignments are auditable in `ArchetypeAnalysis.lean`, and that the 83% alignment rate would change under different assignments. Treating these as modeling assumptions analogous to the matchup matrix itself is the right framing.

**Suggestion for improvement:** The binomial test (p < 0.001 for 15/18 alignment vs. 50% random baseline) is a useful sanity check but the null hypothesis of "random type assignments" is unrealistic. A more informative comparison would be: what alignment rate would we expect from any reasonable set of single-type proxies for multi-card decks? The current null is too weak to be convincing evidence of anything beyond "types matter somewhat in Pokémon"—which is not surprising. I don't require this for acceptance but it would strengthen the argument.

### 5. Game-Theoretic Modeling Concerns

**5a. Two-player game abstraction.** The paper models deck selection as a two-player bimatrix game. In a Swiss tournament with N players, the relevant strategic interaction is more complex: you face a sequence of opponents drawn (approximately) from the population, and your payoff is reaching a win threshold, not winning a single match. The paper acknowledges this ("modeling limitation") but I think it deserves more emphasis. The Nash equilibrium of the two-player game is not the Nash equilibrium of the N-player tournament game. In particular, in the tournament game, variance matters: a player might prefer a deck with 48% expected win rate but low variance over one with 52% expected but high variance if the objective is reaching X-2 in 8 rounds. This is briefly mentioned but its implications for the "Dragapult is suboptimal" claim are not fully explored.

**5b. Replicator dynamics interpretation.** The paper is appropriately cautious about replicator dynamics, framing results as "directional diagnostics." The preliminary validation (Section VII-A) is refreshingly honest: 2/3 predictions confirmed, with the Grimmsnarl failure illustrating multi-step cascade effects. This is good scientific practice.

**5c. The sub-50% game value.** The Nash game value of ~47.97% is below 50% due to the tie convention. The paper explains this. However, this means the game is slightly negative-sum in the win-rate metric, which complicates the interpretation of "expected win rate vs. field" as a strategic fitness measure. If both players play optimally and still average below 50%, the fitness benchmark should arguably be the game value (~48%), not 50%. Under this benchmark, Dragapult's 46.7% is only ~1.3pp below optimal rather than 3.3pp. The paper should at least acknowledge this alternative benchmark.

### 6. The `native_decide` Trust Boundary

The paper handles this well: 244 of ~2,500 theorems use `native_decide`, and the structural reason `decide` cannot substitute (opaque `Fin.foldl` in kernel reducer) is clearly explained. The honest assessment that a single compiler bug could invalidate the game-theoretic core is appreciated.

However, the paper states this is "the standard approach for computational proofs over finite structures in the Lean community" which, while true for many projects, may not be appropriate for a paper whose primary contribution is the *trustworthiness* of formal verification. If the verification's selling point is machine-checkability, the paper should more forthrightly discuss the gap between "machine-checked" and "kernel-checked."

### 7. Minor Issues

- The abstract mentions "2,500 theorems—of which roughly 190 directly verify empirical claims." What do the other 2,310 theorems verify? Infrastructure, presumably, but the ratio invites questions about proof bloat. A brief characterization would help.
- The `GrimssnarlFroslass` typo footnote is charming but also slightly concerning for an artifact-centric paper—it suggests the data-entry process was not fully systematic.
- Table I (sensitivity analysis): "95% sensitivity ranges" with the caveat that these are not frequentist confidence intervals is good. But the column header still says "95% Range" which may be misread. Consider "Sensitivity Range (95% of iterations)."
- The paper would benefit from a comparison with at least one other TCG metagame analysis tool or framework to contextualize the 30K-line investment.

---

## Questions for Authors

1. Have you investigated whether the LP solver returns a vertex equilibrium, and whether other vertex equilibria of the bimatrix game include Dragapult in their support?
2. Could the algebraic sufficiency result be strengthened to show that Dragapult is dominated (weakly or strictly) by some mixed strategy, which would exclude it from *all* Nash equilibria?
3. What is the plan for aligning the artifact's internal documentation (CausalChain.lean headers/comments) with the paper's more careful "integration test" framing?

---

## Overall Assessment

The paper presents a genuinely novel methodological contribution: proof-carrying analytics for a real competitive game ecosystem. The formal artifact is impressive in scope and the authors are commendably transparent about trust boundaries (`native_decide`), modeling assumptions (type assignments, top-14 normalization), and the limits of their Nash analysis (no uniqueness proof). The algebraic sufficiency framing is a clear improvement and the Nash uniqueness caveat is now prominent.

The main weaknesses are: (a) residual causal language that slightly oversells the formal guarantees, (b) the gap between the paper's careful framing and the artifact's CausalChain.lean documentation, (c) insufficient discussion of the two-player vs. N-player tournament game distinction, and (d) the game-value benchmark issue.

None of these are fatal. The paper is above the acceptance threshold for its methodological novelty and artifact quality, but requires minor revisions to fully deliver on its transparency promises.

---

## Recommendation: **Weak Accept**

The methodological contribution is real and the artifact is strong. Revisions needed:
1. Add uniqueness qualifier to the abstract's Nash claim.
2. Align CausalChain.lean naming/documentation with paper's "integration test" framing.
3. Discuss the game-value (~48%) vs. 50% benchmark issue for fitness interpretation.
4. Soften "structural explanation" to "structural association" or similar.
5. Briefly discuss two-player vs. N-player tournament equilibrium implications more substantively.
