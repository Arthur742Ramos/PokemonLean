# Review of Submission #753 (v13, Revision Round 3)

**Reviewer:** Reviewer 2  
**Expertise:** Empirical game theory, metagame analysis, competitive esports analytics  
**Date:** 2026-02-20  
**Venue:** IEEE Transactions on Games

---

## Summary

The paper presents a formally verified metagame analysis of the Pokémon TCG, using Lean 4 to machine-check claims about a "popularity paradox" (the most-played deck is suboptimal), Nash equilibria over a 14-archetype matchup matrix, and replicator dynamics predictions. The artifact is ~30K lines across 81 files with ~2,500 theorems and no `sorry`. Data comes from Trainer Hill (Jan 29–Feb 19, 2026).

This is revision 3 (v13). I have reviewed earlier versions. The authors have made substantive improvements: qualifying the Nash uniqueness claim, renaming "algebraic sufficiency" to "numerical sufficiency," replacing the causal arrow-chain with four independently verified facts, and clarifying domination status.

---

## Scores

| Criterion         | Score | Comments |
|--------------------|-------|----------|
| **Novelty**        | 4/5   | The methodological contribution—proof-carrying metagame analytics—is genuinely novel. No prior work applies formal verification at this scale to empirical competitive game data. |
| **Technical Soundness** | 3/5 | Improved but still has structural issues. See detailed comments below. |
| **Significance**   | 3/5   | Demonstrates feasibility of an interesting methodology, but the empirical results themselves are routine metagame observations. |
| **Clarity**        | 4/5   | Substantially improved from v12. Qualifications are now mostly honest and well-placed. |
| **Reproducibility** | 4/5  | Strong artifact with `lake build` instructions. Python sensitivity analysis external to Lean is clearly marked. |

---

## Overall Recommendation: **Weak Accept**

The paper has improved meaningfully across revisions and now presents its claims with appropriate qualification. It makes a genuine methodological contribution to the intersection of formal methods and game-theoretic esports analysis. I still have reservations about the cost-benefit argument and some modeling choices, but these are no longer blockers.

---

## Detailed Comments

### What improved since v12 (positive)

1. **Nash uniqueness qualification.** The abstract now explicitly states "uniqueness is not proven; other equilibria may differ." This was my primary concern in round 2, and the authors have addressed it thoroughly—both in the abstract and in the Section VII discussion. The careful distinction between "there exists an equilibrium excluding Dragapult" vs. "all equilibria exclude Dragapult" is exactly right.

2. **"Numerical sufficiency" renaming.** Replacing "algebraic sufficiency" with "numerical sufficiency" is honest. The inequality is checked over concrete constants, not proven symbolically over parameterized inputs. The new framing correctly characterizes the contribution.

3. **Arrow-chain replacement.** The four independently verified facts (rules, type assignments, empirical data, population weights) with explicit mutual-consistency framing is a major improvement. The v12 arrow-chain implied a causal derivation that wasn't there; the new version correctly describes correlational consistency across four layers.

4. **Domination clarification.** Explicitly stating Dragapult is *not* strictly dominated (citing the 64.1% Charizard lane) prevents a common misreading. This is technically important: non-domination means Dragapult *could* appear in some Nash equilibrium, making the uniqueness caveat substantive rather than pro forma.

5. **CausalChain.lean naming.** Acknowledging "named for historical reasons" is a small but welcome honesty. The file now serves as cross-module integration tests rather than claiming to establish causation.

### Remaining concerns

#### Technical Soundness (moderate issues)

**T1. The two-player game model is underdefended for a tournament setting.**  
The paper acknowledges (§VII) that Swiss tournaments create different incentives than head-to-head play, but then proceeds to base all equilibrium analysis on the two-player model anyway. For an empirical game theory venue, this is a significant modeling gap. In Swiss, your "opponent" is drawn from a pairing pool conditioned on your record—not uniformly from the field. A 6-2 player in round 7 faces a systematically different distribution than the field average. The Nash equilibrium over the unconditional matchup matrix may not be strategically relevant for actual tournament decisions. The paper's own §VIII acknowledges this but treats it as a "modeling limitation" rather than engaging with the Swiss-pairing literature. I'd like to see at least a paragraph discussing how the equilibrium shifts under record-conditioned opponent distributions, even if only qualitatively.

**T2. The `native_decide` concentration remains uncomfortable.**  
The authors are now fully transparent about this (§IX), and I appreciate the honest discussion of why `decide` is structurally precluded. But the fact remains that 244 theorems—including *all* game-theoretic core results—share a single trust assumption. The paper correctly notes "no defense in depth for the game-theoretic core." For a paper whose primary contribution is formal verification, this is an inherent tension. I accept the authors' position that this is a known Lean 4 limitation and standard practice, but it should be weighted when evaluating the strength of the "formally verified" claim. The qualifier "modulo the `native_decide` trust boundary" in the abstract and conclusion is appropriate and sufficient.

**T3. Sensitivity analysis is external to Lean.**  
The 10,000-iteration bootstrap is Python, not Lean. The paper is clear about this, but it means the robustness claims (Table II) lack the formal guarantees that are the paper's main selling point. The "exact support set recovered in only 2.1% of iterations" is a striking fragility result that deserves more discussion. Is the point estimate equilibrium a knife-edge? The core support trio (Grimmsnarl/Absol/Raging Bolt at 96-98% inclusion) is reassuring, but the fact that the *exact* equilibrium is so fragile somewhat undermines the significance of having verified *this particular* equilibrium.

#### Significance (moderate concern)

**S1. The popularity paradox itself is not surprising.**  
As a metagame analyst, I find the headline result—most popular deck ≠ best deck—to be a well-known phenomenon in every competitive game with public metagame data. The MTG, LoL, and Hearthstone communities have documented this repeatedly. The *formal verification* of this fact is novel, but the fact itself is not. The paper now frames the contribution as "methodological rather than competitive-tactical" (§I), which is the right framing, but I worry that the extensive presentation of the paradox (all of §VI, much of §V) reads as if the empirical finding is the main result. Consider rebalancing toward the methodology.

**S2. Cost-benefit remains hard to justify for practitioners.**  
Table IX is honest: 30K lines vs. 100 lines of Python for equivalent outputs. The authors argue marginal update cost is low (~200 lines to change the data), which is fair, but the practical audience for proof-carrying metagame analytics remains unclear. Who rebuilds a 10-minute Lean build to check weekly metagame updates? The paper would benefit from a more concrete vision of the target user: is it tournament organizers? Game designers? Integrity auditors? Academic researchers?

#### Minor Issues

**M1.** The type-assignment methodology paragraph (§III-A) is good but could be stronger. The 83% alignment rate is computed over only 18 matchups (Dark→Psychic). What about other type interactions (e.g., Water→Fire, Fighting→Dark)? Is Dark→Psychic cherry-picked as the strongest alignment? If so, report the overall alignment across all type-advantage pairs.

**M2.** The replicator dynamics are single-step from the observed state. The preliminary directional check (§VII-A) honestly reports a failure (Grimmsnarl declining due to Absol rise). This is commendable honesty, but it also shows the predictive utility of the formalization is limited. Multi-step replicator simulation is listed as future work but would significantly strengthen the contribution.

**M3.** The Wilson interval discussion (§V-D) states intervals are "not propagated through the Nash equilibrium linear program." This is a real gap. Even a first-order sensitivity bound (how much does the game value change per percentage-point perturbation in a given cell?) would be valuable and potentially Lean-verifiable.

**M4.** Figure 3 (the directed interaction motif) is useful but should include edge directionality labels more clearly. Currently one must cross-reference Table III.

**M5.** The behavioral-economic interpretation (§VI-B) cites classic references but doesn't engage with TCG-specific literature on deck selection behavior. Is there any survey or empirical work on *why* players choose popular decks? Card availability, social pressure, content creator influence, and practice familiarity are all mentioned but not cited with TCG-specific evidence.

**M6.** Line count claims ("approximately 30,000 lines, 81 files, 2,500 theorems") should be exact if the artifact is static. "Approximately" is imprecise for a paper about precision.

---

## Questions for Authors

1. Have you tested whether the Nash equilibrium support changes if you use a different tie convention (e.g., T/2 instead of T/3)? This would strengthen the robustness claim.

2. The symmetric Nash (Table V) has 7-deck support vs. 6-deck asymmetric support. Is Gholdengo's appearance in the symmetric equilibrium (9.2%) but near-zero in the asymmetric row (0%) a consequence of the symmetrization, or does it reflect genuine sensitivity?

3. What is the build time breakdown? How much of the ~10 minutes is spent on the 244 `native_decide` calls vs. other proofs?

---

## Summary Assessment

v13 is a meaningfully improved paper. The Nash uniqueness qualification, numerical sufficiency renaming, and arrow-chain removal address my primary round-2 concerns. The paper now makes honest, well-scoped claims. The methodological contribution—demonstrating that proof-carrying analytics is feasible for empirical game ecosystems—is genuine and novel for this venue. The remaining concerns (two-player model adequacy for Swiss, `native_decide` concentration, external sensitivity analysis) are real but disclosed. The empirical content, while not itself novel, serves as an adequate demonstration vehicle.

I move from **Reject** (v12) to **Weak Accept** (v13), conditional on minor revisions addressing T1 (Swiss-pairing discussion) and M1 (type-alignment scope).
