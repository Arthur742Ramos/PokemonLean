# IEEE Transactions on Games — Submission #753 (v11)
## Reviewer 2: Detailed Review

**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game

**Reviewer expertise:** Empirical game theory, esports analytics, competitive strategy

**Date:** 2026-02-20

---

## Summary

This paper presents a formally verified metagame analysis of competitive Pokémon TCG using Lean 4 and real tournament data from Trainer Hill (Jan 29–Feb 19, 2026). The authors model 14 archetypes and their full pairwise matchup matrix, prove a "popularity paradox" (the most-played deck Dragapult has sub-50% expected win rate), compute and verify a Nash equilibrium that assigns Dragapult zero weight, run full 14-deck replicator dynamics, and connect these results to tournament-format considerations (Bo3, Swiss). The artifact is ~30,200 lines across 81 files with no `sorry` or `admit`. Version 11 adds `CausalChain.lean` (12 end-to-end theorems) and a marginal-cost defense for the LOC-to-insight ratio.

---

## Scores

### Novelty: 4/5

The core methodological contribution—applying proof-carrying verification to empirical metagame analytics—is genuinely novel. I am not aware of prior work that machine-checks Nash equilibrium certificates over real tournament data in any competitive game, let alone one with 14 strategies and a 196-cell matrix. The idea of treating metagame analysis as theorem proving over empirical constants is a creative synthesis of formal methods and esports analytics.

The novelty is tempered slightly by the fact that the underlying game-theoretic techniques (Nash equilibrium via LP, replicator dynamics, Bo3 amplification) are textbook material. The paper is transparent about this: the contribution is methodological, not analytical. The new `CausalChain.lean` module is an interesting attempt to demonstrate that the rules formalization is not merely decorative infrastructure, though I have reservations about whether "causal chain" is the right framing (see Technical Soundness).

### Technical Soundness: 3/5

This is the area where I have the most significant concerns, and they fall into several categories:

**A. The "causal" framing is overclaimed.**
The paper repeatedly uses language like "causal chain," "causal sufficiency," and "mechanistic explanation." However, what is actually verified is *correlational consistency*: given expert-assigned type labels, the type chart predicts matchup direction in 83% of cases. The paper acknowledges this in places ("correlational consistency check") but then immediately escalates to causal language in others (theorem name `dark_weakness_sufficient_for_suboptimality`, section heading "Causal sufficiency," the `CausalChain.lean` module).

The "causal sufficiency" argument (that Dark-type losses alone drag Dragapult below 50% even granting 50% against all non-Dark opponents) is a valid *algebraic sufficiency* result—it shows the Dark matchups are large enough in magnitude. But calling this "causal" conflates algebraic sufficiency in a model with causal identification in the scientific sense. The type assignments are modeling assumptions, not formally derived from deck composition. The paper should be more disciplined about this distinction throughout.

**B. The Nash equilibrium verification is sound but its interpretation requires caveats the paper undersells.**
The verification itself is clean: the LP solution is found externally and Lean independently checks all 14 best-response conditions for both players. This is the strongest part of the technical contribution.

However, several interpretive issues deserve more prominence:
1. *Uniqueness is not proven.* The paper notes this but does not emphasize that multiple equilibria could assign Dragapult positive weight. The sensitivity analysis (77.9% exclusion) is complementary but is Python-based and outside the trust boundary.
2. *The two-player symmetric game model is a simplification.* Real tournaments are multiplayer Swiss events. The paper acknowledges this ("modeling limitation") but then continues to draw strong conclusions from the two-player Nash model without adequately qualifying them.
3. *Top-14 normalization.* Excluding 30.5% of the field is a substantial modeling choice. The robustness analysis (Dragapult needs >57.6% vs. Other to reach 50%) is helpful but doesn't address whether the Nash equilibrium support itself is robust to including the "Other" segment.

**C. The `native_decide` trust boundary is correctly documented but is more consequential than typical.**
I appreciate the thorough discussion in Section IX, including the disclosure that `Fin.foldl` structurally precludes `decide`. The honest acknowledgment that 244 theorems share a single trust assumption (and that a compiler bug could invalidate all of them simultaneously) is commendable. However, this means the "formally verified" headline is qualified in a way that the abstract doesn't fully convey. The abstract says "formally verified (modulo the `native_decide` trust boundary discussed in Section IX)" which is accurate but could be more explicit about the scope.

**D. Replicator dynamics claims are appropriately scoped.**
The v11 paper correctly limits replicator claims to single-step directional pressure and proves algebraic step-size independence. The preliminary predictive check (2/3 confirmed, Grimmsnarl wrong due to multi-step cascade) is honest and informative. This is well-handled.

**E. Type assignments are expert modeling choices, not formally derived.**
`ArchetypeAnalysis.lean` assigns primary attack/defense types to archetypes manually. These are domain-expert judgments, not computed from deck lists or game semantics. If an archetype's "primary defense type" were assigned differently, the type-alignment statistics would change. The paper should state this limitation more prominently.

### Significance: 3/5

The methodological demonstration is significant for the formal methods and games research communities. Showing that proof-carrying analytics is feasible for a real game ecosystem with real data is valuable. The marginal-cost argument (updating requires ~200 lines in `RealMetagame.lean`) strengthens the practical case.

However, significance is limited by three factors:
1. *The specific analytical results (popularity paradox, Dragapult suboptimality) are not surprising to competitive players.* The paper acknowledges this but the gap between 30K lines of Lean and a spreadsheet delivering the same insights remains large. The cost-benefit table (Table VII) is helpful but doesn't fully address whether the verification catches errors that matter in practice beyond the matrix data-entry example.
2. *Generalizability is asserted but not demonstrated.* The paper claims portability to "any domain with discrete strategies and measurable outcomes" but provides no second domain. A brief extension to even a toy example from another game would strengthen this claim considerably.
3. *The behavioral-economic interpretation (Section V-C) is appropriately hedged as hypothetical but adds little.* Citing Kahneman, Tversky, and herding literature without any player-level data to test these mechanisms is window dressing. The paper would be tighter without it, or with it explicitly marked as pure speculation.

### Clarity: 4/5

The paper is well-structured and clearly written for its target audience. The progression from rules → data → paradox → Nash → dynamics → tournament is logical. Tables and figures are effective—Figure 1 (scatter plot) and Figure 2 (interaction motif) are clean visualizations.

Minor clarity issues:
- The `GrimssnarlFroslass` typo in the Lean source is a small but distracting blemish. A rename in the artifact (even if breaking) would be cleaner than the footnote.
- The paper oscillates between "causal" and "correlational" language in a way that could confuse readers about what is actually proven. A consistent terminology would help.
- Section IX (Methodology) is long and could be tightened. The case study (Section IX-G) is nice but could be a sidebar or appendix.
- The tie convention ($T/3$) is mentioned in several places; consolidating the discussion would reduce redundancy.
- The v11 additions (CausalChain.lean, LOC defense) are well-integrated and don't feel bolted on.

### Reproducibility: 5/5

This is the paper's strongest dimension and where the formal verification methodology pays clear dividends.

- The artifact is self-contained: `lake build` reportedly verifies all claims in ~10 minutes.
- No `sorry`, no `admit`, no custom axioms—a clean zero-axiom standard.
- Data provenance is documented (Trainer Hill, date range, inclusion criteria).
- The `MatrixConsistency.lean` cross-check between array-based and function-based representations is a nice touch that eliminates a common source of errors in verified artifacts.
- The one-to-one mapping between paper claims and named theorems makes auditing straightforward.
- The Python sensitivity analysis is appropriately flagged as external to the trust boundary.

The only reproducibility concern is that Trainer Hill data may not be permanently archived. A persistent snapshot (e.g., Zenodo DOI) of the raw data would future-proof the artifact.

---

## Detailed Comments

### Major Issues

1. **Tighten the causal language.** Replace "causal chain," "causal sufficiency," and "mechanistic explanation" with more precise language throughout. Suggestions: "algebraic sufficiency," "structural consistency," "end-to-end integration." The `CausalChain.lean` module name is fine as an internal label but the paper's framing should not imply causal identification in the econometric sense. This is the single revision most likely to prevent rejection from a methodologically careful referee.

2. **Acknowledge the gap between verified equilibrium properties and strategic prescriptions more explicitly.** The paper proves that *one particular* Nash equilibrium assigns Dragapult zero weight. Without uniqueness, this is weaker than "Dragapult should never be played." The sensitivity analysis helps but is unverified. A paragraph explicitly stating what the Nash result does and does not imply for competitive decision-making would strengthen the paper.

3. **The type assignment methodology needs its own subsection or at least a prominent paragraph.** How were primary attack/defense types assigned? Are they unambiguous? What about multi-type decks (Dragapult Charizard)? What happens to the 83% alignment if borderline assignments are changed? This is currently buried and deserves explicit treatment as a modeling assumption.

### Minor Issues

4. The Wilson interval discussion (Section V-D) is good but the propagation gap (intervals not propagated through Nash) should be mentioned earlier, not as an afterthought. Consider moving it to immediately follow the interval computation.

5. Table I (matchup matrix) shows only top-6. The full 14×14 matrix should be in the appendix/supplement, which it apparently is in `RealMetagame.lean`, but an explicit reference would help.

6. The "preliminary directional check" (Section VII-A) against one day of post-window data is interesting but statistically meaningless. Either expand this to a proper out-of-sample validation or downgrade it to a footnote. As currently presented, it occupies too much space for one data point.

7. In `CausalChain.lean`, Chain 2 (weakness doubles damage, saves a turn of tempo) proves `2 - 1 = 1` as a conjunct. This is trivially true and adds no information. Several chains in this module mix genuinely interesting cross-module bridges with trivial arithmetic in a way that dilutes the impact.

8. The `CausalChain.lean` "grand causal chain" (theorem `the_complete_story`) is impressive as a proof artifact but the paper should note that it is a conjunction of independently checkable facts, not a single logical derivation. The conjunctive structure means each conjunct is separately necessary; the theorem doesn't establish that the conjunction is *jointly* stronger than its parts.

9. Bo3 amplification is verified on a grid of rational values (51%–99%) rather than symbolically for all p ∈ (0.5, 1). This is fine for the concrete matchups used but the paper should note this is gridded verification, not a universal proof.

10. The expected Swiss matchups calculation (`expectedSwissMatchupsIn8`) appears in `CausalChain.lean` without clear derivation in the paper body. Either derive it or reference where it comes from.

---

## Questions for Authors

1. Have you attempted to verify uniqueness of the Nash equilibrium (even on a coarse grid, as done for the 3×3 RPS case)?
2. Could the type assignments be derived computationally from deck lists (e.g., most common attack type by damage output) rather than assigned by expert judgment?
3. What is the actual build time on the reported hardware? The ~10 min claim should be verified and reported precisely.
4. Is there a plan to archive the Trainer Hill snapshot with a persistent identifier?

---

## Overall Recommendation: **Weak Accept**

This paper makes a genuine methodological contribution by demonstrating that proof-carrying metagame analytics is feasible over real tournament data. The artifact quality is high, the reproducibility is exemplary, and the game-theoretic analysis—while using standard techniques—is competently executed and honestly scoped.

The main weaknesses are (1) overclaimed causal language that exceeds what the formal proofs actually establish, (2) interpretive gaps around Nash uniqueness and the two-player modeling simplification, and (3) the LOC-to-insight ratio that remains hard to justify despite the marginal-cost argument. The `CausalChain.lean` addition in v11 is a step in the right direction for connecting the rules infrastructure to strategic conclusions, but the "causal" framing needs to be revised to match what is actually proven.

If the authors tighten the causal language, add explicit discussion of type assignment methodology, and acknowledge the equilibrium interpretation limitations more prominently, the paper would be suitable for publication. The formal verification infrastructure and zero-sorry artifact represent real engineering achievement, and the template is portable to other competitive game domains.

**Overall Score: 3.5/5 (Weak Accept, conditional on revisions)**

---

*Reviewer 2, IEEE Transactions on Games*
*Expertise: Empirical game theory, esports analytics, competitive strategy*
*Confidence: High*
