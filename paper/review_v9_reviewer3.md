# IEEE Transactions on Games — Review of Submission #753 (v9)

**Reviewer 3: Empirical Game Theory / Esports Analytics**
**Date:** 2026-02-20

---

## Summary

This paper presents a formally verified metagame analysis of competitive Pokémon TCG using Lean 4, built atop Trainer Hill tournament data (Jan 29–Feb 19, 2026). The core empirical finding is a "popularity paradox": Dragapult Dusknoir, the most-played deck at 15.5% share, has only 46.7% expected win rate, while Grimmsnarl Froslass (5.1% share) achieves 52.7%. A machine-checked Nash equilibrium assigns Dragapult 0% weight. Replicator dynamics over the full 14-deck game predict directional meta shifts. The artifact is ~30K lines of Lean with ~2,500 theorems and no `sorry`.

V9 adds: (1) abstract caveat on the `native_decide` trust boundary, (2) contextualized skill thresholds against empirical 2–5pp range, (3) explicit "unverified Python" note on the sensitivity table, (4) symbolic step-size invariance proof, (5) tightened equilibrium multiplicity argument.

---

## Scores

| Criterion        | Score | Comments |
|------------------|:-----:|---------|
| **Novelty**       | 4/5  | First proof-carrying metagame analysis pipeline for a real competitive game. The idea of coupling formal verification to empirical game-theoretic claims is genuinely new. Not 5/5 because the underlying game theory (Nash, replicator dynamics) is textbook. |
| **Technical**      | 4/5  | The Lean artifact is impressively rigorous. The `native_decide` trust boundary is now properly disclosed. The symbolic step-size proof (StepSizeGeneral.lean) is a real upgrade over v8's concrete-only verification. Matrix consistency cross-check (MatrixConsistency.lean) eliminates a real class of errors. Deducted for the unverified sensitivity analysis and the structural limitation of `Fin.foldl` blocking kernel-checked proofs. |
| **Significance**   | 3/5  | The methodological template is valuable but the practical impact is unclear. The popularity paradox itself could be (and regularly is) demonstrated with a spreadsheet. The paper is candid about this, but the 30K-line overhead vs. 100 lines of Python remains a hard sell for the esports analytics community. Significance would increase with demonstrated portability to another game or a rolling-window deployment. |
| **Clarity**        | 4/5  | Well-structured, honest about limitations. The verified/unverified seam is now transparent (see below). Some notation inconsistency remains (e.g., `GrimssnarlFroslass` typo acknowledged in footnote but distracting). The paper is dense at 12 pages—Section IV (probability) and parts of Section III (rules) could be compressed to make room for deeper discussion of the sensitivity analysis methodology. |
| **Reproducibility** | 5/5  | Exemplary. `lake build` reproduces all verified claims. Data provenance is clearly stated. The Python sensitivity script is included. MatrixConsistency.lean eliminates cross-module data drift. This is the gold standard for reproducibility in this subfield. |

---

## Detailed Assessment

### A. Skill-Gap Contextualizations (v9 addition)

The contextualization of the 3.4pp and 6.1pp skill thresholds against the "empirical 2–5pp range" (Section X, Threats to Validity) is a meaningful improvement. The argument that the break-even threshold "falls at the upper end of this range" while the Grimmsnarl-matching threshold "exceeds plausible within-event confounding entirely" is directionally convincing.

However, I have reservations:

1. **Source of the 2–5pp benchmark.** The paper cites no source for the "2–5 percentage points between top-quartile and bottom-quartile finishers" claim. This is a critical number that anchors the entire skill-confounding argument. Is this from Pokémon TCG specifically? From general TCG literature? From esports broadly? The lack of citation makes this the weakest link in an otherwise well-sourced paper. If this number comes from the authors' domain knowledge rather than a published study, it should be labeled as such.

2. **Uniform bias model is conservative but potentially misleading.** The SkillSensitivity.lean proof assumes a *uniform* bias across all 13 non-mirror matchups. In reality, skill confounding would be heterogeneous—weaker pilots might lose disproportionately in complex matchups (e.g., vs. Gardevoir) while performing closer to deck-strength in straightforward ones (e.g., vs. Charizard). A matchup-specific sensitivity analysis, even unverified, would be more convincing.

3. **The 3.4pp threshold is not as reassuring as presented.** The paper says this "falls at the upper end" of the 2–5pp range. But 3.4pp is below the midpoint of 2–5pp. If anything, this suggests the paradox *could* be substantially explained by skill confounding under moderate assumptions. The rhetorical framing slightly oversells the robustness.

### B. Verified/Unverified Seam Transparency (v9 addition)

V9 substantially improves the seam disclosure. Specific improvements I note:

- The abstract now includes "modulo the `native_decide` trust boundary discussed in Section IX."
- Table II caption explicitly states "produced by an external Python script; these results complement but do not inherit the formal guarantees of the Lean artifact."
- Section IX-C provides a thorough `native_decide` discussion including the structural reason `decide` fails (`Fin.foldl` opacity) and the concentration risk (244 theorems share one trust assumption).
- The repeated caveat on the sensitivity table is appropriate.

**This seam is now transparent.** A reader can clearly distinguish what is machine-checked, what trusts `native_decide`, and what is Python-only. This was my primary concern in previous rounds and it is resolved.

One remaining subtlety: the equilibrium multiplicity argument now combines verified evidence (Dragapult gets 0% in both asymmetric and symmetric equilibria, is strictly suboptimal against the Nash column mix) with unverified evidence (77.9% exclusion across 10,000 resampled matrices). The text handles this carefully ("provides strong empirical evidence") but the interleaving of verified and unverified claims in the same paragraph could be made even crisper with explicit labels.

### C. Symbolic Step-Size Proof (v9 addition)

StepSizeGeneral.lean is a clean, well-structured proof. The key theorem `replicator_sign_independent_of_dt` is proved by elementary sign reasoning over integers—no `native_decide` needed. This is exactly the kind of proof that *should* be symbolic rather than computational, and it eliminates a legitimate concern about whether the 5-grower/9-shrinker classification was an artifact of the chosen dt. Good addition.

### D. Equilibrium Multiplicity Argument (v9 addition)

The tightened argument is improved but still has a logical gap. The paper proves:
1. Dragapult gets 0% in the asymmetric row strategy ✓
2. Dragapult gets 0% in the asymmetric column strategy ✓
3. Dragapult gets 0% in the symmetric Nash equilibrium ✓
4. Dragapult is strictly suboptimal against the verified Nash column mix ✓

Point (4) is the strongest: it means Dragapult cannot appear in *any* best response to *this particular* column strategy. But the paper correctly notes this "does not logically preclude Dragapult from equilibria with different column strategies." The sensitivity analysis (77.9% exclusion) fills this gap empirically but not formally.

For a paper whose methodological contribution is formal verification, this is a notable gap. I don't think it's fatal—the combined evidence is genuinely compelling—but the paper should be explicit that the "Dragapult is excluded from all equilibria" claim remains a conjecture, not a theorem.

### E. Broader Technical Observations

- **Replicator dynamics as single-step diagnostics.** The paper is appropriately cautious that verified results are single-step directional claims, not convergence guarantees. The predictive validation (Section VII-A) where Grimmsnarl *declined* despite highest fitness—due to multi-step cascade effects—is an honest and valuable inclusion.

- **The type-alignment bridge (Section III-A).** The 83% alignment rate (13/15 Dark→Psychic pairs) with binomial p < 0.001 is a nice quantitative check. However, the two exceptions (N's Zoroark) are not deeply analyzed. What specific card interactions override type advantage? This would strengthen the "rules as falsifiable predictions" argument.

- **Sample size heterogeneity.** The paper acknowledges wide variation (2,845 games for Dragapult mirror vs. ~100 for Ceruledge vs. N's Zoroark) but doesn't systematically flag which claims rest on thin data. The Wilson intervals help, but a heat map of sample sizes alongside the matchup matrix would be informative.

---

## Recommendation: **Weak Accept**

The paper presents a genuinely novel methodological contribution—proof-carrying metagame analytics—executed with impressive rigor and transparency. V9 addresses the major concerns from prior rounds: the trust boundary is disclosed, the skill thresholds are contextualized, and the verified/unverified seam is clear. The symbolic step-size proof and matrix consistency check are meaningful technical additions.

The paper is not yet a clean accept because: (1) the skill-gap contextualization relies on an unsourced benchmark, (2) the significance for the broader community remains somewhat narrow without portability demonstration, and (3) the equilibrium multiplicity claim mixes verified and unverified evidence in a way that slightly undermines the paper's own methodological standard.

---

## 3 Must-Do Revisions

1. **Cite or qualify the 2–5pp skill differential benchmark.** The claim that "within-tournament skill differentials in competitive TCGs typically range from 2–5 percentage points" (Section X) is currently unsourced and anchors the entire skill-confounding robustness argument. Either (a) cite a published study of within-tournament skill effects in TCGs or esports, (b) derive the range from the Trainer Hill data itself (e.g., comparing top-cut vs. non-top-cut matchup WRs for the same archetype), or (c) explicitly label it as an author estimate and weaken the rhetorical framing accordingly. As-is, it reads as an empirical fact but may be an assumption.

2. **Separate verified and unverified evidence in the equilibrium multiplicity argument.** In Section VII, the argument that "Dragapult's exclusion is not an artifact of equilibrium selection" interleaves four formally verified facts with one unverified Python result (77.9% exclusion rate) in a single paragraph. Restructure into two clearly labeled sub-arguments: (a) "Formally verified: Dragapult receives 0% weight in all three computed equilibria and is strictly suboptimal against the Nash column mix" and (b) "Complementary unverified evidence: sensitivity analysis shows 77.9% exclusion across resampled matrices." This separation is consistent with the paper's own methodological standard and would strengthen, not weaken, the argument.

3. **Add a sample-size qualifier to thin-data matchup claims.** Several matchup-dependent claims (e.g., Ceruledge vs. N's Zoroark at 70.9%, used in EvolutionaryDynamics.lean) rest on approximately 100 games with Wilson intervals of ±9pp. Add a brief discussion or table footnote identifying which matchup cells have <200 games and noting that the replicator classification could be affected if these cells shifted within their confidence intervals. The 10,000-iteration sensitivity analysis partially addresses this, but the connection between thin-data cells and sensitivity results should be made explicit.

---

## 3 Questions for the Authors

1. **Portability test.** You position the pipeline as a "general template" (Section XI). Have you attempted even a minimal instantiation on a second game (e.g., a 3×3 subgame from Magic: The Gathering or a fighting game matchup chart)? Even a negative result ("we attempted X and found Y was the bottleneck") would calibrate the portability claim.

2. **Temporal falsification.** Your predictive validation (Section VII-A) covers one day post-window. The data window closed February 19; it is now February 20. Do you plan to report a structured out-of-sample evaluation over the subsequent 2–4 weeks? The Grimmsnarl counter-prediction (declined despite highest fitness) is the most interesting finding in the paper and deserves systematic follow-up.

3. **Player-level data feasibility.** You note that disentangling deck strength from pilot strength requires "player-level covariates not available in the Trainer Hill dataset." Is this a fundamental limitation of the data source, or could player IDs + ELO ratings from Limitless be integrated? If feasible, this would transform the skill-confounding threat from a sensitivity bound into an empirical measurement, which would substantially increase the paper's significance.

---

*Reviewer 3 — Empirical Game Theory / Esports Analytics*
*IEEE Transactions on Games, Submission #753, Version 9*
