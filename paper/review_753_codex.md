# Review — Submission #753

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"  
**Venue:** IEEE Transactions on Games  
**Reviewer Confidence:** High (expertise in formal methods, game theory, and competitive game analysis)

---

## 1. Summary

This paper presents a formally verified metagame analysis of the competitive Pokémon TCG using Lean 4 and real tournament data from Trainer Hill (January–February 2026). The authors encode a 14×14 archetype matchup matrix, prove a "popularity paradox" (the most-played deck, Dragapult at 15.5% share, has only 46.7% expected win rate), compute and machine-check a Nash equilibrium with six-deck support that assigns Dragapult 0% weight, and run full 14-deck replicator dynamics over the complete matchup matrix. The artifact comprises ~30K lines of Lean 4 across 80 files with 2,500+ theorems, zero `sorry`/`admit`/custom axioms, and builds in ~10 minutes.

---

## 2. Strengths

1. **Methodological novelty.** To my knowledge, this is the first formally verified metagame analysis of any competitive game with real tournament data. The idea of "proof-carrying analytics" — where every strategic claim is a machine-checkable theorem — is a genuine contribution to game science methodology that is portable beyond TCGs.

2. **Artifact quality and scale.** The Lean artifact is substantial (80 files, ~30K lines, 2,500+ theorems, zero sorry). I verified that `sorry` and `admit` do not appear in proof-bearing positions. The modular architecture (rules → probability → data → equilibrium → dynamics) is clean and well-factored. The claim of a ~10 minute build is credible given the module structure.

3. **Complete equilibrium certification.** The Nash equilibrium is certified by checking best-response conditions for all 14 pure strategies for both players — a 196-cell verification that would be error-prone by hand. The inclusion of both the bimatrix equilibrium and the symmetrized constant-sum formulation (with verified game value = 500) is thorough and addresses the natural concern about tie-induced asymmetry.

4. **Full 14-deck replicator dynamics.** Unlike earlier drafts that might have used toy 3-archetype models, the evolutionary dynamics theorems operate over the complete 14-deck game and observed share vector, making the directional predictions (Dragapult decline, Grimmsnarl dominance, Alakazam extinction) directly empirically relevant.

5. **Honest uncertainty quantification.** The 10,000-iteration sensitivity analysis, Wilson confidence intervals, and explicit acknowledgment that the exact Nash support is fragile (recovered in only 2.1% of resampled equilibria) while core support decks appear in >96% of iterations is a mature treatment of robustness. The clear labeling of sensitivity ranges as "not frequentist confidence intervals" is commendable.

6. **Transparent trust boundary.** The paper explicitly discusses the `native_decide` trust boundary and correctly explains why `decide` is structurally precluded (Lean 4's kernel reducer cannot handle opaque `Fin.foldl`). The data provenance section cleanly separates computational correctness guarantees from empirical data trustworthiness.

7. **Strong related work coverage.** The paper positions itself well against both formal methods literature (Gonthier, mathlib, Kepler) and game AI literature (Cepheus, Libratus, AlphaStar), correctly identifying the orthogonal contribution of metagame-level analysis versus in-game decision quality.

8. **Predictive validation attempt.** The comparison against post-window trend data, including the honest report that Grimmsnarl declined (contradicting the single-step prediction due to Mega Absol's rise), shows scientific integrity and motivates iterated dynamics as future work.

---

## 3. Weaknesses

### Critical

None identified. The core claims are machine-checked and the methodology is sound.

### Major

**M1. Gap between rules formalization and empirical analysis.** The paper presents 15 files of rules formalization (game state, deck legality, card effects, type effectiveness) but these are largely disconnected from the empirical metagame analysis, which operates entirely at the matrix level. The paper acknowledges this ("the rules layer is supporting infrastructure rather than the primary empirical claim") but the rules formalization still occupies significant page space (Section III, parts of Section IV) without contributing to the headline results. The connection via `checkDeckLegal_iff` ensuring only legal configurations enter the analysis is stated but not demonstrated in the paper. *Recommendation:* Either tighten the narrative to make the rules→matrix connection more concrete (e.g., show how a type-effectiveness theorem constrains a specific matchup entry) or compress Sections III–IV to make room for deeper equilibrium analysis.

**M2. Single-step replicator limitation acknowledged but not addressed.** The predictive validation reveals that single-step replicator dynamics miss multi-step cascades (Mega Absol rising → Grimmsnarl declining). This is a fundamental limitation for the paper's practical claims about metagame prediction. The iterated replicator simulation (`replicatorIter` is defined in the artifact) could be run for multiple steps to produce trajectory predictions, but this analysis is absent from the paper. Even a 5-step or 10-step simulation with the existing Lean infrastructure would significantly strengthen the dynamics claims.

**M3. "Other" segment treatment.** The 30.5% unmodeled field is a substantial fraction. While the worst-case robustness bounds are verified, the paper never attempts to model this segment even coarsely (e.g., as a uniform 50% matchup baseline or using aggregate win rates). This is a missed opportunity: even a 15×15 matrix with an "Other" row/column using aggregate data would be more defensible than complete exclusion, and the Lean infrastructure could clearly handle it.

### Minor

**m1. Figure quality.** Figure 1 uses a LaTeX `picture` environment with manual coordinate placement. The paper itself contains a TODO comment ("Replace picture environment with TikZ/pgfplots for camera-ready"). This is below publication standard for IEEE Transactions on Games. The scatter plot needs proper axes, gridlines, and all 14 data points — not just 6.

**m2. Footnote inside listing.** The footnote about `GrimssnarlFroslass` spelling (footnote 1) appears inside a code listing, which is typographically awkward and may render incorrectly depending on the LaTeX toolchain. The typo in the Lean identifier itself (`Grimssnarl` vs `Grimmsnarl`) is a minor artifact quality issue — a simple rename would fix both the identifier and the footnote.

**m3. Nash equilibrium uniqueness.** The paper proves *existence* of a Nash equilibrium with the stated support but does not discuss uniqueness. For a non-degenerate bimatrix game of this size, uniqueness is unlikely, and multiple equilibria with different support sets would weaken some claims. The sensitivity analysis partially addresses this (different resampled matrices yield different supports), but a direct discussion of multiplicity for the point-estimate matrix would be valuable.

**m4. Bo3 independence assumption.** The paper correctly notes that the Pokémon TCG lacks sideboarding, making Bo3 independence "substantially more defensible." However, information revelation (seeing the opponent's deck in game 1) is a non-trivial dependency that could shift Bo3 win probabilities by 1–3 percentage points for decks with surprise-dependent strategies. This deserves slightly more discussion.

**m5. Continuous monitoring claim.** Section VIII-G claims the infrastructure "naturally supports continuous operation" with weekly updates. This is plausible but undemonstrated — the paper covers exactly one 3-week snapshot. A brief discussion of what would need to change (data ingestion pipeline, constant updates, re-verification time) would substantiate this claim.

**m6. Page budget.** At approximately 12 pages of content (before references), the paper is dense. The methodology section (Section VIII) is thorough but could be compressed — the "Case Study: Verifying a Headline Claim End-to-End" subsection, while pedagogically useful, largely restates what is already clear from the paper structure.

### Typographic

**t1.** The Lean listing for `dragapult_popularity_paradox` uses `\footnote` inside `lstlisting`, which is non-standard.

**t2.** "GrimssnarlFroslass" — identifier typo noted by the authors but should be fixed in the artifact before final publication.

**t3.** The `optimize_proof` macro expanding to `native_decide` should be documented more prominently, perhaps in a one-line comment in the first listing where it appears rather than only in prose below.

**t4.** Table V caption says "Formalization Module Breakdown" — consider a more descriptive caption like "Lean artifact module statistics."

---

## 4. Questions for Authors

**Q1.** Have you attempted to run `lake build` with `decide` replacing `native_decide` for even a single key theorem (e.g., the popularity paradox) to confirm the `Fin.foldl` opacity claim? If so, what is the exact error message?

**Q2.** The sensitivity analysis uses Python to solve LPs over resampled matrices. Did you compare the Python-computed Nash equilibrium against the Lean-verified one for the point-estimate matrix to validate consistency between the two solvers?

**Q3.** The symmetrized Nash equilibrium has 7-deck support while the bimatrix one has 6-deck support per player. Is Alakazam's inclusion in the symmetrized equilibrium (2.5% weight) but exclusion from the column player's bimatrix support a consequence of the symmetrization, or does it reflect a genuine strategic difference?

**Q4.** The replicator dynamics predict Grimmsnarl as the fittest archetype, yet the post-window data show Grimmsnarl declining. Have you run multi-step replicator iterations to see whether the model eventually predicts Grimmsnarl's decline via the Mega Absol cascade?

**Q5.** What is the actual build time on the hardware described (Apple M-series, 16 GB RAM)? Does this include `native_decide` compilation time?

---

## 5. Overall Assessment

This paper makes a genuine methodological contribution: it demonstrates that formal verification can serve as practical scientific infrastructure for competitive game analysis. The artifact is impressive in scale and rigor, and the core claims (popularity paradox, Nash equilibrium, replicator dynamics) are machine-checked. The paper is well-written, honest about limitations, and properly contextualized in the literature.

The main weaknesses are: (1) the rules formalization is largely disconnected from the empirical analysis, consuming page space without contributing to headline results; (2) the replicator dynamics are limited to single-step predictions that the paper's own validation shows are insufficient; and (3) the 30.5% unmodeled field segment is a significant gap that could be partially addressed with existing infrastructure.

These weaknesses are addressable in revision and do not undermine the core contribution. The paper would benefit from compressing the rules sections, adding multi-step replicator trajectories, fixing Figure 1, and incorporating an "Other" segment in the matrix.

---

## 6. Overall Recommendation

**Weak Accept**

The methodological contribution is novel and well-executed. The artifact quality is exceptional for a games paper. The empirical analysis, while temporally limited, is honest and thorough. The weaknesses are real but correctable. With the revisions suggested above — particularly improving Figure 1, adding multi-step dynamics, and tightening the rules↔analysis narrative — this would be a solid Accept. In its current form, the contribution is above the acceptance threshold but would benefit from one more revision pass.

**Severity Summary:**  
- Critical: 0  
- Major: 3 (M1–M3)  
- Minor: 6 (m1–m6)  
- Typographic: 4 (t1–t4)
