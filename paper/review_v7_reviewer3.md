# IEEE Transactions on Games — Reviewer Report

**Submission #753 (v7):** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Reviewer 3 — Empirical Game Theory / Esports Analytics Specialist**

---

## Summary

This paper presents a formally verified metagame analysis of the competitive Pokémon TCG, using Lean 4 to machine-check strategic claims over real tournament data from Trainer Hill (Jan 29–Feb 19, 2026). The core finding is a "popularity paradox": the most-played deck (Dragapult, 15.5% share) has a sub-50% expected field win rate (46.7%), while a less-played deck (Grimmsnarl, 5.1%) achieves the highest expected win rate (52.7%). The paper then derives a machine-checked Nash equilibrium (six-deck support, 0% Dragapult weight), replicator dynamics predictions over all 14 archetypes, and a type-effectiveness bridge linking formalized game rules to empirical matchup outcomes. The artifact spans ~30,000 lines of Lean 4 with no `sorry`, `admit`, or custom axioms.

Version 7 improves on v6 with tighter page count (14→12), machine-checked skill-sensitivity bounds, step-size invariance proofs for replicator dynamics, and transparent `native_decide` disclosure.

---

## Scores

| Criterion        | Score | Comment |
|------------------|:-----:|---------|
| **Novelty**          | 4/5 | The proof-carrying metagame analytics pipeline is genuinely new. No prior work formally verifies equilibrium and dynamics claims over real competitive game data at this scale. |
| **Technical Soundness** | 4/5 | The verified components are sound modulo `native_decide`. The empirical methodology is competent but has identifiable gaps (see below). |
| **Significance**     | 3/5 | Methodologically significant as a proof-of-concept. Practical impact on competitive play is limited by temporal locality and the static-matrix assumption. |
| **Clarity**          | 4/5 | Well-written for a technically dense paper. The tightening from 14 to 12 pages is effective; the paper reads more crisply than prior versions. |
| **Reproducibility**  | 5/5 | Exceptional. Full Lean artifact, `lake build` instructions, Python sensitivity scripts. The strongest aspect of the submission. |

---

## Detailed Assessment

### 1. Empirical Methodology

**Data window and sample sizes.** The 22-day window (Jan 29–Feb 19, 2026) with a 50+ player tournament filter is a reasonable snapshot, but the paper should be more explicit about how many tournaments this represents and the total number of games in the matrix. The largest matchup pair (Dragapult mirror, 2,845 games) is well-powered, but the tail matchups (e.g., Ceruledge vs. N's Zoroark at ~100 games) have Wilson intervals of ±9 percentage points — wide enough that the sign of the matchup advantage could flip. The paper acknowledges this but does not systematically characterize which cells in the 14×14 matrix fall below a reliability threshold. With 196 cells, some are inevitably thin.

**Normalization over top-14.** The decision to normalize over the 69.5% top-14 subfield is the single largest unverified modeling choice. The remaining 30.5% is a large residual. The worst-case bounds in Section X (Dragapult needs 57.6% vs. Other to reach 50%) are helpful but assume uniform confounding across the entire Other category — in reality, Other is heterogeneous and could contain specific Dragapult-favorable archetypes. The share-perturbation robustness is well done (paradox persists when shares are swapped), but this does not address the missing-mass problem. The paper would benefit from a sensitivity analysis that models Other as a mixture of the known 14 archetypes with random weights, rather than a single block.

**Tie convention.** The $T/3$ weighting is an inherited convention from Trainer Hill. The paper correctly notes this but never quantifies its impact. Since mirror matches systematically show sub-50% WR (48.0–49.5%) due to tie drag, and these mirrors disproportionately affect popular decks, there is a subtle bias: popular decks accumulate more mirror matches, which deflate their average WR. This is a small effect but worth quantifying, especially since the popularity paradox gap (46.7% vs. 52.7%) is only 6 percentage points.

### 2. Skill-Sensitivity Bounds

The `SkillSensitivity.lean` file is a welcome addition and directly addresses the most important confound. The finding that Dragapult needs a ≥3.4pp uniform boost across all matchups to reach 50%, and ≥6.1pp to match Grimmsnarl, is a clean, interpretable result. However, the **uniform bias model is overly restrictive**:

- In practice, skill confounding is unlikely to be uniform. Weaker pilots may perform disproportionately worse in complex matchups (e.g., Gardevoir vs. Dragapult requires intricate resource management) while performing close to baseline in simple ones (e.g., aggressive mirrors). A non-uniform bias model — even a simple two-tier version (easy vs. hard matchups) — would strengthen the claim considerably.
- The 3.4pp threshold is smaller than it appears. In competitive TCGs, a 3–4pp skill gap between the average pilot of a popular accessible deck and the average pilot of a niche specialist deck is entirely plausible. The paper should engage more seriously with the empirical literature on skill effects in competitive games (e.g., Elo-stratified matchup analysis in chess/poker) to contextualize whether 3.4pp is large or small.

That said, the tight machine-checked bounds (33 < threshold ≤ 34 in per-mille units) are methodologically elegant and represent exactly the kind of result that formal verification enables more naturally than ad hoc scripting.

### 3. Step-Size Invariance

The `StepSizeInvariance.lean` proofs confirming identical 5-grower/9-shrinker classification across dt=1/100, 1/10, and 1 are correct and expected — the sign of $x_i(f_i - \bar{f})$ is independent of dt by construction. This is algebraically trivial but verification-relevant, since it confirms the implementation does not introduce numerical artifacts. I would prefer the paper state this more concisely: the invariance is a structural property of the discrete replicator equation, not an empirical finding.

### 4. Bridge Between Rules and Empirical Data

The type-effectiveness bridge (Section III-A, `ArchetypeAnalysis.lean`) is one of the more interesting contributions but warrants careful scrutiny:

**Strengths:**
- The 83% alignment rate (15/18 type-advantaged matchups correctly predicted) is a nontrivial correlational finding. The binomial null ($p < 0.001$) is correctly computed.
- The counterexamples (N's Zoroark losing despite Dark-type advantage) are honestly documented and mechanistically explained.
- The chain rules → type assignments → empirical confirmation → weighted drag is clearly articulated.

**Weaknesses:**
- The type assignments are **domain-expert modeling choices**, not formally derived from deck composition. If the authors had assigned types differently (e.g., Dragapult Charizard as Fire-defending instead of Psychic-defending), the alignment statistics would change. The paper acknowledges this ("modeling assumptions, not formally derived") but does not perform sensitivity analysis on the type assignments themselves.
- The alignment test has a selection effect: the authors chose to analyze type interactions where they expected alignment (Dark→Psychic, Fire→Steel). A more rigorous test would enumerate all possible type interactions in the 14-archetype matrix and report the full confusion matrix.
- The 83% figure counts matchup pairs equally regardless of sample size. A weighted analysis (by game count) might yield different results.

### 5. Practical Relevance to the Competitive Gaming Community

The paper's honest framing — "the primary contribution is methodological rather than competitive-tactical" — is appropriate. The specific metagame findings (Dragapult overplayed, Grimmsnarl underplayed) would be actionable if delivered within the data window, but a 22-day analysis published months later in an academic venue has zero competitive utility.

However, the **pipeline** has real potential value. If the artifact could ingest rolling weekly data and output verified equilibrium reports, competitive teams would have a genuine tool. The paper should be more concrete about this pathway: what is the wall-clock time for re-verification with a new matchup matrix? (~10 minutes on Apple M-series is stated for full build; what about incremental updates?)

The predictive validation (Section VII-A) — 2 of 3 directional predictions confirmed, with the Grimmsnarl miss explained by second-order dynamics — is admirably honest. The single post-window datapoint is insufficient for calibration, but the framework for systematic forecast scoring is clearly laid out.

### 6. `native_decide` Trust Boundary

The disclosure in v7 is substantially improved. The structural explanation (Fin.foldl opacity to kernel reduction) is technically accurate and exonerates the authors from a lazy shortcut accusation. The risk concentration (244 theorems sharing a single trust path) is correctly identified. I am satisfied that the trust boundary is appropriate for the claims made, but the paper should explicitly note that the game-theoretic core (Nash verification, replicator dynamics) is *entirely* within this boundary — there is no verified fallback for any headline result.

---

## Overall Recommendation

### **Weak Accept**

This is a well-executed proof-of-concept that demonstrates formal verification can be applied to empirical game-theoretic analysis of real competitive games. The artifact quality is exceptional. The empirical methodology is competent but has identifiable gaps (top-14 normalization, uniform skill-bias model, thin tail matchups). The v7 improvements (skill sensitivity, step-size invariance, `native_decide` disclosure) directly address prior reviewer concerns and are substantive. The paper is at the quality boundary for acceptance; the revisions below would push it over.

---

## Must-Do Revisions

1. **Characterize matchup cell reliability systematically.** Report the number of games underlying each cell of the 14×14 matrix (at minimum, provide the distribution: median, 25th percentile, minimum). Identify which cells fall below a defensible reliability threshold (e.g., <200 games, where Wilson intervals exceed ±5pp) and discuss how the Nash equilibrium and replicator results change if those cells are excluded or treated as uncertain. The current presentation gives the reader no way to assess whether the equilibrium support is driven by well-estimated or poorly-estimated cells.

2. **Relax the uniform skill-bias assumption.** The current SkillSensitivity analysis assumes a single constant bias across all 13 non-mirror matchups. Add a non-uniform sensitivity analysis — even a simple worst-case version: "What is the minimum bias needed in the k most favorable matchups alone to reverse the paradox?" This would address whether a plausible pattern of skill confounding (e.g., Dragapult pilots underperforming specifically against complex control decks) could explain the gap. The formal verification machinery is well-suited to this kind of parameterized bound.

3. **Quantify the mirror-match/tie bias on popular decks.** Since the $T/3$ convention deflates mirror-match WR below 50%, and popular decks play more mirrors (which are counted in the expected WR computation), there is a systematic downward bias on popular decks' expected WR. Compute the magnitude: what would Dragapult's expected WR be if mirror matches were excluded from the field expectation, or if mirrors were fixed at exactly 50%? This is a 10-line calculation and directly addresses whether the paradox is partly an artifact of the tie convention.

---

## Questions for Authors

**Q1.** The Nash equilibrium was computed externally via `scipy.optimize.linprog` and then verified in Lean. How sensitive is the equilibrium support to numerical precision in the LP solver? Specifically, did you verify that scipy's output was exact (rational), or did you convert floating-point output to exact rationals? If the latter, how was the rounding performed, and could a different rounding yield a different support set that also passes verification?

**Q2.** Raging Bolt Ogerpon appears in 98.3% of resampled equilibria (highest inclusion rate) yet has only 3.3% observed meta share — an even more extreme popularity-performance gap than Dragapult/Grimmsnarl. The paper focuses on the Dragapult paradox but barely discusses Raging Bolt. Is there a strategic narrative for why Raging Bolt is so equilibrium-critical yet so underplayed? Does it face specific barriers (card availability, deck complexity, metagame perception) that would explain the gap?

**Q3.** The replicator dynamics analysis is entirely one-step from the observed distribution. Have you computed iterated trajectories (e.g., 50–100 steps) to check whether the dynamics converge to the Nash equilibrium, cycle, or exhibit chaotic behavior? For a non-zero-sum 14-player game, convergence is not guaranteed, and the relationship between your verified Nash support and the replicator attractor (if any) is unclear. Even a Python simulation of iterated dynamics would meaningfully complement the single-step Lean verification.

---

*Reviewer 3, IEEE Transactions on Games*
*Review date: February 20, 2026*
