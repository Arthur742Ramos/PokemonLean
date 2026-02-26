# Review of Submission #753 (v10)

**"From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"**

**Reviewer expertise:** Formal methods (Lean/Coq proof engineering), algorithmic game theory, mechanism design.

---

## Summary

This paper presents a ~30K-line Lean 4 artifact that formally verifies game-theoretic metagame analysis—Nash equilibria, replicator dynamics, and expected-value computations—for competitive Pokémon TCG using real tournament data from Trainer Hill (Jan–Feb 2026). The headline result is a "popularity paradox": Dragapult, the most-played deck at 15.5% share, achieves only 46.7% expected win rate, while Grimmsnarl at 5.1% share achieves 52.7%. A machine-checked Nash equilibrium assigns Dragapult zero weight. A symmetric constant-sum formulation, replicator dynamics over the full 14-deck game, robustness bounds, and skill-sensitivity analysis are all verified. The paper has gone through five revision rounds and the artifact now contains no `sorry`, `admit`, or custom axioms, with `native_decide` as the acknowledged trust boundary.

---

## Scores

| Criterion        | Score | Justification |
|------------------|:-----:|---------------|
| **Novelty**      | 3/5   | First proof-carrying metagame analytics pipeline for a real competitive game ecosystem. The individual game-theory components (Nash verification, replicator dynamics) are standard; the novelty is in the integration and the domain application. |
| **Technical Soundness** | 4/5 | The formal artifact is well-structured and the claims are faithfully mirrored by Lean theorems. The `native_decide` trust boundary is honestly disclosed and justified. One point deducted for the gap between what is verified and what is claimed (see weaknesses). |
| **Significance** | 3/5   | Methodologically interesting as a proof-of-concept. The game-theoretic insights themselves are not deep (weighted averages over a matrix), and the temporal scope is narrow. Impact depends on whether the community adopts the methodology. |
| **Clarity**      | 4/5   | Very well written for a v10 paper. The trust boundary discussion is exemplary. Some redundancy across sections (the popularity paradox is stated in at least four different ways). |
| **Reproducibility** | 5/5 | Exceptional. The artifact is self-contained, `lake build` is documented, all constants trace from source data to theorems. This is a model for reproducible formal work. |

---

## Recommendation: **Weak Accept**

The paper makes a genuine methodological contribution—demonstrating that proof-carrying analytics is feasible for real competitive game ecosystems—and the artifact quality is high. The weaknesses are real but bounded, and the paper is honest about its limitations. The work is suitable for IEEE Transactions on Games as a methods paper, provided the authors address the issues below.

---

## Strengths

### S1: Exemplary Artifact Engineering and Transparency

The 30K-line Lean 4 artifact is genuinely impressive as a proof-engineering effort. The `MatrixConsistency.lean` cross-module consistency check (proving that the array-based matrix for Nash verification matches the function-based matrix for replicator dynamics) eliminates an entire class of copy-paste bugs that plague computational game-theory work. The `StepSizeGeneral.lean` file provides a clean symbolic proof of step-size invariance with a rigorous Int↔Rat bridge, going beyond brute-force `native_decide`. The trust boundary discussion around `native_decide`—including the honest acknowledgment that `Fin.foldl` opacity structurally precludes kernel-checked `decide`—sets a standard for formalization papers.

### S2: Well-Designed Robustness Analysis

The paper goes significantly beyond point estimates. The skill-sensitivity analysis (`SkillSensitivity.lean`) showing that Dragapult needs ≥3.4pp uniform bias correction to break even, the share-perturbation theorems (`SharePerturbation.lean`) showing the paradox is independent of Dragapult's share across the full 1–30% grid, and the worst-case "Other" segment bounds collectively provide a layered defense of the headline claim. The 10,000-iteration sensitivity analysis (external Python, honestly labeled as such) showing core support deck inclusion >96% is a responsible complement to the verified point equilibrium. This is how robustness should be handled.

### S3: Clean Separation of Verified and Unverified Claims

The paper is disciplined about labeling what is machine-checked vs. what is externally computed (Python sensitivity analysis) vs. what is interpretive narrative (behavioral-economic explanations). The explicit data provenance section, the acknowledgment that the matchup matrix is an empirical input parameter analogous to trusted source code in a verified compiler, and the careful scoping of the type-advantage alignment as "correlational consistency" rather than causal derivation all show maturity in the authors' understanding of what formal verification does and does not guarantee.

---

## Weaknesses

### W1: The `native_decide` Concentration Risk Is More Serious Than Acknowledged

While the paper honestly discloses the `native_decide` trust boundary, the implications deserve stronger emphasis. All 244 `native_decide` proofs—including every Nash equilibrium verification, every replicator dynamics result, and every bridge alignment theorem—depend on the same compilation pipeline. A single bug in Lean 4's code generation for `Lean.Rat` arithmetic over `Fin.foldl` would invalidate the entire game-theoretic core simultaneously. The paper states "no such bugs have been reported in practice," but this is an argument from absence. The `StepSizeGeneral.lean` symbolic proof is the one bright spot of defense-in-depth, but it covers only sign invariance, not the equilibrium or fitness computations themselves.

**Recommendation:** The authors should (a) more prominently flag that the entire Nash/replicator core shares a single-point-of-failure trust assumption, (b) report the Lean toolchain version and commit hash used for verification, and (c) discuss whether independent re-verification with a different Lean build or a second proof assistant (e.g., extracting the rational arithmetic to a verified C checker) would be feasible.

### W2: The Game-Theoretic Model Is Thin Relative to the Verification Overhead

The verified game-theoretic model is a standard bimatrix Nash equilibrium over a 14×14 matchup matrix with point estimates. This is important to get right, but it is not a deep game-theoretic contribution. Several modeling limitations compound:

1. **No uniqueness proof.** The paper verifies *a* Nash equilibrium but explicitly states uniqueness is not proven. Without uniqueness (or at least a characterization of the equilibrium set), the claim "Dragapult is excluded from equilibrium" is weaker than it appears—it means excluded from *this* equilibrium. The `dragapult_strictly_suboptimal` theorem (Dragapult's payoff is strictly below the game value against the Nash column mix) is a stronger statement, but it only rules out Dragapult from best responses to *this particular* column strategy. The paper should more clearly articulate what is and is not proven about all equilibria.

2. **Single-match model vs. Swiss reality.** The paper acknowledges the Swiss-system mismatch but does not verify any Swiss-relevant quantities beyond the Bo3 amplification formula. For a venue like IEEE Transactions on Games, the practical gap between "Nash equilibrium of the single-match game" and "optimal deck choice for a Swiss tournament" should be addressed more substantively.

3. **Static snapshot.** The three-week window and the admission that one of three directional predictions failed on out-of-sample data (Grimmsnarl declined due to Mega Absol predation) suggest the model has limited predictive horizon. The paper correctly notes this, but it somewhat undermines the practical significance of the equilibrium computation.

**Recommendation:** The authors should (a) prove or discuss the structure of the equilibrium set (e.g., is the LP dual non-degenerate? Does complementary slackness pin down uniqueness?), (b) consider verifying at least one Swiss-relevant quantity beyond Bo3 amplification, and (c) more explicitly position the contribution as methodological infrastructure rather than predictive analytics.

### W3: Large Fraction of Artifact Is Loosely Connected Supporting Infrastructure

Of the ~30K lines and ~2,500 theorems, only ~180 directly verify empirical claims. The remaining infrastructure—card effects, zone transitions, deck legality, Lost Zone mechanics, V-STAR rules, Stadium cards, etc.—is presented as "supporting infrastructure" and "future-proofing for counterfactual analysis," but it is not exercised by any theorem in the paper. The type-advantage bridge (Section III-A) connects rules to data, but only through a correlational consistency check (83% alignment with 15/18 matchups), not through any causal derivation.

This raises a cost-benefit question: is verifying card conservation for Professor's Research (a combinatorial identity about list lengths) meaningful for the strategic analysis? The paper argues these checks prevent "subtle bookkeeping bugs from distorting probability estimates," but no probability estimate in the paper actually depends on this card-flow invariant. The 15 rules files and ~4K lines of Core Rules & Semantics are essentially a separate contribution (a partial Pokémon TCG formalization) grafted onto the game-theory pipeline.

**Recommendation:** Either (a) demonstrate an end-to-end theorem chain where a rules-level property (e.g., card conservation) flows through to a strategic conclusion, or (b) clearly separate the rules formalization as a standalone contribution and reduce its prominence in the paper. The current framing overstates the integration between rules and strategy.

---

## Minor Issues

1. **Identifier typo:** The `GrimssnarlFroslass` (double-s, single-m) identifier is acknowledged in a footnote but should ideally be fixed in the artifact for professionalism.

2. **Table I bootstrap semantics:** The column header "95% Range" with the footnote "not frequentist confidence intervals" is potentially confusing. Consider "95% sensitivity range" or "95% resampling interval."

3. **Replicator dynamics convergence:** The paper proves single-step directional pressures but explicitly disclaims convergence. A brief discussion of whether the Lyapunov analysis (share product) could be extended to multi-step guarantees would strengthen Section VII.

4. **Wilson intervals:** The Wilson interval formula in Section V-D appears correct, but the propagation to expected win rate intervals ("Dragapult's expected field win rate... has a 95% interval of approximately [45.5%, 47.9%]") seems to assume independent matchup cells. If matchup correlations exist (e.g., because the same games appear in multiple cells for decks that faced each other), these intervals may be anti-conservative. A brief note on independence assumptions would be appropriate.

5. **Behavioral interpretation scope:** Section VI-C cites Tversky & Kahneman (1974), Banerjee (1992), and quantal response equilibrium as potential explanations for non-equilibrium play, but these are post-hoc rationalizations without any testable predictions in the current framework. This section could be shortened without loss.

6. **Bo3 independence:** The paper notes that Pokémon TCG lacks sideboarding, making Bo3 game independence "substantially more defensible." However, information revelation (seeing the opponent's deck composition in game 1) and psychological tilt are acknowledged but not quantified. Since the Bo3 amplification formula `3p²-2p³` is verified, any deviation from independence directly undermines these specific verified results. Consider stating the sensitivity of Bo3 amplification to correlation.

7. **Page budget:** At 12 pages, the paper is at the IEEE limit. The behavioral-economic section (VI-C), the preliminary directional check (VII-A), and some of the RPS toy examples in the artifact could be condensed to make room for addressing W2/W3.

---

## Questions for Authors

1. Can you characterize the equilibrium set more precisely? Is the LP dual non-degenerate, implying uniqueness of the Nash equilibrium for each player?

2. Have you attempted cross-validation against Limitless API data directly, or against a different time window, to assess temporal stability of the matchup matrix?

3. What is the wall-clock build time for the full artifact on the reference hardware? The paper says "~10 min on Apple M-series, 16 GB RAM"—is this dominated by `native_decide` on the Nash verification?

4. The `FiniteGame` structure carries a `payoff` field (player payoffs) and a `matrix` field, but `payoff` is always set to `fun _ _ => 0` and never used. Is this vestigial? It could confuse readers inspecting the artifact.

---

## Detailed Assessment

**Is the paper suitable for IEEE Transactions on Games?** Yes—it sits at the intersection of formal methods and competitive game analysis, and the methodology has clear transferability to other game ecosystems (Magic: The Gathering, Hearthstone, etc.).

**Would I trust the results?** Modulo the `native_decide` boundary (which I consider acceptable for the Lean community's current practice), yes. The artifact is well-organized, the cross-consistency checks are reassuring, and the robustness analysis addresses the most obvious objections.

**Is the contribution primarily methodological?** Yes, and the paper is honest about this. The specific metagame findings (Dragapult is overplayed) are useful illustrations but could be computed with a spreadsheet. The value is in the verification infrastructure—the guarantees against silent errors, the compositional theorem linking, and the reproducibility standard.

**Overall:** A solid methods paper with a well-executed artifact, limited by the thinness of the game-theoretic model and the loose coupling between the rules formalization and the strategic analysis. Suitable for publication with minor revisions addressing the trust boundary documentation and the equilibrium uniqueness question.

---

*Review completed 2026-02-20. Reviewer: anonymous (formal methods + game theory).*
