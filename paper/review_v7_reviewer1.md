# IEEE Transactions on Games — Reviewer Report

**Submission #753 (v7)**
*"From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"*

**Review Date:** 2026-02-20
**Reviewer Expertise:** Game theory (Nash equilibria, evolutionary dynamics, mechanism design)
**Reviewer Confidence:** High

---

## Summary

The paper presents a Lean 4 formalization of metagame analysis for the competitive Pokémon TCG, using real tournament data (Trainer Hill, Jan–Feb 2026). The central finding is a "popularity paradox": the most-played deck (Dragapult, 15.5% share) has a sub-50% expected field win rate, while a less-played deck (Grimmsnarl, 5.1%) achieves 52.7%. The authors verify a 6-deck Nash equilibrium over a 14×14 bimatrix game, run discrete replicator dynamics over the full 14-deck system, and provide a type-advantage bridge from game rules to empirical matchup outcomes. The artifact is ~30K lines of Lean 4 with no `sorry`/`admit`.

This is v7, responding to prior reviewer concerns about length (14→12pp), theorem count qualification (~180 core of ~2,500), `native_decide` disclosure, step-size invariance, and skill-sensitivity bounds.

---

## Scores

| Criterion        | Score | Comment |
|-----------------|-------|---------|
| **Novelty**          | 4/5 | First formally verified metagame equilibrium analysis over real tournament data. The methodology is genuinely new, even if the game-theoretic tools themselves are standard. |
| **Technical Soundness** | 3/5 | The Nash verification is correct but the game-theoretic modeling has non-trivial gaps (see below). The replicator dynamics claims are carefully scoped in v7 but still risk over-interpretation. |
| **Significance**     | 3/5 | The methodological template is valuable. The specific empirical results have a 3-week shelf life. The gap between the verification effort (~30K LoC) and the analytical payload (weighted averages + LP solution) remains a legitimate concern. |
| **Clarity**          | 4/5 | Much improved from v6. The paper reads well, the trust boundary is explicit, the qualification of "2,500 theorems" is now honest. Some game-theoretic terminology still needs tightening. |
| **Reproducibility**  | 5/5 | Exemplary. The artifact is self-contained, `lake build` reproducible, data provenance is documented, and the LP discovery/Lean certification split is transparent. |

---

## Detailed Assessment

### 1. Nash Equilibrium Formulation

**Strengths.** The bimatrix formulation is correctly implemented. The `NashEquilibrium` predicate in `NashEquilibrium.lean` checks:
- Both strategies are valid mixed strategies (non-negative, sum to 1)
- Row best-response: no pure strategy improves on the expected payoff
- Column best-response: ditto for the column player

This is textbook correct for a finite two-player game. The LP-discover / Lean-certify split is a clean architecture — the untrusted solver finds candidates, the trusted verifier checks optimality conditions. The 14×14 best-response check across all 196 cells is exactly the kind of tedious verification where formal methods earn their keep.

The symmetrized constant-sum formulation (Table IV) is a welcome addition. The game value of exactly 500 and the 7-deck support provide a useful robustness check on the bimatrix result. I appreciate that the row/column support asymmetry in the bimatrix case is explicitly explained as a consequence of the tie convention breaking exact constant-sum structure.

**Concerns.**

**(a) The game is not zero-sum, and the paper's language still wobbles.** The `FiniteGame` structure has a `payoff` field that is set to `fun _ _ => 0` — it is never used. The `NashEquilibrium` definition uses a minimax-like formulation: it checks `rowPurePayoff ≤ value` and `value ≤ colPurePayoff`. This is the saddle-point condition for zero-sum games, which happens to be equivalent to the Nash best-response condition only when the game is constant-sum. The paper acknowledges the matrix is not exactly constant-sum (due to ties), yet the equilibrium definition implicitly assumes it is. For the bimatrix equilibrium, this works because the saddle-point inequalities are *stronger* than Nash best-response — if they hold, it's a Nash equilibrium regardless. But the paper should state this explicitly rather than letting readers infer it. The sentence "the Nash equilibrium is verified as a bimatrix Nash equilibrium via best-response checks for both players independently, which does not require the zero-sum assumption" (Section VII) is correct but under-explained; the actual Lean definition *is* a saddle-point check, which is subtly different from the standard bimatrix Nash condition (where each player's strategy must be a best response to the *other's* strategy, not to a shared game value).

**(b) The equilibrium value (47.97%) is reported but not discussed.** The sub-50% game value is dismissed as a tie-convention artifact, but this deserves more attention. In a truly constant-sum game, the game value determines how much each player can guarantee. Here, the row player's guarantee is below 50%, meaning the game is slightly favorable to the column player. Is this an artifact of the specific equilibrium found, or is it structural? The symmetrized formulation gives exactly 50%, which suggests it's the tie convention. But since the bimatrix equilibrium is the one the paper emphasizes, the interpretation of a sub-50% value for *both* players (since the column player's payoff is not 1000 minus the row's) should be discussed.

**(c) Uniqueness is not addressed.** The paper verifies *a* Nash equilibrium but says nothing about whether it is unique or one of many. For a 14×14 game with this payoff structure, multiple equilibria are likely. The sensitivity analysis (Table I) partially addresses this by showing support fragility (exact support recovered in only 2.1% of iterations), but the paper never states whether the verified equilibrium is unique even for the point-estimate matrix. This matters because the "Dragapult gets 0% weight" claim could be specific to one equilibrium while other equilibria include Dragapult.

### 2. Replicator Dynamics Scoping and Step-Size Claims

**Strengths.** The v7 scoping is dramatically improved. The paper now correctly states that replicator results are "statements about single discrete steps from the observed share vector" and establish "directional pressure, not convergence trajectories." The step-size invariance theorems (`StepSizeInvariance.lean`) are a nice touch — they confirm that the 5-grower/9-shrinker classification is determined by the sign of $f_i - \bar{f}$, independent of $dt$.

The algebraic insight behind step-size invariance is simple ($\text{sign}(x_i' - x_i) = \text{sign}(f_i - \bar{f})$ for $dt > 0$) but worth verifying formally because it disciplines the choice of $dt$ as a modeling parameter.

**Concerns.**

**(a) The step-size invariance claim is trivially true and slightly misleading.** For discrete-time replicator dynamics $x_i' = x_i(1 + dt(f_i - \bar{f}))$, the direction $x_i' - x_i = x_i \cdot dt \cdot (f_i - \bar{f})$ has the same sign as $f_i - \bar{f}$ for any $dt > 0$ and $x_i > 0$. This is a one-line algebraic fact, not a deep property. Verifying it for three specific values of $dt$ by brute-force computation (rather than proving the general algebraic lemma) understates the simplicity of the result while overstating its significance. The paper should acknowledge this is a sanity check, not a substantive invariance result. A more interesting (and harder) step-size result would be to show that the discrete dynamics do not produce negative shares or that the discrete and continuous dynamics agree qualitatively for a range of $dt$.

**(b) The `EvolutionaryDynamics.lean` file contains both 3-deck toy examples and 4-deck subcycle analyses that are superseded by the full 14-deck `FullReplicator.lean` results.** The paper text focuses on the 14-deck results, but the artifact retains ~200 lines of 4-deck subcycle theorems that duplicate conclusions already proven on the full game. This isn't a paper defect per se, but it inflates the theorem count and creates an impression of more analytical depth than exists. The 4-deck subcycle replicator dynamics are strictly weaker than the 14-deck results — they should be either removed from the artifact or clearly marked as scaffolding.

**(c) The predictive validation (Section VII-A) is honest but weak.** Two of three directional predictions confirmed at one day out is not statistically meaningful. The Grimmsnarl counter-example (declining despite highest fitness) is correctly attributed to iterated predator-prey effects, but this undermines the practical value of single-step replicator predictions. The paper acknowledges this, but the framing still gives these predictions more weight than they deserve.

### 3. Skill-Sensitivity Bound Methodology

**Strengths.** The `SkillSensitivity.lean` analysis is well-designed. The model — a uniform additive bias $b$ across all Dragapult matchups — is simple and interpretable. The tight integer thresholds (3.4pp break-even, 6.1pp to match Grimmsnarl) are cleanly verified with both upper and lower bounds (`skill_threshold_breakeven` + `skill_threshold_breakeven_tight`).

**Concerns.**

**(a) The uniform bias model is too simple.** A uniform skill correction assumes Dragapult pilots are equally weaker in *every* matchup. A more realistic model would allow matchup-specific bias (e.g., Dragapult pilots might be disproportionately weaker in complex matchups). The paper could strengthen the robustness claim by showing that even under adversarial (non-uniform) bias allocation, the paradox survives — e.g., by solving for the minimum total bias $\sum_j |b_j|$ needed to push Dragapult above 50%, subject to the constraint that each $b_j$ is bounded by a plausible range.

**(b) The 3.4pp threshold is contextualized in the Threats section but not benchmarked against known skill differentials in TCG populations.** Is 3.4pp a lot or a little? Without an empirical estimate of the skill gap between Dragapult pilots and the field average, the reader cannot assess whether the confound is plausible. Even a rough citation to skill-differential estimates from other competitive games would help.

### 4. Paper Length and Structure

The 12-page version is appropriate. The cuts from v6 were well-chosen. The remaining content is dense but not padded. If anything, the paper could afford to cut the 3-archetype RPS toy examples (Section VII's abstract dynamics) in favor of expanding the game-theoretic discussion (uniqueness, interpretation of game value, relationship between bimatrix and zero-sum formulations).

One structural suggestion: the type-advantage bridge (Section III-A) is interesting but somewhat disconnected from the game-theoretic core. It would read better as a standalone subsection in the data methodology (Section V) rather than in the formalization section, since it is ultimately a correlational validation of the type assignments.

---

## Must-Do Revisions

1. **Clarify the equilibrium definition's relationship to game structure.** The `NashEquilibrium` predicate is a saddle-point condition. State explicitly that: (a) for the bimatrix (non-constant-sum) case, this is a *sufficient* condition for Nash equilibrium (stronger than needed); (b) the row/column support asymmetry is expected; and (c) the sub-50% game value is a consequence of the tie convention, not a strategic asymmetry. Currently the paper gestures at this but does not nail it down precisely. One additional sentence in the Lean code comment and one paragraph in Section VII would suffice.

2. **Address equilibrium uniqueness or multiplicity.** State whether the verified equilibrium is the unique Nash equilibrium of the 14×14 game (unlikely) or one of potentially many. If multiple equilibria exist, discuss whether the "Dragapult = 0%" result holds across all equilibria or is specific to the verified one. The sensitivity analysis (Table I) partially addresses this but only for perturbed matrices, not for the point-estimate matrix itself. At minimum, verify whether any equilibrium with Dragapult in the support exists by checking a small grid of candidate profiles — the Lean infrastructure already supports this.

3. **Tone down the step-size invariance discussion.** Acknowledge that for $x_i' = x_i(1 + dt(f_i - \bar{f}))$ the directional invariance is algebraically immediate for any $dt > 0$. The formal verification confirms the computation is correct but does not establish a non-trivial dynamical property. Alternatively, prove the *general* algebraic lemma in Lean (for all $dt > 0$ and $x_i > 0$, $\text{sign}(x_i' - x_i) = \text{sign}(f_i - \bar{f})$) rather than checking three specific values, which would be a genuinely stronger formal result.

---

## Questions for Authors

1. **On equilibrium multiplicity:** Have you checked whether the 14×14 game has equilibria where Dragapult receives positive weight? If so, what is the maximum Dragapult weight across all Nash equilibria? If not, can you verify (perhaps via iterated elimination of dominated strategies) that Dragapult is dominated in the reduced game?

2. **On the `native_decide` trust boundary:** You note that `Fin.foldl` is opaque to the kernel reducer. Have you considered reformulating `sumFin` as a structurally recursive function over `Fin` (e.g., `sumFin 0 f = 0; sumFin (n+1) f = f ⟨n, ...⟩ + sumFin n (f ∘ Fin.castSucc)`)? If so, what specifically blocked kernel reduction — was it the rational arithmetic, the recursion depth, or something else?

3. **On the sensitivity analysis:** The 10,000-iteration resampling uses uniform draws from Wilson intervals. Why uniform rather than, e.g., Beta-distributed draws based on the underlying win-loss counts? The choice of resampling distribution affects the inclusion frequencies in Table I. Relatedly, since you have the raw W-L-T counts for each matchup, a Bayesian posterior over the matchup matrix would be more principled than uniform resampling from frequentist confidence intervals.

---

## Minor Issues

- The identifier `GrimssnarlFroslass` (double-s, single-m) is acknowledged in a footnote but still jars on every code listing. Consider a `notation` alias.
- Table II (matchup matrix) shows only the top-6 subset. The full 14×14 matrix should appear in supplementary material (if it doesn't already).
- The Lyapunov analysis in `EvolutionaryDynamics.lean` (share product) is interesting but entirely absent from the paper text. Either cite it or remove it from the artifact to avoid confusion about what is claimed.
- Figure 3 (directed cycle motif) uses a 4-deck subset but the replicator results are over the full 14-deck game. Clarify that the cycle diagram is illustrative, not the basis for the dynamics claims.
- The Bo3 amplification section (Section VIII) is standard and adds limited novelty. Consider trimming to a single paragraph with the table.

---

## Overall Recommendation

### **Weak Accept**

The paper makes a genuine methodological contribution: it demonstrates that proof-carrying metagame analytics is feasible for real competitive game ecosystems. The Lean artifact is impressive in scope and engineering quality, and the v7 revisions substantially address prior concerns about overclaiming and trust boundaries. The game-theoretic modeling is competent but not state-of-the-art — the equilibrium analysis uses standard tools (LP + best-response certification) and the replicator dynamics are single-step directional checks rather than convergence analysis.

The paper earns its acceptance on methodological novelty and artifact quality, not on game-theoretic depth. The three Must-Do revisions are tractable and would raise confidence in the equilibrium claims. If addressed, I would upgrade to Accept.
