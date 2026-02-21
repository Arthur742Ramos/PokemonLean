# Review: Submission #753 — "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Reviewer:** Reviewer 2 (IEEE Transactions on Games)  
**Specialization:** Game theory, formal methods  
**Date:** 2026-02-20

---

## 1. Summary

This paper presents a formally verified metagame analysis of the competitive Pokémon Trading Card Game using Lean 4, covering ~30,000 lines and ~2,500 theorems with no `sorry`/`admit`/custom axioms. The authors encode real tournament matchup data from Trainer Hill (Jan–Feb 2026), prove a "popularity paradox" (Dragapult at 15.5% meta share has only 46.7% expected win rate), compute and machine-check a Nash equilibrium over the 14-archetype game, and verify directional replicator dynamics predictions. The primary contribution is methodological: demonstrating that proof-carrying analytics can transform qualitative metagame narratives into machine-checkable, reproducible strategic science.

---

## 2. Strengths

**S1. Genuinely novel methodology.** To my knowledge, this is the first paper to couple a theorem prover with real competitive TCG tournament data to produce machine-checked Nash equilibrium and evolutionary dynamics results. The pipeline—from data encoding through expected-value computation, equilibrium certification, and replicator dynamics—is end-to-end and architecturally clean. The "discover externally, verify internally" pattern (Python LP solver produces candidate equilibrium weights; Lean independently verifies best-response conditions for all 14 strategies) is a sound and well-documented trust decomposition.

**S2. Rigorous equilibrium certification.** The Nash equilibrium verification is done correctly: `real_nash_row_best_response_checks` and `real_nash_col_best_response_checks` universally quantify over all 14 pure strategies for both players (NashEquilibrium.lean:320–328). This is a genuine 196-cell verification, not a spot-check. The authors also provide a symmetrized constant-sum formulation (`SymmetricNash.lean`) with 7-deck support yielding game value exactly 500, which is the right thing to do given the approximately-but-not-exactly constant-sum structure of the empirical matrix. The distinct row/column supports in the bimatrix version are correctly explained as a consequence of tie-weighting breaking constant-sum symmetry.

**S3. Thorough robustness analysis.** The paper addresses validity threats seriously: worst-case bounds on the unmodeled 30.5% "Other" field segment (Section X), Wilson confidence intervals with explicit propagation caveats, a 10,000-iteration sensitivity analysis (Table I) showing core support decks appear in >96% of resampled equilibria, and share-perturbation theorems. The honest admission that the exact Nash support is recovered in only 2.1% of resampled iterations, while the qualitative conclusions are robust, is commendable transparency.

**S4. Bug-catching case study is convincing.** The authors report that during development, best-response certification failed multiple times due to data-entry errors (swapped row/column indices, copy-paste row duplication) in the 14×14 matrix. Each failure was caught immediately by `native_decide` returning false. This is a concrete, credible argument for formal verification over ad hoc scripting—an LP solver would have silently returned a different equilibrium without flagging the corrupt input. This addresses a real failure mode in metagame analytics.

**S5. Honest trust-boundary disclosure.** The paper is unusually transparent about the limitations of `native_decide` (Section IX-C), noting that ~244 theorems depend on it, that `Fin.foldl` is opaque to the Lean 4 kernel reducer making `decide` structurally precluded (not merely slow), and that a hypothetical compiler bug could invalidate all computational proofs simultaneously. This is exactly the right level of disclosure for a verification-focused paper.

---

## 3. Weaknesses

**W1. Discrete-time vs. continuous-time replicator dynamics: insufficiently distinguished.** The paper presents the continuous-time replicator equation (ẋ_i = x_i(f_i − f̄)) in the Nash/dynamics section but implements discrete-time Euler steps (`replicatorStep` with dt = 1/10 or 1/100). The authors acknowledge this ("All verified replicator results are therefore statements about single discrete steps...they establish directional pressure, not convergence trajectories"), but the acknowledgment is buried mid-paragraph on what appears to be page 7–8.

The problem is deeper than presentation. Discrete-time replicator dynamics can exhibit qualitatively different behavior from continuous-time dynamics—including chaos, overshooting, and spurious extinction—depending on step size and payoff scaling. The `replicatorStep` function uses dt=1/10 for the full 14-deck game and dt=1/100 for the 4-deck subcycle, but there is no analysis of step-size sensitivity. The share conservation theorem (`full_replicator_step_conservation`) is verified only for dt=1/10; it is not proved to hold generically for all valid step sizes (which it does algebraically, but the paper doesn't say so). The Lyapunov analysis in `EvolutionaryDynamics.lean` (share product as Lyapunov function) is only verified for the symmetric 3-archetype RPS case, not for the real 14-deck game. Claims like "no deck goes extinct" are verified for 3 or 5 discrete steps from a single initial condition—this is not an extinction result in any meaningful dynamical-systems sense.

**W2. The connection between rules formalization and metagame analysis remains loose despite effort.** Section III-A (type alignment) is the main bridge. The authors show that 13/15 Dark→Psychic matchups exceed 50% win rate, and claim 83% overall type-advantage alignment (15/18 matchups). However, the type assignments (`Deck.primaryAttackType`, `Deck.primaryDefenseType`) are manually specified domain-expert labels, not formally derived from deck composition. The paper acknowledges this ("modeling assumptions, not formally derived from deck composition"), but the alignment check then reduces to: "given expert-assigned labels, the observed win rates are directionally consistent." This is a consistency check, not a falsifiable prediction from the formalization.

Furthermore, the 83% figure is computed over a cherry-picked subset (Dark attackers vs. Psychic defenders) rather than all type-advantage pairs. The binomial p-value claim (p < 0.001) assumes independence between matchup pairs, which is questionable when several involve the same deck.

**W3. The Nash equilibrium analysis models only single-match expected payoffs, not Swiss-tournament utility.** The paper acknowledges this (Section VII, first paragraph: "a modeling limitation") and provides brief Bo3 amplification calculations (Table VII), but the gap is larger than suggested. In Swiss tournaments, variance matters: a deck with 51% win rate against everyone can be strictly preferable to one with 70% against half and 30% against the other half, because Swiss rewards consistency. The Nash equilibrium computed here is therefore not the equilibrium a rational tournament player would compute. The Bo3 section (Section VIII) is too brief to bridge this gap and does not recompute the equilibrium under Bo3 or Swiss payoffs.

**W4. The "2,500 theorems" framing oversells the verification depth.** Examining the Lean source, the vast majority of theorems are either (a) infrastructure boilerplate (decidability instances, type coercions, `Fin` manipulation), (b) toy examples (3-archetype RPS, 2×2 minimax), or (c) repetitive per-deck instantiations (e.g., 14 separate fitness comparison theorems in `FullReplicator.lean`). The count of "roughly 180 theorems directly verify empirical claims" (Section IX-D) is more honest but still conflates trivially-verified point comparisons (e.g., `matchupWR .X .Y > 500` discharged by `decide`) with substantive results. The paper's actual intellectual contribution rests on perhaps 10–20 key theorems (Nash certification, replicator classification, robustness bounds), not 2,500.

**W5. Predictive validation is minimal and partly fails.** Section VII-B reports that 2/3 directional predictions were confirmed against the immediately following Trainer Hill snapshot, while Grimmsnarl (predicted: growing, as the highest-fitness deck) actually declined. The authors attribute this to "secondary effects" of Mega Absol's rise—but this is exactly the kind of post-hoc narrative the paper claims to replace with formal verification. The single-step replicator model cannot capture multi-step cascades by design, so the predictive validation is structurally underpowered. No quantitative predictive score (e.g., Brier score, rank correlation) is reported.

---

## 4. Must-Do Revisions

**M1. Clearly separate discrete-time and continuous-time replicator dynamics claims.** The paper must not present the continuous-time ODE and then verify only discrete-time Euler steps without explicit discussion of the approximation gap. Either: (a) prove that the step sizes used are small enough that qualitative conclusions (growth/decline direction) are preserved (this is straightforward for a single step since the sign of f_i − f̄ is independent of dt for sufficiently small dt > 0, but should be stated as a theorem), or (b) remove the continuous-time equation entirely and present the work as purely discrete-time replicator dynamics, citing appropriate references (e.g., Cabrales & Sobel 1992, Weibull 1997 Ch. 5). The current presentation risks misleading readers into thinking convergence or asymptotic results from continuous-time theory apply.

**M2. Qualify the "2,500 theorems" claim.** The abstract and introduction should distinguish between infrastructure theorems, per-deck instantiations, and core analytic results. A more honest framing would be: "The artifact contains approximately 2,500 Lean declarations, of which ~180 directly verify empirical claims and ~20 constitute the core game-theoretic results." The current presentation inflates the perceived verification depth.

**M3. Strengthen or reframe the type-alignment bridge.** Either (a) extend the alignment analysis to all type-advantage pairs in the 14-deck matrix (not just Dark→Psychic), report the full confusion matrix, and compute the alignment rate without cherry-picking, or (b) explicitly reframe the analysis as a "sanity check" rather than a "bridge" and remove the causal-sounding language ("the rules layer generates falsifiable predictions"). The current 83% figure based on a selected subset with a dubious independence assumption is not robust enough for the weight placed on it.

---

## 5. Should-Do Revisions

1. **Add a step-size sensitivity theorem.** Verify that for all dt ∈ (0, δ) for some explicit δ, the sign of (x_i' − x_i) agrees with the sign of (f_i − f̄). This is trivial given the multiplicative form x_i' = x_i(1 + dt·(f_i − f̄)), since for x_i > 0 and dt > 0, the sign of x_i' − x_i = x_i · dt · (f_i − f̄) equals the sign of (f_i − f̄). State this as a generic Lean theorem.

2. **Recompute the Nash equilibrium under Bo3 payoffs.** The Bo3 transform p → 3p² − 2p³ applied to the full 14×14 matrix would yield a new game whose equilibrium is more tournament-relevant. This is straightforward given the existing infrastructure.

3. **Report the full 14×14 matchup matrix in the paper body,** not just a 6×6 subset. This is essential for reproducibility by readers who do not download the artifact. If space is tight, use a compact format or supplementary appendix.

4. **Provide a single-command reproducibility check.** The paper mentions `lake build` (~10 min), but should specify the exact Lean toolchain version, mathlib commit (if used), and OS requirements. A `Dockerfile` or `flake.nix` would be ideal.

5. **Fix the reference page column imbalance.** The final page has severe column imbalance (left column full of references, right column nearly empty). This is a straightforward LaTeX fix (e.g., `\balance` or `\IEEEtriggeratref` adjustment) that should not reach final copy.

6. **Rename `GrimssnarlFroslass` to `GrimmsnarFroslass` or `GrimmsnarFroslass`.** The footnote acknowledging the typo (single-m, double-s) is insufficient for a 30,000-line artifact. A find-and-replace is cheap; perpetuating a known error in a "reproducibility-first" artifact undermines the credibility claim.

7. **Discuss the sensitivity analysis methodology more carefully.** The 10,000-iteration resampling (Table I) is done in Python, external to Lean. The paper should clearly state whether the LP solver uses exact arithmetic or floating-point, and whether the "95% sensitivity ranges" are parametric or empirical quantiles.

8. **Cite the discrete-time replicator dynamics literature explicitly.** The current citations (Taylor & Jonker 1978, Weibull 1997) are primarily continuous-time. Add Cabrales & Sobel (1992), Losert & Akin (1983), or similar discrete-time references.

---

## 6. Questions for Authors

**Q1.** The `NashEquilibrium` definition (NashEquilibrium.lean:62–65) uses a zero-sum-flavored formulation: row player cannot improve upward, column player cannot lower row payoff. This is the minimax saddle-point condition, not the general bimatrix Nash condition. The paper claims the equilibrium is "verified as a bimatrix Nash equilibrium via best-response checks for both players independently, which does not require the zero-sum assumption" (Section VII). Can you clarify: is the verified property equivalent to a general Nash equilibrium for bimatrix games, or does it assume/exploit the (approximate) zero-sum structure? Specifically, what is the column player's payoff function? If it is 1000 − M_{ij} (constant-sum), the verification is valid but should be stated as a constant-sum Nash result. If it is −M_{ij} (zero-sum), the sub-50% game value is trivially expected. If the column payoff is M_{ji} (the transpose), then the formulation is a genuine bimatrix game and the saddle-point condition is strictly stronger than Nash.

**Q2.** The replicator dynamics in `EvolutionaryDynamics.lean` and `FullReplicator.lean` operate on two different games: a 4-deck subcycle (`realCyclePayoff` with centered payoffs WR − 500) in the former, and the full 14-deck game (`fullPayoff` with payoffs WR/1000) in the latter. The payoff centering changes the absolute fitness values but should not change the replicator direction (since it's a constant shift to all payoffs). However, the `FullReplicator.lean` payoff is on [0, 1] while `EvolutionaryDynamics.lean` uses centered payoffs on [−500, +500]. Can you confirm that the replicator dynamics direction is invariant to this affine rescaling, and if so, is this verified in the artifact?

**Q3.** The paper claims Raging Bolt Ogerpon receives the largest Nash weight (28.7% row, 35.9% column), yet its expected field win rate is only 47.9% (Table IV, Tier C). This seems counterintuitive—the deck with the largest equilibrium weight has a below-average field win rate. Can you explain the strategic logic? Is this driven by Raging Bolt's extreme 67.3% counter against Mega Absol, which makes it indispensable for preventing Mega Absol domination despite poor performance against the broader field?

---

## 7. Scores

| Criterion        | Score (1–5) | Justification |
|------------------|:-----------:|---------------|
| **Novelty**      | 4 | First paper coupling a proof assistant with real TCG tournament data for equilibrium analysis. Not entirely novel in formal game theory, but novel in application domain and methodology. |
| **Technical Soundness** | 3 | Nash certification is correct; replicator claims are directionally sound but discrete/continuous conflation is a real issue. Type-alignment analysis has methodological gaps. Sensitivity analysis is external to Lean. |
| **Significance** | 3 | Methodological contribution is clear but impact is uncertain. The audience intersection of competitive game researchers and formal methods practitioners is small. The specific metagame results are ephemeral. |
| **Clarity** | 4 | Well-written, well-structured, honest about limitations. Some overstatement in abstract/introduction (2,500 theorems). The paper is too long (14 pages) and could be tightened. |
| **Reproducibility** | 4 | Artifact is comprehensive (30K lines, 80 files, zero sorry). The `native_decide` trust boundary is clearly documented. Python sensitivity analysis is external but included. Exact Lean toolchain version should be specified. |

---

## 8. Overall Recommendation

### **Weak Accept**

**Rationale:** This is a genuinely novel and ambitious paper that makes a clear methodological contribution: demonstrating that proof-carrying analytics is feasible for real competitive game ecosystems. The Nash equilibrium certification and the bug-catching case study are convincing. The writing is clear and the threat-to-validity analysis is among the most thorough I have seen in a game-analysis paper.

However, the discrete-time/continuous-time conflation (W1) is a real technical issue that must be addressed before publication, and the type-alignment bridge (W2) needs either strengthening or reframing. The "2,500 theorems" framing (W4) should be moderated. These are all fixable with a careful revision.

The paper sits at the intersection of formal methods and competitive game analysis in a way that is genuinely interesting, even if the immediate practical impact is limited. If the authors address the must-do revisions, particularly M1 (discrete/continuous separation) and M3 (type-alignment reframing), I would upgrade to Accept.
