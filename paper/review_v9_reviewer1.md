# Review of Submission #753 v9 — IEEE Transactions on Games

**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game

**Reviewer:** Reviewer 1 (Game Theory specialist)  
**Date:** 2026-02-20  
**Version reviewed:** v9 (12 pages, 8 Lean source files examined)

---

## Summary

The paper presents a Lean 4–verified metagame analysis of the competitive Pokémon TCG, covering a 14-archetype matchup matrix sourced from Trainer Hill (Jan–Feb 2026). The main claims are: (1) a "popularity paradox" where the most-played deck (Dragapult, 15.5% share) has sub-50% expected win rate while Grimmsnarl (5.1%) achieves the field maximum; (2) a machine-checked Nash equilibrium (six-deck support, 0% Dragapult) and a symmetrized constant-sum variant (seven-deck support, game value exactly 500); (3) full 14-deck replicator dynamics classifying 5 growers and 9 shrinkers; and (4) skill-sensitivity bounds quantifying confound thresholds.

V9 changes include a general symbolic step-size invariance proof over `Int`, a `native_decide` caveat in the abstract, tightened Dragapult suboptimality scope, contextualized sensitivity thresholds against empirical skill-gap ranges, explicit labeling of the Python sensitivity table as unverified, and removal of all `optimize_proof` macros.

---

## Scores

| Criterion        | Score (1–5) | Rationale |
|------------------|:-----------:|-----------|
| **Novelty**      | 4 | First proof-carrying metagame analytics pipeline for a real TCG; the methodology is genuinely new even if the game-theoretic tools are standard. |
| **Technical**    | 3 | The equilibrium verification is sound for the stated matrix but the `native_decide` monoculture, the unverified sensitivity analysis, and the absence of propagated uncertainty through the Nash computation collectively weaken the technical floor. |
| **Significance** | 3 | Methodologically significant as a proof of concept; limited competitive-strategic impact, which the authors acknowledge. The template is portable but the specific findings are temporally narrow. |
| **Clarity**      | 4 | Well-organized, honest about limitations, and the traceability from prose to theorem names is exemplary. Minor notation inconsistencies remain (see below). |
| **Reproducibility** | 5 | Outstanding. Named theorems, `lake build` instructions, exact rational constants, cross-module consistency checks. Best-in-class for this venue. |

---

## Detailed Assessment

### A. Equilibrium Argument: Is It Complete?

**Mostly yes, with a scoping caveat.** The Nash equilibrium for the bimatrix game is correctly certified: `real_nash_equilibrium_verified` checks the saddle-point condition (all 14 row best-response inequalities and all 14 column best-response inequalities) via `native_decide`. The symmetric variant on the constant-sum symmetrization confirms the qualitative picture (Dragapult excluded, game value 500). The `DragapultDominated.lean` file tightens scope appropriately: Dragapult is strictly suboptimal *against this particular column strategy*, not against all possible equilibrium column strategies — a correction the paper now states clearly.

**Remaining gap 1: Equilibrium uniqueness.** The paper proves *an* equilibrium, not *the* equilibrium. The sensitivity analysis (77.9% exclusion of Dragapult across 10k resampled matrices) provides empirical evidence but not a formal guarantee. The paper should state whether uniqueness is conjectured or known to be false for this matrix, and whether the LP has degenerate vertices. For an approximately constant-sum 14×14 game, the equilibrium is generically unique but degeneracy in the Trainer Hill matrix is not ruled out.

**Remaining gap 2: The NashEquilibrium definition uses a zero-sum/saddle-point condition** (row payoffs ≤ value ≤ column payoffs), which is *stronger* than the general bimatrix best-response condition. The paper correctly notes this implies Nash in both senses, but the `FiniteGame` structure carries a vestigial `payoff` field (always set to `fun _ _ => 0`) that is never used. This is harmless but confusing — it suggests the formalization was initially designed for a richer game model that was never completed. The `NashEquilibrium` predicate is really a minimax/saddle-point predicate, and calling it `NashEquilibrium` in a bimatrix context may mislead readers expecting the standard bimatrix definition (each player's strategy is a best response to the other's). The paper should add a one-line remark that the two coincide for the (approximately) zero-sum case.

### B. Step-Size Symbolic Proof: Is It Satisfying?

**Yes, this is a genuine improvement over v8.** `StepSizeGeneral.lean` proves `replicator_sign_independent_of_dt` and `replicator_decline_independent_of_dt` as general symbolic lemmas over `Int`, using clean auxiliary sign-extraction lemmas (`pos_of_mul_pos_of_pos_pos`, etc.). The proof is elementary but correct: since `δ_i = x_i · dt · (f_i − f̄)`, positivity of `x_i` and `dt` means the sign is determined entirely by `f_i − f̄`.

**Minor critique:** The proof works over `Int`, which the paper justifies as "rational dynamics are recovered by clearing denominators." This is true but the connection is informal — there is no Lean lemma explicitly bridging the `Int` sign result to the `Rat`-valued replicator step used in `FullReplicator.lean`. The concrete `StepSizeInvariance.lean` verifications (dt = 1/10, 1/100, 1) provide empirical confirmation but the formal bridge theorem is missing. This is not a soundness issue (the algebraic argument is trivially correct) but it is an elegance gap in a paper whose central selling point is formal completeness.

### C. Remaining Gaps

1. **Sensitivity analysis is entirely outside the trust boundary.** Table II (10,000-iteration resampling) is produced by an unverified Python script. The paper now correctly labels this, but the Nash equilibrium fragility (exact support recovered in only 2.1% of iterations) is a significant finding that deserves formal treatment. At minimum, the authors should verify one perturbed matrix endpoint (e.g., all cells at their Wilson lower bound) to show the equilibrium structure survives worst-case perturbation within Lean.

2. **Replicator dynamics: single-step only.** All verified replicator results are single-step directional claims. The paper acknowledges this and the predictive validation section (Section VII-A) honestly reports a failed Grimmsnarl prediction due to multi-step cascading. However, the gap between "one-step direction" and "metagame prediction" is larger than the paper's framing suggests. Iterated dynamics are verified for toy 3–5 deck subsystems but not for the full 14-deck game. Since multi-step iteration over 14 decks with exact rationals is computationally expensive, I recommend the authors verify at least 3–5 iterated steps on the full system, or prove a monotonicity result for Dragapult's decline over iterated steps.

3. **The "Other" segment.** The 30.5% unmodeled field is handled via worst-case bounds (Section X), which is adequate but coarse. The bounds show Dragapult needs ≥57.6% vs. Other to reach 50% overall — but the paper does not check whether any *equilibrium-relevant* conclusion (e.g., Dragapult exclusion from Nash support) survives when Other is modeled as a 15th "average" strategy. This would be a straightforward extension.

4. **Skill-sensitivity contextualization (v9 change).** The 3.4pp and 6.1pp thresholds are now contextualized against "2–5 percentage points between top-quartile and bottom-quartile finishers." This is helpful but the cited range is unsourced — no reference is provided for this empirical claim. If this is the authors' estimate, it should be flagged as such; if from the literature, it needs a citation.

---

## Must-Do Revisions

1. **Bridge the `Int`-level step-size invariance proof to the `Rat`-level replicator dynamics with an explicit Lean lemma.** Currently `StepSizeGeneral.lean` proves sign invariance over `Int` and `FullReplicator.lean` operates over `Rat`, but no theorem connects them. Adding a corollary like `replicator_sign_independent_of_dt_rat` that applies the `Int` result to the actual `Rat`-valued fitness delta would close the formal gap and make the general proof actually *used* by the concrete dynamics, rather than existing as a parallel artifact.

2. **Provide a source or explicit qualification for the "2–5 percentage points" skill-gap range** cited in Section X. This claim is doing significant epistemic work (it's the basis for arguing that 3.4pp is implausibly large) and must either be cited to published data on competitive TCG skill differentials or clearly flagged as an authorial estimate. Without grounding, the contextualization added in v9 is as much narrative as the claims it aims to discipline.

3. **Verify at least one perturbed-matrix Nash equilibrium within Lean** (e.g., all matchup cells shifted to their Wilson 95% lower or upper bounds) to provide a single formally verified robustness data point that complements the unverified Python sensitivity analysis. This would partially close the gap between the paper's strongest claims (machine-checked) and its robustness evidence (Python-only).

---

## Questions for the Authors

**Q1.** The `NashEquilibrium` predicate uses a saddle-point formulation that is strictly stronger than the standard bimatrix best-response condition. Was this choice made for computational convenience (`native_decide` over a conjunction of universal quantifiers), or does it reflect a deliberate modeling decision? If the former, have you verified that the standard bimatrix definition (∀ alternative row strategies s₁', expectedPayoff(s₁', s₂) ≤ expectedPayoff(s₁, s₂), and symmetrically for columns) also holds? The saddle-point formulation is equivalent for zero-sum games but the paper repeatedly notes the matrix is *not* exactly zero-sum.

**Q2.** Raging Bolt Ogerpon has the highest Nash weight (28.7% row, 35.9% column) yet its observed expected win rate is only 47.9% (Tier C). The paper discusses Dragapult's paradox extensively but says little about this inverse paradox — a deck that is unpopular and low-EWR in the current meta yet dominates equilibrium play. Can you provide intuition for why the Nash solution loads so heavily on Raging Bolt? Is it functioning as a "kingmaker" counter (67.3% vs. Mega Absol) whose value emerges only in the equilibrium mixture?

**Q3.** The `FiniteGame` structure has fields `n` (number of players), `m` (strategies), `payoff`, and `matrix`, but `n` is always 2 and `payoff` is always `fun _ _ => 0`. The `matrix` field carries all the strategic content. Is this structure inherited from an earlier generalization attempt? If so, does the vestigial `payoff` field ever interact with `native_decide` performance (e.g., by inflating the decidability witness)? Cleaning this up would reduce reviewer confusion about what the formal model actually captures.

---

## Recommendation

**Weak Accept.**

The paper makes a genuine and novel methodological contribution: it is the first proof-carrying metagame analytics pipeline applied to real tournament data in a competitive card game. The v9 changes are responsive and improve the paper materially — the general step-size proof is satisfying, the `native_decide` caveat is honest, the Dragapult suboptimality scoping is now correct, and the sensitivity table labeling is appropriate. The equilibrium argument is complete for the stated game; the main residual weakness is the gap between verified point-estimate claims and unverified robustness evidence. The three must-do revisions are tractable and would move the paper to a clear Accept.

The paper's contribution is primarily methodological, which is appropriate for IEEE Transactions on Games, but the game-theoretic content itself (Nash equilibrium of a single empirical matrix, single-step replicator dynamics) is standard. What elevates this above a routine application paper is the demonstration that formal verification is *feasible* and *catches real errors* in this domain — the anecdote about `native_decide` catching matrix data-entry errors during development is particularly compelling. The reproducibility standard is exceptional.

---

*Reviewer 1 — Game Theory Specialist*
