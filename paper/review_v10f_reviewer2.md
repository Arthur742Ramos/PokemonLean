# IEEE Transactions on Games — Reviewer 2 (Final Review)

**Submission:** #753 v10  
**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game  
**Date:** 2026-02-20  
**Reviewer expertise:** Formal methods, interactive theorem proving, mechanized game theory  
**Review round:** Final (v10, 5th revision cycle)

---

## Scores

| Criterion        | Score (1–5) | Comment |
|-------------------|:-----------:|---------|
| Novelty           | 4           | First proof-carrying metagame analytics pipeline for a real competitive game; methodological contribution is genuine. |
| Technical         | 4           | 31K LoC, ~2500 theorems, zero sorry/admit; Nash certification over 14 strategies is non-trivial. Trust boundary clearly disclosed. |
| Significance      | 3           | Metagame results are snapshot-specific; lasting value is the reusable methodology, which is well-argued but not yet replicated on a second domain or dataset window. |
| Clarity           | 4           | Paper reads cleanly for a mixed audience. Trust boundary section is exemplary for a non-PL venue. Tier labeling and scatter plot are effective. |
| Reproducibility   | 5           | `lake build` on released artifact; all constants traceable; cross-module consistency theorem prevents drift. Gold standard for this venue. |

---

## Recommendation: **Accept**

After five revision rounds and careful examination of both the manuscript and the Lean artifact (85 files, 31K lines), I am satisfied that this paper meets the bar for IEEE Transactions on Games and recommend **Accept**.

---

## Rationale for decisive Accept (not Weak Accept)

Previous rounds converged on Weak Accept, with concerns around (a) trust-boundary transparency for `native_decide`, (b) the gap between rules formalization and empirical claims, and (c) robustness of the Nash equilibrium to data uncertainty. Version 10 addresses all three decisively:

1. **Trust boundary disclosure (§IX).** The paper now gives a precise count (244 of ~2500 theorems use `native_decide`), explains *why* `decide` is structurally precluded (`Fin.foldl` opacity to the kernel reducer), and explicitly states the correlated-failure risk. For a games venue—not POPL—this level of disclosure exceeds what I would expect and is more honest than most "verified" claims in ML/AI papers. The footnote on Table VII ("modulo `native_decide`") is a nice touch.

2. **Rules-to-data bridge (§III-B).** The type-alignment analysis (13/15 Dark→Psychic matchups confirmed, 83% overall, binomial p < 0.001) transforms the rules layer from dead-weight formalization into a falsifiable prediction engine. The explicit counterexample (`type_advantage_not_sufficient` for N's Zoroark) is the kind of honest negative result that strengthens rather than weakens the contribution.

3. **Sensitivity analysis (§V, Table I).** The 10,000-iteration resampling study, while external to Lean, is properly flagged as unverified and complements the formal results well. Core support decks (Grimmsnarl 96.5%, Mega Absol 97.3%, Raging Bolt 98.3%) are stable; Dragapult exclusion holds in 77.9% of iterations. The paper correctly notes that embedding this in Lean via verified interval arithmetic is future work.

4. **Symmetric Nash cross-check (§VII, Listing 2, Table IV).** The constant-sum symmetrization with game value exactly 500 and seven-deck support is a clean robustness device. Dragapult receiving 0% in both formulations is compelling.

5. **Artifact quality.** I verified: zero `sorry`/`admit` matches in source (the grep hits are in documentation comments stating their absence); `native_decide` count (~292) is consistent with the paper's claim of ~244 direct uses plus downstream transitive calls; the `MatrixConsistency.lean` cross-module check and `StepSizeGeneral.lean` symbolic lemma are genuine proof engineering, not boilerplate.

The combination of a novel methodology, a substantial and honest artifact, and domain relevance to the ToG readership justifies acceptance. The paper is not perfect, but after five revisions the remaining issues are minor and do not warrant another round.

---

## Three Remaining Concerns

These are noted for the camera-ready but do not block acceptance.

### 1. `native_decide` concentration risk remains a soft ceiling on assurance claims

The paper is admirably transparent, but the reader should understand that *all* game-theoretic core results (Nash, replicator, bridge alignment) flow through the same unverified compilation path. If a `native_decide` soundness bug existed in Lean 4's code generator for rational arithmetic over `Fin.foldl`, it would invalidate the entire strategic layer simultaneously. The paper says this; I want the camera-ready to add one sentence in the abstract or introduction qualifying "formally verified" with a parenthetical forward-reference to §IX (currently only in the abstract as a parenthetical to §IX—good, but easy to miss). **Suggested wording:** "...formally verified (modulo the `native_decide` trust boundary; §IX)..." — I see this is already present. Satisfactory.

### 2. No temporal replication

The three-week snapshot is acknowledged as a limitation. The preliminary directional check (§VII subsection) is honest about the Grimmsnarl miss due to cascade effects. For the camera-ready, I would appreciate one sentence stating whether a second snapshot (e.g., the following three-week window) has been attempted or is planned, and whether the `lake build` pipeline can ingest new data with only constant-file changes. This would strengthen the "reusable methodology" claim.

### 3. The 30.5% "Other" exclusion

The worst-case bounds (Dragapult needs ≥57.6% vs Other to reach 50% overall) are convincing for the popularity paradox, but the Nash equilibrium is computed only over the 14-deck subgame. If "Other" contains a strategy that dominates the Nash support, the equilibrium is meaningless for full-field play. The paper should add one sentence to §VII explicitly noting that the Nash equilibrium is conditional on the 14-deck subgame and would need re-verification if "Other" were decomposed. (This is implicit but should be explicit for readers unfamiliar with subgame reasoning.)

---

## Minor / Editorial

- The identifier `GrimssnarlFroslass` (single-m, double-s) is noted in a footnote—fine, but consider a Lean `abbrev` alias for the camera-ready to reduce reader confusion in code listings.
- Table III caption: "Uniqueness is not proven" is appropriately stated. Consider adding "and is not expected to hold generically for bimatrix games" for completeness.
- The Bo3 independence assumption (§VIII) is more defensible for Pokémon TCG than for Magic or Yu-Gi-Oh due to lack of sideboarding—this is well-argued and I have no objection.

---

## Summary

This is a methodologically novel paper that introduces proof-carrying analytics to competitive game science, backed by a substantial and reproducible artifact. The trust boundary is disclosed with unusual honesty, the empirical results are robust to multiple sensitivity checks, and the writing quality is appropriate for the venue. After five rounds of revision, the paper has earned acceptance.

**Final recommendation: Accept.**
