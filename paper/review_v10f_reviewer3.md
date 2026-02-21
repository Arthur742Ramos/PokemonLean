# IEEE Transactions on Games — Final Review

**Submission:** #753 v10  
**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game  
**Reviewer:** 3 (Empirical Game Theory / Esports Analytics)  
**Date:** 2026-02-20  
**Review round:** Final (v10, 5th revision cycle)

---

## Recommendation: **Accept**

---

## Scores

| Criterion | Score (1–5) | Notes |
|---|---|---|
| **Novelty** | 4 | First proof-carrying metagame analytics pipeline for a real competitive game. The idea of coupling a theorem prover to empirical tournament data for strategic analysis is genuinely new. Not 5 because the game-theoretic tools (Nash via LP, replicator dynamics) are standard; the novelty is in the verification wrapper. |
| **Technical Quality** | 4 | 30K-line Lean artifact, ~2,500 theorems, zero sorry/admit/axiom. Nash equilibrium verified via saddle-point best-response checks over all 14 pure strategies. Sensitivity analysis (10K iterations) and worst-case robustness bounds are thorough. Deducted for the `native_decide` trust boundary—discussed honestly (Section IX) but structurally unavoidable given current Lean 4 kernel limitations with `Fin.foldl`. The matrix consistency theorem (`MatrixConsistency.lean`) and skill-sensitivity bounds (`SkillSensitivity.lean`) are particularly well-crafted additions that close prior review concerns cleanly. |
| **Significance** | 3 | The methodological contribution—demonstrating feasibility of formally verified empirical game theory—is significant for the community. The specific empirical finding (popularity paradox) is interesting but modest: experienced competitive players would recognize that "most popular ≠ best" is common in metagames. The significance is in *proving* it machine-checkably, not in the surprise of the result itself. Narrow scope (one game, one 3-week window) limits immediate impact. |
| **Clarity** | 5 | Exceptionally well-written for a paper with this much formal content. The trust boundary is stated explicitly and repeatedly. Verified vs. unverified claims are cleanly separated (Python sensitivity analysis clearly flagged as external). Tables, figures, and Lean listings are well-integrated. The end-to-end traceability case study (Section IX) is a model of exposition. |
| **Reproducibility** | 5 | `lake build` in ~10 min on commodity hardware. Full artifact included. Data provenance documented. This is among the most reproducible submissions I have reviewed for this venue. |

**Overall: 4.2 / 5**

---

## Assessment

### The Central Question: Does Narrow Scope Justify Rejection?

No. The paper's contribution is primarily **methodological**, and the authors state this clearly and repeatedly. The one-game, one-window empirical scope is a limitation, not a fatal flaw, for three reasons:

1. **The methodology is the contribution, not the Pokémon results.** The paper demonstrates that proof-carrying analytics is *feasible* for real competitive game ecosystems. This is a proof-of-concept that transfers to any domain with discrete strategies and measurable outcomes. Demanding multi-game, multi-season empirical breadth would be demanding a different paper.

2. **The robustness analysis is thorough enough to bound the scope limitation.** The worst-case "Other" analysis (Section X), share-perturbation theorems (`SharePerturbation.lean`), and skill-sensitivity bounds (`SkillSensitivity.lean`) collectively demonstrate that the headline results are not knife-edge artifacts of the particular snapshot. Dragapult needs ≥3.4pp uniform skill bias correction to reach 50%—a large and implausible confound.

3. **The 3-week window is explicitly bounded, not overclaimed.** The authors consistently frame results as properties of "this window" and provide falsifiable predictions (Section VII-A preliminary directional check), one of which already failed in an instructive way (Grimmsnarl declining due to Mega Absol predation cascade). This is honest science.

### What the Paper Does Well

- **Trust transparency is exemplary.** The `native_decide` boundary is documented with structural explanation (why `decide` is precluded, not just slow), count of affected theorems (244/2,500), and explicit risk characterization. This is the most honest treatment of a verification trust boundary I have seen in a games paper.

- **The type-alignment bridge (Section III-A) is clever.** Connecting the formalized type chart to empirical matchup outcomes (13/15 Dark→Psychic, 83% overall, p < 0.001 under binomial null) demonstrates that the rules layer is not merely decorative infrastructure—it generates falsifiable predictions. The explicit characterization of exceptions (N's Zoroark) strengthens rather than weakens the argument.

- **Equilibrium multiplicity is handled correctly.** The paper proves one Nash equilibrium, does not claim uniqueness, and uses sensitivity analysis to show core-support robustness (Grimmsnarl 96.5%, Raging Bolt 98.3% inclusion across resampled matrices). The symmetric Nash on the constant-sum symmetrization (Table V) provides a complementary cross-check with exact 500 game value.

- **The matrix consistency theorem** (`MatrixConsistency.lean`) closes a real engineering risk—that two representations of the same data could silently diverge across module boundaries. This is a contribution to proof engineering practice beyond the specific domain.

### Three Remaining Concerns

1. **The "Other" 30.5% segment remains a modeling gap, not just a robustness question.** The worst-case bounds show the paradox survives extreme assumptions, but the *equilibrium* analysis operates over a 14-deck subgame that excludes nearly a third of the field. If "Other" contains archetypes with strong anti-Grimmsnarl matchups, the Nash support could shift materially. The paper acknowledges this (Section X) and lists explicit modeling of "Other" as future work, which is adequate but leaves the equilibrium results more provisional than the expected-WR results. **Recommendation:** In the camera-ready, add one sentence to the Nash section explicitly stating that the equilibrium is conditional on the 14-deck subgame and may not be stable under field expansion. (This is implicit but should be explicit near Table IV.)

2. **The preliminary directional check (Section VII-A) is suggestive but methodologically weak.** Checking 3 predictions against "one day after" trend data is not a validation study—it is an anecdote. The Grimmsnarl failure actually demonstrates a real limitation (single-step replicator cannot capture multi-step cascades), which is valuable, but the framing as a "preliminary predictive check" overpromises. **Recommendation:** Reframe as "illustrative example of single-step limitations" rather than "predictive check."

3. **No discussion of between-tournament heterogeneity.** The 3-week window aggregates across multiple 50+ player events, but event-level variation (regional metagame differences, online vs. in-person, player pool overlap) is not analyzed. If two events have very different Dragapult win rates, the aggregate matrix masks meaningful strategic heterogeneity. This is a standard concern in empirical game theory that deserves at least a paragraph acknowledging the aggregation assumption. **Recommendation:** Add a brief discussion of event-level heterogeneity as a threat to validity.

---

## Disposition

The paper has been through five revision rounds and has addressed every substantive concern raised by this panel: length (now 12 pages), trust boundary transparency, equilibrium multiplicity, skill confounding, step-size invariance, matrix consistency, and verified/unverified separation. The artifact is real, buildable, and impressive in scope. The three remaining concerns above are camera-ready-level edits, not structural deficiencies.

The combination of (a) a genuinely novel methodology, (b) a rigorous and honest 30K-line formal artifact, (c) thorough robustness analysis, and (d) exemplary clarity and reproducibility meets the bar for IEEE Transactions on Games. The narrow empirical scope is a limitation the authors own transparently, and the methodological contribution stands independently of whether the Pokémon metagame shifts next week.

**Decision: Accept.**

---

*Reviewer 3 — Empirical Game Theory / Esports Analytics*
