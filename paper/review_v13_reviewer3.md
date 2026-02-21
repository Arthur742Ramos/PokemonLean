# IEEE Transactions on Games — Submission #753, Revision Round 3
## Reviewer 3 Report (v13)

**Reviewer expertise:** Proof engineering, Lean 4, formal verification, interactive theorem proving

**Date:** 2026-02-20

---

## Summary

This paper presents a formally verified metagame analysis of the competitive Pokémon TCG, using Lean 4 to machine-check game-theoretic claims (popularity paradox, Nash equilibrium, replicator dynamics) over real tournament data. The artifact spans ~30K lines, 81 files, and ~2,500 theorems with no `sorry`/`admit`/custom axioms. v13 addresses several concerns from prior rounds: qualifying uniqueness of Nash claims, renaming "algebraic sufficiency" to "numerical sufficiency," replacing the causal arrow-chain with four independent facts, clarifying Dragapult's non-domination status, specifying StepSizeGeneral tactics, and aligning conclusion language with `native_decide` precision.

---

## Criteria Scores

### 1. Novelty: 4/5

The idea of applying proof-carrying formal verification to empirical metagame analytics is genuinely novel. No prior work I'm aware of connects a full tournament matchup matrix to machine-checked Nash equilibrium certification and replicator dynamics classification in a proof assistant. The methodological template—encode data as exact constants, express claims as theorems, verify with decision procedures—is portable and well-articulated.

The deduction is for the underlying game theory being entirely standard (finite bimatrix Nash, textbook replicator dynamics, Bo3 amplification). The novelty is squarely in the *verification methodology*, which the paper now correctly emphasizes.

### 2. Technical Soundness: 3/5

This is the axis where v13 has improved most but where substantive concerns remain.

**Improvements acknowledged:**
- The Nash uniqueness qualification is now explicit and properly scoped ("uniqueness is not proven; other equilibria may differ"). This was a critical fix.
- "Numerical sufficiency" is honest about what the inequality actually proves—a concrete numerical bound, not an algebraic derivation from abstract principles.
- The four independent facts replacing the arrow-chain are a significant improvement. The paper now correctly states these are "mutually consistent" layers rather than a causal derivation.
- `CausalChain.lean` being "named for historical reasons" is acceptable but mildly irritating—renaming files is cheap and would eliminate reader confusion.
- The StepSizeGeneral tactics (`simp`, `ring`, `omega`) providing kernel-level assurance for sign-invariance is a genuine verification win and one of the strongest results in the paper.

**Remaining concerns:**

**(a) The `native_decide` concentration is a real trust gap.** 244 of ~2,500 theorems use `native_decide`, but these 244 are *all* the game-theoretically interesting ones: Nash equilibrium verification, replicator dynamics classification, bridge alignment theorems. The paper is commendably transparent about this (Section IX), and the structural explanation for why `decide` is precluded (`Fin.foldl` opacity) is convincing. However, this means the paper's headline claims—the Nash equilibrium, the replicator fitness ordering, the best-response checks—rest on trusting Lean 4's compiler pipeline rather than on kernel-verified proof terms. The paper correctly notes "no defense in depth for the game-theoretic core." I appreciate the honesty, but this is a genuine limitation for a paper whose raison d'être is formal verification. The abstract's qualification "modulo the `native_decide` trust boundary" is appropriate but easy to miss.

**(b) The 83% type-alignment figure depends on modeling choices the paper cannot formally validate.** The type assignments are "domain-expert modeling choices, not formally derived from deck composition." The paper is now transparent about this, but the rhetorical weight placed on the 83% alignment (including a binomial p-value) sits uneasily with the fact that the assignments are chosen by the authors. A skeptic could argue this is a semi-circular validation: the authors chose assignments that they expected to align, then verified the alignment. The paper's defense—that random assignments would yield ~50%—is reasonable but not dispositive. I'd want to see at least one sensitivity analysis: what happens if borderline assignments (e.g., Dragapult Charizard) are flipped?

**(c) The sensitivity analysis is external to the verified artifact.** The 10,000-iteration resampling analysis (Table I) is produced by an unverified Python script. The paper acknowledges this clearly, but the rhetorical structure leans heavily on these results (77.9% Dragapult exclusion, 96.5% Grimmsnarl inclusion) for robustness arguments. For a paper whose thesis is "formal verification transforms narratives into machine-checkable science," relying on unverified Python for the robustness story is a tension the authors should acknowledge more forthrightly. The future work mention of verified interval arithmetic over the LP is appreciated but currently vaporware.

**(d) The replicator dynamics are single-step only.** The paper is now clear about this limitation and even provides an honest empirical check (Section VII-A) where Grimmsnarl's predicted rise was contradicted by Mega Absol's counterpredation. This is good scientific practice. However, single-step replicator dynamics over a discrete Euler step are a very weak predictive tool—they tell you the instantaneous gradient direction, not the trajectory. The paper appropriately calls these "directional diagnostics" but still uses language like "predict Dragapult decline" and "Grimmsnarl dominance" in the abstract and conclusion, which overstates what a single-step result can establish.

### 3. Significance: 3/5

The methodological contribution—demonstrating feasibility of proof-carrying metagame analytics—is real and has potential impact. The template is portable. However:

- The specific results (Dragapult is overplayed, Grimmsnarl is underplayed) are unsurprising to anyone who has looked at the matchup data. The paper acknowledges this ("the headline popularity paradox could be computed in a spreadsheet") but then needs the verification methodology to carry the significance argument.
- The practical impact is limited: competitive players will not adopt 30K-line Lean artifacts for deck selection. The paper correctly frames this as a research contribution, not a practical tool.
- The verification catches real errors (the matrix data-entry story in Section IX is compelling), but the cost-benefit table (Table VII) makes the case that Python + scipy at ~100 LoC provides adequate guarantees for most practitioners.

For IEEE Transactions on Games, the significance is borderline: the game-theoretic content is standard, and the formal verification content, while novel in application, is primarily an engineering achievement rather than a conceptual advance in either game theory or proof engineering.

### 4. Clarity: 4/5

v13 is well-written for a paper spanning formal verification and competitive gaming. The structure is logical, the notation is consistent, and the Lean code excerpts are well-chosen and readable.

Specific praise:
- The trust boundary discussion (Section IX) is exemplary in its honesty.
- The case study tracing a headline claim end-to-end (Section IX-F) effectively illustrates the methodology's value.
- The threats-to-validity section is thorough and well-calibrated.

Remaining clarity issues:
- The paper is long. At ~970 lines of LaTeX plus substantial code listings, it pushes the limits of a journal submission. Some compression is possible in Section III (game formalization) and Section IV (probability), which are more infrastructure than contribution.
- The `CausalChain.lean` naming issue should just be fixed. "Named for historical reasons" reads as technical debt that made it into the paper.
- The footnote about the `GrimssnarlFroslass` typo is charming but shouldn't be necessary in a final version.
- The index mapping (0-based `Deck.toFin`) interrupts the Nash equilibrium discussion. A supplementary table would suffice.

### 5. Reproducibility: 5/5

This is the paper's strongest axis, and appropriately so given the thesis. The artifact is self-contained: `lake build` on specified hardware reproduces all claims. The zero-sorry/zero-admit/zero-axiom standard is met. Data provenance is documented. The Python sensitivity analysis script is included (though external to the verified core). The one-to-one mapping between paper claims and named theorems is excellent reproducibility practice.

The `MatrixConsistency.lean` cross-representation check is a nice touch that eliminates a real class of bugs.

---

## Detailed Comments

1. **Abstract, line "A machine-checked Nash equilibrium with six-deck support assigns Dragapult 0% weight"**: The parenthetical about uniqueness is good but could be more prominent. Consider: "A machine-checked Nash equilibrium (one of potentially many) with six-deck support..."

2. **Section V-B (Type alignment)**: The `hasTypeAdvantage` function is clean, but the claim "13 of 15 pairs" for Dark→Psychic alignment should note the denominator: 3 Dark attackers × 5 Psychic defenders = 15 pairs. This is implicit but would help the reader.

3. **Section VII (Nash)**: The saddle-point verification is stronger than bimatrix best-response—good. But the paper should note explicitly that this implies Nash equilibrium *of the zero-sum game defined by the row player's payoff matrix*, which is subtly different from Nash equilibrium of the full bimatrix game when the game is not exactly constant-sum. The symmetric Nash on the constant-sum symmetrization (Table IV) partially addresses this.

4. **Section VII, replicator dynamics**: The `full_replicator_grimmsnarl_fittest` theorem is a universal quantifier over `Fin 14`—machine-checked universal quantification over a finite domain via `native_decide`. This is sound but should be distinguished from the general symbolic result in `StepSizeGeneral.lean` which achieves kernel-level assurance. The paper makes this distinction but could be sharper.

5. **Section IX-C**: "A hypothetical bug in Lean 4's code generator affecting rational arithmetic over `Fin.foldl` could simultaneously invalidate all 244 `native_decide` proofs." This is the most important sentence in the paper for the formal verification audience. I would promote it to the abstract or introduction.

6. **Table VI (Methodology comparison)**: The "verified*" asterisk with the `native_decide` caveat is honest but easy to overlook. Consider adding a row for "Lean 4 (kernel-only)" with "infeasible (Fin.foldl)" in the guarantee column to make the gap explicit.

7. **Section X (Threats)**: The skill-confounding analysis (3.4pp threshold) is well-done. The 6.1pp Grimmsnarl-matching threshold is a strong robustness argument. However, the claim that "within-event skill differentials between top-quartile and bottom-quartile finishers are unlikely to exceed 5 percentage points" is stated as domain expertise, not a verified bound. This is fine—not everything can be formalized—but could be flagged as an unverified assumption.

8. **The "preliminary directional check" (Section VII-A)**: This is honest and valuable. The Grimmsnarl failure is exactly the kind of result that should appear in a rigorous paper. More of this empirical humility would strengthen the paper.

9. **Section III (Game Formalization)**: The `professorsResearchEffect_preserves_cards` theorem is a nice illustration but its connection to the metagame analysis pipeline is tenuous. The paper claims it "prevents subtle bookkeeping bugs from distorting probability estimates," but no probability estimate in the paper actually depends on this theorem. Consider being explicit about whether this is future-proofing infrastructure or a live dependency.

10. **Data window (Jan 29 – Feb 19, 2026)**: Three weeks is short. The paper's temporal locality caveat is appropriate, but the shortness of the window combined with the claim of "persistent property of the underlying strategic landscape" (Section X) is a tension. The robustness-to-share-perturbation argument is clever but doesn't address whether the *matchup matrix itself* is stable across windows.

---

## Minor Issues

- The `Deck.toFin` mapping should be in a supplementary appendix, not inline.
- Wilson interval formula: the paper presents it correctly but the "center adjustment" phrasing may confuse readers unfamiliar with Wilson's method. Consider just calling it "Wilson score interval."
- The replicator dynamics equation uses continuous-time notation ($\dot{x}_i$) but the implementation is discrete-time Euler. The paper acknowledges this but could present the discrete-time equation directly.
- Reference [1] (moura2021lean) should be checked for the correct publication year/venue.

---

## Overall Assessment

v13 represents substantial improvement over earlier versions. The authors have been responsive to criticism: the Nash uniqueness qualification, the numerical sufficiency rename, the arrow-chain decomposition, and the `native_decide` trust boundary discussion all address real problems that were raised in previous rounds. The paper is honest about its limitations to a degree that is uncommon and commendable.

The core tension remains: this is a paper about formal verification whose game-theoretically interesting results all rest on `native_decide` rather than kernel-checked proofs. The paper is transparent about this, but it weakens the verification story. The methodological novelty is real—nobody has done this before for a competitive TCG—but the specific results are not surprising, and the practical impact is limited by the enormous engineering cost relative to the analytical output.

The paper is above the acceptance threshold for IEEE Transactions on Games on the strength of its methodological novelty, reproducibility, and honest treatment of limitations, but it does not clear the bar comfortably. The `native_decide` trust concentration, the external Python sensitivity analysis, and the limited significance of the game-theoretic findings (standard techniques, unsurprising results) are genuine weaknesses that the verification methodology, however well-executed, does not fully compensate for.

---

## Recommendation: **Weak Accept**

The paper demonstrates a genuinely novel application of formal verification to competitive game analytics, with exemplary transparency about trust boundaries and limitations. The artifact quality is high, the reproducibility is excellent, and the writing is clear. However, the reliance on `native_decide` for all core results, the external (unverified) sensitivity analysis, and the limited game-theoretic novelty prevent a stronger recommendation. I would support acceptance if the authors:

1. Rename `CausalChain.lean` to something accurate (trivial fix, removes distraction).
2. Add a sentence to the abstract noting the `native_decide` trust boundary more prominently.
3. Explicitly characterize which results have kernel-level assurance (StepSizeGeneral) vs. compiler-trust assurance (`native_decide`), perhaps in a summary table.

These are minor revisions that would not require a new review round.

| Criterion        | Score |
|------------------|-------|
| Novelty          | 4/5   |
| Technical Sound. | 3/5   |
| Significance     | 3/5   |
| Clarity          | 4/5   |
| Reproducibility  | 5/5   |
| **Overall**      | **Weak Accept** |
