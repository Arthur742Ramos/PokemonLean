# Review: IEEE Transactions on Games Submission #753 (v13, Revision Round 3)

**Reviewer 1 — Game Theory / Equilibrium Computation / Evolutionary Dynamics**

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Date:** February 20, 2026

---

## Summary

The paper presents a formally verified metagame analysis of the Pokémon TCG, using Lean 4 to machine-check game-theoretic claims (Nash equilibrium existence, replicator dynamics directions, expected value computations) over a 14-archetype matchup matrix derived from tournament data. The central empirical finding is a "popularity paradox": the most-played deck (Dragapult, 15.5% share) has a sub-50% expected win rate, while a less-played deck (Grimmsnarl, 5.1% share) achieves the highest fitness. The primary contribution is framed as methodological—demonstrating that proof-carrying analytics is feasible for competitive game ecosystems.

---

## Scores

| Criterion | Score (1–5) | Comments |
|---|---|---|
| **Novelty** | 3 | See below |
| **Technical Soundness** | 3 | Improved but persistent gaps |
| **Significance** | 3 | Methodological demo is interesting; game-theoretic depth is limited |
| **Clarity** | 4 | Substantially improved from v12 |
| **Reproducibility** | 4 | Strong artifact; `native_decide` caveat well-documented |

---

## Detailed Assessment

### Novelty (3/5)

The novelty sits at the intersection of formal verification and empirical game theory applied to TCGs. This intersection is genuinely underexplored, and the paper deserves credit for pioneering it. However, the game-theoretic content itself is standard: computing a Nash equilibrium of a finite matrix game via LP, checking best-response conditions, and running one-step replicator dynamics. None of these are methodologically novel from a game theory perspective. The novelty is purely in the verification wrapper. The question for the reader is whether wrapping known computations in Lean constitutes sufficient novelty for a top venue. I lean toward "conditionally yes"—but the paper would benefit from engaging more deeply with the game theory literature on equilibrium refinement and selection, especially given the uniqueness gap (see below).

### Technical Soundness (3/5)

**Improvements in v13 acknowledged.** The authors have made meaningful corrections since v12:

1. **Nash uniqueness qualification.** The abstract and body now correctly state "uniqueness is not proven; other equilibria may differ." This is a critical fix. The v12 phrasing risked implying Dragapult's exclusion was equilibrium-necessary rather than equilibrium-consistent.

2. **"Algebraic sufficiency" → "Numerical sufficiency."** Honest relabeling. The inequality is over concrete constants, not a symbolic/algebraic result. Good.

3. **Arrow-chain → numbered facts.** The old causal narrative was misleading. The new framing ("four independently verified facts... not that any one causes the next") is epistemically much cleaner.

4. **Domination clarification.** Correctly noting Dragapult is NOT strictly dominated (64.1% vs Charizard) is important. The v12 text left ambiguity about whether domination could close the uniqueness gap; v13 explicitly states it cannot.

**Remaining concerns:**

(a) **The uniqueness gap is the elephant in the room.** The paper proves existence of *a* Nash equilibrium excluding Dragapult, not that *all* equilibria do so. The 14×14 game could have many equilibria, some potentially including Dragapult with positive weight. The paper acknowledges this but does not attempt any equilibrium refinement (trembling hand, proper equilibrium, etc.) or even a computational enumeration of equilibria. For a game theory venue, this is a significant gap. The sensitivity analysis (77.9% Dragapult exclusion across resampled matrices) is helpful but addresses measurement noise, not equilibrium multiplicity within a fixed matrix.

**Recommendation:** At minimum, discuss why equilibrium enumeration (e.g., via the Lemke-Howson algorithm or support enumeration) was not attempted. For a 14×14 game, full enumeration of Nash equilibria is computationally feasible. If uniqueness could be established computationally (even if not formally verified), it would dramatically strengthen the paper's claims.

(b) **Replicator dynamics are single-step only.** The paper is transparent about this (discrete Euler steps, directional pressure only), which is good. But the preliminary directional check (Section VII-B) reveals the fundamental limitation: Grimmsnarl declined despite being predicted as highest-fitness, because Mega Absol's rise created predation pressure. This is not a minor caveat—it demonstrates that the single-step analysis can give qualitatively wrong predictions even one day out. The paper frames this as "illustrating a limitation" but it actually undermines the predictive value of the evolutionary analysis.

The sign-invariance result (`replicator_sign_independent_of_dt`) is correct but trivially so—it follows immediately from the definition of discrete replicator dynamics. Elevating this to a named theorem with kernel-level verification feels like over-engineering a tautology. The `simp`, `ring`, `omega` tactic specification is appreciated for transparency but doesn't change the mathematical content.

(c) **The `native_decide` trust boundary.** The paper is now admirably transparent about this (Section IX), including the structural preclusion of `decide` due to `Fin.foldl` opacity. The 244-theorem concentration risk is well-stated. However, this means the *entire* game-theoretic core (Nash verification, replicator dynamics, bridge alignment) rests on trusting the Lean compiler's code generation. For a paper whose headline contribution is "machine-checked" guarantees, this is an inherent tension. The paper handles it well editorially but the reader should understand that "formally verified" here means "verified modulo native code compilation," not "kernel-checked."

(d) **Constant-sum assumption.** The bimatrix game is approximately but not exactly constant-sum. The paper correctly handles this by verifying both the asymmetric and symmetric Nash equilibria. However, the game value of the asymmetric equilibrium (≈47.97%) being sub-50% is a direct consequence of the tie convention, not a strategic insight. The paper explains this but could be more concise about it.

(e) **Type assignment subjectivity.** The 83% alignment rate between type chart predictions and empirical matchup directions depends entirely on domain-expert type assignments. The paper now acknowledges these are "modeling choices, not formally derived from deck composition"—good. But the statistical test (binomial p < 0.001 under random assignment) is weak: random assignment is not the relevant null hypothesis. A more appropriate null would be informed assignment with noise, or permutation within type-ambiguous archetypes.

### Significance (3/5)

The methodological contribution—showing that proof-carrying analytics is feasible for real competitive games—is genuinely interesting and, to my knowledge, novel at this scale. The 30K-line Lean artifact is impressive engineering.

However, the specific game-theoretic insights are modest:
- The popularity paradox (most-played deck is suboptimal) is interesting but not surprising to game theory audiences—it's a standard feature of boundedly rational populations.
- The Nash equilibrium computation is a solved problem; the verification adds assurance but no new theory.
- The replicator dynamics analysis provides only directional claims that, as demonstrated by the paper's own predictive check, can fail within one day.

The paper would be more significant if it used the formal verification infrastructure to prove something that would be genuinely hard to trust without verification—e.g., properties of the equilibrium set, or robustness guarantees that require symbolic reasoning over parameterized matrices. The "numerical sufficiency" result gestures in this direction but remains a computation over concrete constants.

### Clarity (4/5)

This is the strongest dimension and shows significant improvement over v12. Specific positives:

- The numbered-facts framing replacing the arrow-chain narrative is much clearer about what is and isn't being claimed.
- The trust boundary discussion in Section IX is exemplary in its honesty.
- The Wilson interval discussion and sensitivity analysis are well-presented.
- Table and figure quality is good throughout.

Minor clarity issues:
- The `CausalChain.lean` "named for historical reasons" note is slightly awkward—consider renaming the file in the artifact before camera-ready.
- The paper is long for the depth of game-theoretic content. Some of the Lean listing inclusions (e.g., `professorsResearchEffect_preserves_cards`) could be moved to supplementary material without loss.
- The behavioral-economic interpretation (Section VI-B) is speculative and adds little beyond citing standard references. It could be shortened to a paragraph.

### Reproducibility (4/5)

The artifact appears strong: 81 files, ~30K lines, no `sorry`/`admit`, buildable via `lake build` in ~10 minutes. The one-to-one mapping between paper claims and named theorems is good practice. The Python sensitivity analysis being external to the Lean artifact is a minor weakness but clearly disclosed.

The data provenance section is honest about the trust boundary (Trainer Hill as empirical input). The suggestion of cross-validation against Limitless API is a good future-work item.

Deduction: The `native_decide` dependency means full reproducibility requires trusting Lean's native code generation, which is a weaker guarantee than kernel-checked verification. The paper acknowledges this.

---

## Minor Issues

1. **Typo in Lean identifier:** `GrimssnarlFroslass` (double-s) is acknowledged in a footnote. Should be fixed in the artifact if possible.
2. **Table I sensitivity ranges:** The "Point Est." column shows "---" for Gholdengo, which is confusing. Clarify: does this mean 0% point estimate from the base equilibrium, or that it's not in the base support?
3. **Section VII (Tournament Strategy):** The Swiss probability formula assumes independent rounds, which is violated by Swiss pairing algorithms that match players with similar records. This should be noted as an additional modeling limitation.
4. **Reference formatting:** Some references appear incomplete in the .bib (not visible here but should be checked).

---

## Questions for Authors

1. Have you attempted full equilibrium enumeration for the 14×14 game? If uniqueness holds, the paper's claims become dramatically stronger. If multiple equilibria exist, characterizing them would be valuable.

2. The replicator dynamics failed predictively within one day. What is your response to the critique that this undermines the evolutionary analysis as a contribution? Would iterated simulation (which you mention as future work) be verifiable in Lean?

3. The "numerical sufficiency" result shows Dark-type weakness alone accounts for Dragapult's sub-50% fitness. But this requires assuming 50% against all non-Dark opponents—an assumption violated by the data (Dragapult loses to 9/13 non-mirror opponents). How does this strengthen the argument beyond what the direct expected-value computation already shows?

4. Could the sensitivity analysis be partially verified in Lean using interval arithmetic over a certified LP solver? You mention this as future work—how feasible do you consider it with current Mathlib infrastructure?

---

## Overall Recommendation

### **Weak Accept** (3.5/5 → rounded to Weak Accept)

**Rationale:** The paper has improved substantially over three revision rounds. The v13 changes address the most serious issues from v12: the Nash uniqueness qualification, the causal narrative correction, the domination clarification, and the honest relabeling of "algebraic" to "numerical" sufficiency. The writing is now clear and epistemically disciplined. The Lean artifact is impressive and the methodological contribution is genuine.

However, the game-theoretic depth remains thin for a game theory specialist audience. The uniqueness gap is not addressed beyond acknowledgment, the replicator dynamics provide only trivially invariant directional claims that fail predictively, and the core game-theoretic computations are standard fare wrapped in a verification framework. The paper is stronger as a formal methods contribution than as a game theory contribution.

I recommend **Weak Accept** contingent on:
1. Adding a discussion of equilibrium enumeration feasibility and why it was not attempted.
2. Shortening the behavioral economics section and some Lean listings to improve density of contribution per page.
3. Clarifying the Gholdengo entry in Table I.

The paper is publishable in its current form but would benefit from these revisions. It makes a credible case that proof-carrying analytics is feasible and useful for competitive game analysis, even if the specific game-theoretic insights are modest.

---

*Reviewer 1 — IEEE Transactions on Games*
*Submission #753, Revision Round 3*
*Review Date: 2026-02-20*
