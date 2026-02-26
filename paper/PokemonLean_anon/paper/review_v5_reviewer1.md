# IEEE Transactions on Games — Reviewer Report

**Submission #753:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Review Date:** 2026-02-20

---

## 1. Summary

This paper presents a metagame analysis of the competitive Pokémon Trading Card Game, formalized in Lean 4 with ~30,000 lines and ~2,500 theorems. Using tournament data from Trainer Hill (Jan–Feb 2026), the authors encode a 14×14 archetype matchup matrix and prove a "popularity paradox" (the most-played deck, Dragapult, has sub-50% expected win rate), compute a machine-checked Nash equilibrium, perform full 14-deck replicator dynamics, and verify tournament-format transforms (Bo3, Swiss). The primary contribution is methodological: demonstrating that proof-carrying analytics can transform informal metagame narratives into machine-checkable, reproducible strategic science.

---

## 2. Strengths

**S1: Genuinely novel methodological contribution.** To my knowledge, this is the first paper to apply interactive theorem proving (Lean 4) to a full metagame analysis pipeline over real tournament data. The idea of "proof-carrying analytics" for competitive game ecosystems is original and has clear portability to other TCGs, MOBAs, or any domain with discrete strategy choices and observable payoff matrices. The paper credibly demonstrates feasibility rather than merely proposing a concept.

**S2: Impressive artifact scale and rigor.** The claim of zero `sorry`, zero `admit`, zero custom axioms is backed by the source code I examined—grep confirms no stray `sorry`/`admit` in proof positions. The artifact spans 80 files with thousands of theorems. The matchup matrix is fully encoded as a 196-entry function (`matchupWR` in `RealMetagame.lean`), and downstream computations (expected value, Nash equilibrium certification, replicator dynamics) chain directly from it. This is a substantial engineering effort.

**S3: Well-structured bridge from rules to data.** The `ArchetypeAnalysis.lean` module provides a concrete, falsifiable link between the type-effectiveness formalization and empirical matchup outcomes. The 83% alignment rate (13/15 Dark→Psychic matchups confirming type advantage direction) with explicitly characterized exceptions (N's Zoroark) is a thoughtful contribution. The paper correctly frames this as correlational consistency rather than causal derivation, which is scientifically honest.

**S4: Thorough robustness analysis.** The paper addresses the "Other" 30.5% segment with worst-case bounds (Section X), share-perturbation theorems (`SharePerturbation.lean`), and a 10,000-iteration sensitivity analysis showing core support decks appear in >96% of resampled equilibria. The Wilson interval treatment for individual matchups and the explicit acknowledgment that confidence intervals are not propagated through the Nash LP are both commendable. The sensitivity analysis Table I is particularly informative.

**S5: Honest treatment of limitations.** The paper explicitly acknowledges player-skill confounding, temporal locality (3-week window), strategic objective mismatch (Swiss vs. head-to-head), the top-14 normalization scope, and the single-step limitation of replicator predictions. The predictive validation subsection (Section VII-C) openly reports a failed prediction (Grimmsnarl declining despite highest fitness), attributing it to multi-step cascade effects—this is unusually candid for a methods paper.

---

## 3. Weaknesses

**W1: The `native_decide` trust boundary undermines the verification narrative.** The paper's central selling point is "machine-checked" guarantees, yet all game-theoretic core results (Nash equilibrium, replicator dynamics, bridge alignment) rely on `native_decide`, which trusts the Lean compiler's native code generation pipeline end-to-end without producing a kernel-verifiable proof term. The paper discloses this (Section IX-C) and explains that `decide` is "structurally precluded" due to `Fin.foldl` opacity. However, this means the entire game-theoretic core shares a single trust assumption. If a hypothetical code-generation bug affected rational arithmetic over `Fin.foldl`, all 244 `native_decide` theorems would be simultaneously invalid. The paper's own `optimize_proof` macro (which silently expands to `native_decide`) further obscures the trust boundary in the source code. While the disclosure in Section IX-C is adequate, the abstract and introduction use unqualified language ("machine-checked," "formally verified," "2,500 theorems") that overstates the guarantee. The qualifier "modulo native code generation" appears only once in the abstract and should be more prominent throughout.

**W2: The rules formalization is largely decoupled from the empirical analysis.** Despite Section III's emphasis on game-state formalization (GameState, TurnPhase, deck legality, card conservation), these structures are never connected to matchup outcomes or equilibrium computations. The `GameState` type in `Core/Types.lean` is rich (per-player zones, turn phases, prize accounting) but no theorem derives a matchup win rate from game-state simulation. The bridge in `ArchetypeAnalysis.lean` connects type assignments to matchup directions, but these type assignments are manual expert annotations (`Deck.primaryAttackType`, `Deck.primaryDefenseType`), not derived from the card data encoded in `Core/Types.lean`. The card-conservation theorem for Professor's Research (`CardEffects.lean`) is elegant but tangential—it does not feed into any downstream strategic claim. The paper acknowledges this ("future counterfactual analysis"), but the current contribution of the rules layer is weaker than the framing suggests.

**W3: The empirical results, stripped of verification, are unremarkable.** The "popularity paradox"—that the most-played deck has a sub-50% expected win rate—is a well-known phenomenon in competitive gaming communities (often called "popularity bias" or "noob trap"). Computing expected field win rate from a matchup matrix × share vector is a single matrix-vector multiply. The Nash equilibrium of a 14×14 constant-sum game is a linear program solvable in milliseconds. Replicator dynamics are elementary. The paper's value therefore rests almost entirely on the *methodology*—the Lean formalization—rather than on the game-theoretic findings themselves. The paper mostly acknowledges this, but some sections (the behavioral-economic interpretation in Section VI-B, the tournament strategy discussion in Section VIII) present standard textbook material without sufficient formal backing to justify their length.

**W4: Replicator dynamics results are limited to single-step directional statements.** The paper claims "replicator dynamics predict Dragapult decline, Grimmsnarl dominance, and Alakazam extinction pressure," but the verified theorems are point-wise single-step inequalities (e.g., `dragapult_share_decreases` shows share decreases after one Euler step with dt=1/100). No convergence guarantees, trajectory bounds, or multi-step stability results are proven. The `EvolutionaryDynamics.lean` file uses a 4-deck subcycle for tractability rather than the full 14-deck game (though `FullReplicator.lean` does handle 14 decks for fitness comparisons). The predictive validation subsection confirms the limitation: a one-step prediction fails for Grimmsnarl due to cascade effects. The claims in the paper should be more carefully scoped to "verified first-order directional pressure" rather than the broader "replicator dynamics predict."

**W5: The paper is 2–3 pages longer than necessary.** At 14 pages, the manuscript includes material that does not earn its space: Section IV-D ("Counterfactual Resource Experiments") is a single paragraph about capabilities not exercised; Section IX-D (continuous metagame monitoring) describes future workflow rather than results; Table IX (methodology comparison) makes a point better served by a sentence; and several large Lean code blocks could be replaced by theorem-statement summaries with code in supplementary material. The related work section, while competent, spends excessive space on AI game-playing systems (AlphaZero, Pluribus) that are orthogonal to the actual contribution.

---

## 4. Must-Do Revisions

**M1: Strengthen the `native_decide` disclosure and adjust verification claims.** The abstract should replace "formally verified" with "formally verified modulo native code generation" or "computationally verified" consistently. Section I should include a forward reference to the trust boundary discussion. The `optimize_proof` macro should be flagged prominently in the artifact README and in the paper wherever it appears. The paper should quantify: how many of the "180 theorems directly verifying empirical claims" use `native_decide` vs. kernel-checked `decide`? I suspect the answer is "nearly all empirical-claim theorems use `native_decide`," which readers deserve to know upfront.

**M2: Clarify and bound the bridge from rules to matchup data.** The paper should explicitly state that type assignments are expert annotations, not formally derived from card data. The current prose ("assignments are formalized in `ArchetypeAnalysis.lean`") conflates "encoded as Lean definitions" with "derived from game formalization." A clearer diagram showing what is formally derived vs. what is externally assumed would strengthen the contribution claim. The 83% alignment should be presented with appropriate caveats about the small sample (18 matchups) and the sensitivity of the p < 0.001 claim to the choice of null hypothesis.

**M3: Cut 2–3 pages of padding to sharpen the contribution.** Remove or compress Section IV-D, Section IX-D, Table IX, and the extended behavioral-economics paragraph (Section VI-B). Reduce inline code blocks to statement-only summaries where the proof tactic is just `native_decide` or `decide`—showing `by decide` adds no information beyond "this is decidable." Move the full 14×14 matrix listing and complete code blocks to supplementary material.

---

## 5. Should-Do Revisions

1. Fix the `GrimssnarlFroslass` typo in the Lean source (single-m, double-s). The footnote acknowledging it is insufficient; the identifier should be corrected in the artifact for a final publication.

2. Report the number of games underlying each matchup cell alongside the Wilson intervals. Currently, sample sizes are mentioned for only two pairs (Dragapult mirror: 2,845; Gholdengo vs Dragapult: 2,067). The smallest cells likely have <50 games; readers need this to assess reliability of the 14×14 matrix.

3. The symmetrized Nash equilibrium (Section VII, Table VI) has a 7-deck support while the bimatrix version has 6 per player. Discuss whether the one-deck discrepancy (Gholdengo in symmetrized but not bimatrix row) is substantively meaningful or within numerical tolerance.

4. Clarify the relationship between the 4-deck subcycle replicator analysis (`EvolutionaryDynamics.lean`) and the full 14-deck analysis (`FullReplicator.lean`). The paper text references the full 14-deck results but the evolutionary dynamics file primarily proves theorems on the 4-deck cycle. State which results are from which formalization.

5. The sensitivity analysis (10,000 iterations) is conducted in Python, not Lean. This is disclosed, but the paper should discuss whether the Python resampling + LP solving introduces its own trust boundary that partially undermines the verification story.

6. Add a "Threats to Internal Validity" paragraph addressing the possibility of systematic errors in the Trainer Hill data aggregation (e.g., duplicate reporting, platform-specific biases in online vs. in-person tournaments).

7. The scatter plot (Figure 1) should use full archetype names or a legend key; the current abbreviations (Drag, Grimm, Ghold, CharN, Alak, Kang) require memorization that impedes readability.

---

## 6. Questions for Authors

**Q1:** The paper states that `decide` is "structurally precluded" because `Fin.foldl` is opaque to the Lean 4 kernel reducer. Have you tried alternative implementations (e.g., recursive definitions over `List (Fin n)` or `Vector`) that might be kernel-reducible? If so, what specifically failed? If the Lean 4 kernel were extended to reduce `Fin.foldl`, would all 244 `native_decide` theorems be immediately convertible to `decide`?

**Q2:** The type assignments in `ArchetypeAnalysis.lean` map each archetype to exactly one primary attack type and one primary defense type. Many competitive decks run multiple attackers of different types (e.g., Dragapult Charizard has both Psychic and Fire attackers). How sensitive is the 83% alignment claim to the choice of "primary" type? Did you consider a multi-type assignment model?

**Q3:** The paper treats the metagame as a single-shot symmetric game, but tournament play involves sequential rounds with information updating (Swiss pairings, public standing). Have you considered whether the Nash equilibrium of the single-shot game is robust to the sequential structure of Swiss tournaments, or does the Swiss format create incentives that diverge from the single-shot solution?

---

## 7. Scores

| Criterion        | Score (1–5) | Justification |
|------------------|:-----------:|---------------|
| **Novelty**          | 4 | First application of ITP to real TCG metagame analysis; the "proof-carrying analytics" concept is genuinely new, though the game-theoretic content is standard. |
| **Technical Soundness** | 3 | The `native_decide` trust boundary is adequately disclosed but weakens the verification claim. The rules-to-data bridge relies on manual type assignments. Replicator results are single-step only. The core computations are correct but the formal guarantee is weaker than presented. |
| **Significance**     | 3 | Methodological template is valuable but the specific results are unsurprising. Impact depends on whether the approach is adopted by other researchers—the 30K LoC barrier is high. The 3-week window limits empirical significance. |
| **Clarity**          | 4 | Well-written, logically structured, honest about limitations. Some padding in Sections IV-D, IX-D, and VI-B. Code blocks are simultaneously the paper's strength and its main readability challenge. |
| **Reproducibility**  | 5 | Outstanding. Lean source with `lake build` instructions, explicit data provenance, and one-to-one mapping between prose claims and theorem identifiers. This is a model for reproducible game research. |

---

## 8. Overall Recommendation

### **Weak Accept**

This is a well-executed methodological contribution that demonstrates, for the first time, that proof-carrying metagame analytics is feasible for a real competitive game ecosystem. The artifact is impressive in scale and rigor, the reproducibility is exemplary, and the paper is generally well-written and honest about its limitations.

However, the verification claim is materially weakened by the blanket reliance on `native_decide` for all game-theoretic core results, and the paper overstates this guarantee in the abstract and introduction. The rules formalization, while competent, is more loosely coupled to the empirical analysis than the title "From Rules to Nash Equilibria" implies—the bridge is correlational, not causal, and rests on manual type annotations. The empirical findings themselves (popularity paradox, Nash support, replicator directions) are computationally trivial and would be unsurprising to the TCG competitive community.

Conditional on the three must-do revisions—particularly tightening the verification claims and cutting 2–3 pages—this paper would make a solid contribution to IEEE Transactions on Games as a methodological case study. Without those revisions, the gap between the paper's claims and its actual guarantees is too large for acceptance at this venue.
