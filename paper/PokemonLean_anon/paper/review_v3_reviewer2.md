# Review — Submission #753 (Reviewer 2)

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"  
**Venue:** IEEE Transactions on Games  
**Reviewer specialization:** Formal methods, game theory, mechanism design  
**Date:** 2026-02-20

---

## Ratings

| Criterion | Score (1–5) | Justification |
|---|---|---|
| **Novelty** | 3.5 | First proof-carrying metagame pipeline; game-theoretic content is routine |
| **Technical Soundness** | 3.5 | Verified core is solid but several modeling gaps and trust-boundary issues |
| **Significance** | 3 | Methodological template is portable; empirical findings are snapshot-specific |
| **Clarity** | 4 | Well-structured, honest about limitations, good artifact–prose tracing |
| **Reproducibility** | 4.5 | Outstanding: `lake build`, zero sorry, CI badge, versioned data |

---

## 1. Summary

The paper formalizes ~30K lines of Lean 4 covering Pokémon TCG rule semantics, tournament matchup data from Trainer Hill (Jan 29–Feb 19, 2026, ≥50-player events), and metagame analytics over 14 archetypes. The authors machine-check a "popularity paradox" (Dragapult: 15.5% share, 46.7% EV; Grimmsnarl: 5.1% share, 52.7% EV), certify a six-deck Nash equilibrium (bimatrix) and a seven-deck symmetric Nash equilibrium (constant-sum symmetrization), both assigning Dragapult 0% weight, verify one-step replicator dynamics over the full 14-deck game, and perform Bo3 amplification analysis. A Python-based sensitivity analysis (10K iterations) assesses Nash stability. The central claim is methodological: formal verification turns metagame narratives into reproducible, auditable science.

---

## 2. Strengths

**S1. Genuinely novel methodological contribution.** I am unaware of prior work that machine-checks Nash equilibrium certification and evolutionary dynamics over a *real* competitive-game matchup matrix in a proof assistant. The template—formalize rules, encode empirical payoffs, prove strategic claims—is well-articulated and clearly portable beyond Pokémon TCG.

**S2. Rigorous equilibrium certification.** The Nash verification is done properly: best-response inequalities are checked for all 14 pure strategies for *both* row and column players, and the `NashEquilibrium` definition correctly requires valid mixed-strategy conditions (non-negativity, summing to 1) in addition to the payoff inequalities. This is structurally sound and goes beyond simply trusting an LP solver output. Crucially, the authors present both a bimatrix formulation and a symmetrized constant-sum version, demonstrating that the population-game interpretation (symmetric Nash, game value = 500) yields qualitatively identical conclusions. This dual treatment preempts the most natural game-theoretic objection to the bimatrix model.

**S3. Exceptional reproducibility infrastructure.** The zero-sorry/zero-admit/zero-axiom standard, CI integration, and the explicit case study (§IX-F) tracing a headline claim through six auditable steps set a high bar. The claim that "if any upstream value changes, the downstream theorem will fail" is credible given the Lean architecture, and I verified it by inspecting module dependency structure.

**S4. Honest and multi-layered robustness analysis.** The threats section is unusually thorough for an applied game theory paper. The worst-case "Other" bounds, the share-perturbation theorems (Dragapult remains sub-50% even at 5% share; Grimmsnarl remains above 50% even at 15.5% share), and the 10K-iteration sensitivity analysis collectively address different robustness dimensions. The authors correctly distinguish between verified (Lean) and unverified (Python) robustness claims.

**S5. Clean formal definitions.** Inspecting `NashEquilibrium.lean` and `SymmetricNash.lean`, the game-theoretic definitions are standard and correctly formalized. The `FiniteGame` structure, `MixedStrategy`, `expectedPayoff`, and `NashEquilibrium` predicate are textbook-correct. The `sumFin` via `Fin.foldl` is idiomatic Lean 4.

**S6. Appropriate scope discipline.** The paper avoids claiming universal metagame laws and consistently qualifies results to the three-week window and 14-archetype scope. This restraint is commendable for a domain where overclaiming is endemic.

**S7. Type-advantage bridge is a genuine (if modest) formal contribution.** The alignment analysis in §III-B—showing 13/15 Dark→Psychic matchups align with the empirical matrix—is a concrete, falsifiable connection between formalized rules and observed data. It is not a derivation of matchup outcomes from rules, but it is more than mere assertion.

---

## 3. Weaknesses

### Major

**M1. The rules→data bridge (§III-B) is correlational, not causal, and this distinction is insufficiently marked.**

The paper's most ambitious structural claim is the "machine-checked path from rule-level game semantics through type assignments to empirical matchup outcomes." However, what is actually proven is: (a) the type chart says Dark is super-effective against Psychic; (b) certain archetypes are *manually assigned* Dark attack types and Psychic defense types; (c) the empirical win rates for those matchups happen to exceed 50% in 13 of 15 cases.

The critical gap is step (b). The type assignments are hand-coded definitions (`Deck.primaryAttackType`, `Deck.primaryDefenseType`), not derived from deck composition or card-level formalization. These functions are *axioms about the real world* disguised as definitions. There is no formal connection between, say, the cards in a Grimmsnarl deck list and the assignment `.dark`. The 83% alignment is therefore a post-hoc consistency check between two independently specified datasets, not a formal derivation. The paper occasionally conflates these ("this is the formal chain the reviewers asked for"), which risks overstating the contribution.

*Recommendation:* Clearly label the type assignments as modeling assumptions subject to domain-expert judgment, not as formally derived from the card pool. Acknowledge that the bridge is correlational (rules predict direction of matchup advantage) rather than mechanistic (rules entail matchup win rates).

**M2. The `native_decide` trust boundary deserves deeper technical analysis.**

The paper correctly notes that `Fin.foldl` opacity prevents kernel-checked `decide`, and characterizes this as "a known limitation of the current Lean 4 kernel." However, the 244 uses of `native_decide` (including the 186 in `EvolutionaryDynamics.lean` alone, plus all Nash and replicator theorems) mean that the *entire* game-theoretic contribution rests on trusting compiled native code.

The paper should acknowledge three specific risks: (i) potential bugs in Lean 4's code generator that could accept false decidability witnesses; (ii) the `native_decide` pathway does not produce a proof term that the kernel can independently verify—it trusts the compilation pipeline end-to-end; (iii) the concentration of all headline theorems in `native_decide` means there is no defense in depth. If the native code generator has a soundness bug affecting rational arithmetic over `Fin.foldl`, *all* results would be simultaneously invalidated.

I note the paper says "we investigated replacing `native_decide` with kernel-checked `decide`" and found it "structurally precluded." This is honest but raises the question: have the authors tried reformulating `sumFin` using structural recursion instead of `Fin.foldl`? This is a standard workaround in Lean 4 formalization and might enable `decide` for at least some key theorems. If attempted and failed, the paper should say so explicitly.

*Recommendation:* Add a paragraph discussing the specific trust assumptions of `native_decide`, cite relevant Lean community discussions on its soundness status, and report whether recursive reformulation of `sumFin` was attempted.

**M3. The bimatrix game model is a questionable abstraction for a population game.**

A large Swiss tournament is not a two-player game: each player independently chooses a deck and faces a *distribution* of opponents. The correct model is a symmetric population game (or, equivalently, a game against the field). The bimatrix formulation is a standard approximation, but it introduces the artifact of distinct row/column strategies when the matrix deviates from constant-sum.

The symmetrized treatment (§VII, `SymmetricNash.lean`) addresses this well—the game value is exactly 500, and the symmetric equilibrium is unique and well-interpreted. However, the paper leads with the bimatrix result and devotes significant space to explaining the row/column support discrepancy, which is ultimately an artifact of using the wrong game model. The constant-sum symmetrization should be presented as the *primary* result for the population-game interpretation, with the bimatrix as a sensitivity check.

Additionally, neither formulation accounts for the fact that in Swiss tournaments, the objective is not "maximize expected win rate against a random opponent" but "maximize probability of achieving X-2 or better." The paper acknowledges this (§VII) but does not analyze the gap. For decks with highly variable matchup spreads (e.g., Dragapult: 34.3% vs Gardevoir but 64.1% vs Charizard), the Swiss objective could produce materially different equilibria due to variance effects.

*Recommendation:* Reorder presentation to lead with the symmetric equilibrium. Briefly quantify the Swiss-vs-EV gap, even if only for the top 3 decks.

**M4. Statistical methodology is fragmented across verified and unverified components.**

The paper's statistical story has three layers: (a) Wilson intervals on individual matchup cells (computed but not formally verified in Lean), (b) point-estimate Nash equilibrium (verified in Lean), and (c) sensitivity analysis (Python, 10K iterations). This creates an awkward trust gradient where the least-verified component (Python sensitivity) provides the strongest robustness evidence.

Specifically, the 2.1% exact-support recovery rate in the sensitivity analysis suggests the Nash equilibrium is highly non-unique under data uncertainty—a fact that substantially qualifies the "machine-checked Nash equilibrium" narrative. The paper handles this honestly, but the presentation could better emphasize that the *verified* equilibrium is one point in a large set of near-equilibria. The core trio (Grimmsnarl 96.5%, Mega Absol 97.3%, Raging Bolt 98.3% inclusion) is robust; the exact weights are not.

*Recommendation:* Frame the Lean-verified equilibrium as a "witness" (proving that an equilibrium with these properties exists and is valid) rather than "the" equilibrium. Discuss uniqueness or essential uniqueness.

### Minor

**m1. The `optimize_proof` macro is misleading nomenclature.** It expands to `native_decide`, not to any optimization. A reader unfamiliar with the codebase might think it involves proof search or term optimization. Rename to `decide_native` or simply inline `native_decide`.

**m2. The 14-archetype scope covering 69.5% of the field means 30.5% of opponents are unmodeled.** While the worst-case robustness bounds are useful, the implicit assumption that Dragapult's matchup profile against "Other" is not dramatically favorable is not verifiable from the data. If "Other" contains many rogue decks that Dragapult farms (plausible given its high popularity attracting weak-field opponents), the paradox could narrow or vanish at the full-field level.

**m3. Replicator dynamics are verified for a single step only.** The claimed "Grimmsnarl dominance" and "Alakazam extinction pressure" are instantaneous directional derivatives, not trajectory predictions. The predictive failure (§VII-A) confirms this limitation. The paper should be more careful with terminology: "Grimmsnarl has highest instantaneous fitness" ≠ "Grimmsnarl dominance."

**m4. The behavioral-economic interpretation (§VI-B) cites heavyweight references (Kahneman & Tversky, Banerjee, Bikhchandani) without connecting them to observable features of this dataset.** No player-level data, no survey, no structural estimation. This section could be condensed to two sentences without loss.

**m5. Mirror match sub-50% artifact.** The tie convention WR = (W + T/3)/(W + L + T) mechanically depresses mirror-match win rates below 50%. This is noted in a footnote but has implications throughout: the game value being 47.97% in the bimatrix formulation is entirely an artifact of this convention, not a strategic finding. The paper should state this more prominently to avoid misinterpretation.

**m6. Missing discussion of equilibrium selection.** Nash equilibria need not be unique even in finite games. The paper verifies that *a* specific strategy profile is an equilibrium but does not discuss whether the LP solution method guarantees uniqueness for the symmetrized game, or whether alternative equilibria with different support sets exist. For the symmetric constant-sum game, uniqueness follows from the minimax theorem when the game value is unique, but this should be stated explicitly.

**m7. No formal connection between the rules layer and data ingestion.** The `checkDeckLegal_iff` theorem validates deck structure, but there is no mechanism ensuring that Trainer Hill data only includes legal decks. The paper claims the rules layer "ensures that only tournament-legal configurations enter the analysis," but this is aspirational—the data is ingested as raw constants, not filtered through `checkDeckLegal`.

---

## 4. Questions for Authors

**Q1.** The `ArchetypeAnalysis.lean` type assignments are the linchpin of the rules→data bridge. How would you handle archetypes whose primary attacker has a different type from their primary defender (e.g., a deck using a Dragon-type attacker whose weakness is Psychic but whose attacks deal Fire damage)? Does the current single-type assignment model break down for multi-type or hybrid archetypes? Specifically, how do you justify that Dragapult Charizard defends as Psychic rather than Fire, given that both attackers are present?

**Q2.** You report 186 `native_decide` calls in `EvolutionaryDynamics.lean` alone. Have you profiled the build to check whether Lean's code generator is performing exact rational arithmetic on the full 14×14 matrix for each of these, or are intermediate results being shared? What is the total `lake build` time, and how sensitive is it to matrix size? This matters for the claimed portability to "rolling weekly windows."

**Q3.** The sensitivity analysis finds that Dragapult receives *nonzero* Nash weight in 22.1% of resampled equilibria (Table I). Under what matchup perturbation conditions does Dragapult enter the support? Is there a structural characterization (e.g., "Dragapult enters support when its win rate against Gholdengo improves by ≥X points"), and could such a characterization be formally verified?

---

## 5. Recommendation

**Weak Accept** (borderline — revision strongly recommended before final acceptance)

### Justification

The paper makes a genuine methodological contribution: proof-carrying metagame analytics is novel, well-executed, and the artifact quality is high. The dual Nash formulation, the reproducibility infrastructure, and the honest threats section elevate the work above the typical applied game-theory submission.

However, several issues temper enthusiasm:

1. The rules→data bridge, while present, is correlational rather than mechanistic, and the paper's language sometimes overstates the formal chain (M1).
2. The entire verified game-theoretic core rests on `native_decide` with no defense-in-depth, and the paper does not adequately discuss the specific trust assumptions (M2).
3. The bimatrix model is presented as the primary equilibrium result despite being the wrong abstraction for a population game; the symmetrized version should lead (M3).
4. The most important robustness evidence (sensitivity analysis) is unverified, creating a trust inversion (M4).

These are addressable in revision. The core artifact is strong, the methodology is sound in principle, and the domain application is squarely within IEEE ToG scope. The paper would move to a clear Accept if (a) the rules→data bridge claims are appropriately scoped, (b) the `native_decide` trust boundary receives deeper analysis, and (c) the symmetric equilibrium is foregrounded as the primary population-game result.

### Confidence

**4/5.** I have verified the formal definitions in the Lean source, cross-checked key theorem statements against the manuscript, and audited the game-theoretic modeling choices. I have not independently re-run `lake build` on the full artifact.
