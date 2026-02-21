# IEEE Transactions on Games — Review of Submission #753 (v3)

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Reviewer:** Anonymous (expertise: formal methods, game theory, competitive esports analytics)

**Date:** February 20, 2026

---

## 1. Summary

This paper presents a ~30,000-line Lean 4 formalization of competitive Pokémon TCG metagame analysis, claiming 2,500+ theorems with zero `sorry`/`admit`/axiom usage. Working from Trainer Hill tournament data over a three-week window (Jan 29–Feb 19, 2026), the authors encode 14 archetype matchup win rates and meta shares, then formally verify a "popularity paradox" (Dragapult holds 15.5% meta share but only 46.7% expected win rate, while Grimmsnarl at 5.1% share achieves 52.7%), certify bimatrix and symmetric Nash equilibria (both assigning 0% weight to Dragapult), run full 14-deck replicator dynamics (classifying 5 growers and 9 shrinkers), and provide a sensitivity analysis over 10,000 resampled equilibria. The paper positions its primary contribution as methodological—demonstrating that proof-carrying analytics is feasible for real game ecosystems—rather than as a competitive-tactical tool. A secondary contribution is a "bridge" from formalized type-effectiveness rules to empirical matchup outcomes, showing 83%+ directional alignment.

---

## 2. Scores

| Criterion        | Score (1–5) | Notes |
|-------------------|:-----------:|-------|
| **Novelty**       | 3           | Applying Lean 4 to competitive TCG metagame analysis is original in combination, but the individual game-theoretic techniques (Nash certification, replicator dynamics) are textbook. |
| **Technical Soundness** | 3     | The Lean artifact compiles and the mathematics is correct *conditional on* `native_decide` trust and on accepting that hardcoded lookup tables constitute "formalization." The rules→data bridge is weaker than presented. |
| **Significance**  | 2           | The practical delta over scripting is not convincingly demonstrated. The three-week temporal window severely limits external validity. |
| **Clarity**       | 4           | Well-written, clearly structured, honest about limitations. The paper is readable and the Lean listings are well-chosen. |
| **Reproducibility** | 4         | Zero-sorry artifact with build instructions (`lake build`, ~10 min). Data provenance is documented. The Python sensitivity analysis is external but included. |

---

## 3. Strengths

**S1: Genuine artifact completeness.** The project achieves a notable engineering milestone: ~30,000 lines, 80 files, 2,574 theorem/lemma declarations (by `grep` count), zero `sorry`, zero `admit`, zero custom axioms. For a domain-specific Lean 4 project coupling game rules, data encoding, game theory, and evolutionary dynamics, this is a substantial proof-engineering effort. The artifact is buildable and self-contained.

**S2: Bimatrix and symmetric Nash equilibria with full best-response certification.** The Nash equilibrium in `NashEquilibrium.lean` (lines 290–332) is verified via explicit quantified best-response checks over all 14 pure strategies for both row and column players. This is compositionally stronger than merely asserting a solution: `real_nash_row_best_response_checks` and `real_nash_col_best_response_checks` certify that no unilateral deviation is profitable. The symmetric Nash in `SymmetricNash.lean` confirms robustness to the constant-sum approximation (game value exactly 500), and the distinct 7-deck support with 0% Dragapult weight reinforces the headline finding. This dual verification (bimatrix + symmetric) is a genuine contribution that goes beyond what a typical Python script delivers—the certification is total over the strategy space, not sample-based.

**S3: Full 14-deck replicator dynamics.** `FullReplicator.lean` provides machine-checked fitness comparisons and directional predictions over the complete 14×14 matrix and observed share vector. The classification into 5 growers and 9 shrinkers (`growers_above_average`, `shrinkers_below_average`) and the identification of Grimmsnarl as universally fittest (`full_replicator_grimmsnarl_fittest`) and Alakazam as worst (`full_replicator_alakazam_worst`) are complete enumerations that would be tedious and error-prone to verify manually.

**S4: Honest and detailed threat-to-validity analysis.** Section IX is unusually thorough for a games-venue paper. The authors explicitly characterize the temporal locality, top-14 normalization bias, strategic objective mismatch, and the `native_decide` trust boundary (Section VIII.C). The machine-checked worst-case bounds (Dragapult needs ≥57.6% vs. all unmodeled decks to reach 50% overall) add rigor to robustness claims. The share-perturbation analysis (`SharePerturbation.lean`) further strengthens the argument that the paradox is structural rather than artifactual.

**S5: Sensitivity analysis provides meaningful uncertainty quantification.** Table I reports 10,000-iteration sensitivity ranges showing that while the exact Nash support is fragile (recovered in only 2.1% of iterations), the core trio (Grimmsnarl 96.5%, Mega Absol 97.3%, Raging Bolt 98.3%) is highly stable. This is a responsible treatment of point-estimate uncertainty that most metagame analyses omit entirely.

**S6: Clear methodological template.** The paper articulates a transferable four-step pipeline (formalize rules → encode data → prove strategic claims → tournament transforms) that could apply to other TCGs (Magic: The Gathering, Yu-Gi-Oh!, etc.) and competitive ecosystems with discrete strategy spaces. The reproducibility workflow (Section VIII.E) describing one-to-one theorem-to-manuscript mappings is a genuine contribution to scientific practice in games research.

**S7: Writing quality.** The paper is well-structured, readable, and appropriately cites relevant literature from formal methods, game theory, and behavioral economics. The motivating tournament scenario in Section I.A effectively grounds the technical work. Footnotes acknowledging identifier typos (e.g., `GrimssnarlFroslass`) demonstrate attention to detail.

---

## 4. Weaknesses

### Major

**M1: The rules→data "bridge" is a correlational consistency check on manually assigned types, not a formal derivation.** The paper's most ambitious claim is a "machine-checked bridge from type-effectiveness rules to empirical matchup outcomes" (Section III.A). Inspecting `ArchetypeAnalysis.lean`, this bridge consists of: (1) *manually* assigning `primaryAttackType` and `primaryDefenseType` to each archetype (lines 36–77), then (2) checking that `weakness defenderType attackerType = true` correlates with `matchupWR attacker defender > 500` in 83% of cases. This is a lookup-table comparison, not a formal derivation. The type assignments are modeling assumptions chosen by the authors—they are neither derived from deck composition nor from the card-level formalization in `Core/Types.lean`. A skeptic could assign types differently and get different alignment rates. The paper acknowledges this ("domain-expert type assignments, modeling assumptions, not formally derived from deck composition") but the framing throughout still overstates the contribution. The `rules_to_data_bridge` theorem (line ~290) conjoins `weakness .psychic .dark = true` with `matchupWR .GrimssnarlFroslass .DragapultDusknoir > 500`—these are independently hardcoded facts. The Lean kernel verifies that both Boolean expressions evaluate to `true`, but this adds no semantic insight that comparing two spreadsheet columns wouldn't provide. The bridge would be genuinely formal if type assignments were *derived* from deck lists (which are available in the data source) by analyzing the principal attacker's typing from the card database.

**M2: The `native_decide` trust boundary undermines the "formally verified" headline.** The paper reports 244 direct `native_decide` uses, and the custom `optimize_proof` tactic is syntactic sugar for `native_decide` (confirmed in `EvolutionaryDynamics.lean`, line 12). Every headline theorem—the Nash equilibria (`real_nash_equilibrium_verified`, `symmetric_nash_equilibrium_verified`), all replicator dynamics results, all bridge alignment theorems—relies on `native_decide`. As the authors honestly acknowledge in Section VIII.C, `native_decide` trusts the Lean 4 compiler's code generation end-to-end and does not produce a kernel-verifiable proof term. The authors further note that `decide` (the kernel-checked alternative) is "structurally precluded" because `Fin.foldl` is opaque to the kernel reducer. This means there is genuinely *no* path to kernel-level verification for the current formulation. A hypothetical compiler bug in rational arithmetic over `Fin.foldl` could simultaneously invalidate all 244 proofs with no defense-in-depth. While no such bugs are known, the paper's title and abstract claim "formally verified" without qualification. The paper should either qualify this claim (e.g., "verified modulo native code generation") or restructure the core computations to use kernel-transparent recursion (the authors state they attempted this and failed, which is concerning for the robustness claim). For a venue that values formal methods rigor, this is a significant gap between claim and reality.

**M3: Insufficient justification of practical value over scripting.** The paper explicitly states "the primary contribution is methodological rather than competitive-tactical" and acknowledges that "the headline popularity paradox could be computed in a spreadsheet." The three advantages cited—compositional guarantees, robustness proofs, and reproducibility infrastructure—are reasonable in principle but not convincingly demonstrated to matter in practice. The Nash certification checks best-response conditions for 14 strategies—a 14×14 matrix computation that any correct LP solver handles routinely. The "robustness proofs" in `Robustness.lean` are worst-case arithmetic bounds that are equally checkable in Python with exact fractions (`fractions.Fraction`). The "reproducibility infrastructure" argument (Section VIII.E) conflates two different properties: (a) *correctness* of the computational pipeline (which Lean guarantees, modulo `native_decide`) and (b) *scientific reproducibility* (which depends on data provenance, methodology documentation, and open-source code—all achievable without a theorem prover). The paper needs a concrete example where the formal pipeline caught an error that a scripted pipeline would have missed, or a quantitative comparison of verification effort versus error rate. Without this, the 30,000 lines of Lean appear to add significant overhead for marginal benefit over ~200 lines of well-tested Python.

**M4: Three-week temporal window severely limits generalizability.** The entire empirical analysis rests on Trainer Hill data from January 29 to February 19, 2026—a 21-day window. The paper claims "the paradox is structural: it derives from the matchup matrix, not the share vector, so the central finding is not an artifact of a particular metagame snapshot but reflects a persistent property of the underlying strategic landscape." This claim is not supported by the evidence presented. Structural persistence requires demonstration across multiple time windows, which the paper does not provide. The preliminary predictive validation (Section VI.A) tested against data "one day after the analysis window" and found that 1 of 3 directional predictions failed (Grimmsnarl declined despite being predicted as fittest). This is acknowledged as a "limitation of single-step replicator analysis" but it also undermines confidence in the temporal robustness of the underlying matrix. A rolling-window analysis showing stability of the popularity paradox across, say, 4–6 consecutive weekly snapshots would substantially strengthen the paper.

**M5: The game theory is routine; the novelty is in the domain application, which is narrow.** Nash equilibrium certification via best-response checking is standard (see, e.g., Nisan et al., 2007, Ch. 3). Replicator dynamics on finite games is textbook evolutionary game theory (Weibull, 1997; Hofbauer & Sigmund, 1998). The symmetrized constant-sum formulation is a known transformation. The paper does not introduce any new game-theoretic results, algorithms, or proof techniques. The Lean formalization of these standard constructions is an engineering contribution, but the game-theoretic depth is shallow. The `NashEquilibrium` definition (lines 50–54 of `NashEquilibrium.lean`) is a direct encoding of the textbook definition; no novel abstraction barrier, generalization, or proof strategy is introduced. The replicator dynamics formalization in `EvolutionaryDynamics.lean` similarly instantiates textbook definitions on concrete data without proving any general convergence theorems or stability results (the Lyapunov analysis is limited to three specific test distributions). For IEEE Transactions on Games, the game-theoretic contribution needs to go beyond applying known tools to a single dataset.

### Minor

**m1: The `FiniteGame` structure conflates bimatrix and generic games.** The `FiniteGame` structure in `NashEquilibrium.lean` has both a `payoff` field (player × strategy → Rat) and a `matrix` field (strategy × strategy → Rat). The `payoff` field is set to `fun _ _ => 0` in all real uses (`realMetaGame14`, `symMetaGame`), making it dead code. The `NashEquilibrium` definition uses only `matrix`. This is a minor design issue but creates confusion about what the formalization actually models—it claims to be a bimatrix game but only encodes one matrix. The column player's payoff structure is implicit in the `colPurePayoff` definition, which uses the *same* matrix transposed. This conflation should be documented or the dead field removed.

**m2: The paper mixes notation for the replicator dynamics.** Section VI presents the continuous-time replicator equation ($\dot{x}_i$) but the Lean implementation (`replicatorStep` in `EvolutionaryDynamics.lean`, lines 41–43) uses discrete-time Euler steps with fixed `dt`. The discrete-time dynamics can diverge from continuous-time behavior for large `dt`, and the proofs only verify single steps with `dt = 1/10` or `dt = 1/100`. The paper should explicitly state that all verified results are about discrete-time dynamics and discuss the approximation quality.

**m3: Theorem count inflation.** The abstract claims "2,500+ theorems." Many of these are infrastructure theorems about toy examples (e.g., RPS games, 2×2 minimax, dominated strategy examples in `EvolutionaryDynamics.lean` spanning 100+ theorems). `GameTheory.lean` alone has 191 theorem/lemma declarations, the majority being textbook exercises. The "180 theorems directly verify the empirical claims" (Section VIII.D) is the more honest count. The paper should lead with this number.

**m4: The `optimize_proof` tactic is misleading nomenclature.** In `EvolutionaryDynamics.lean` (line 12), `optimize_proof` is defined as a macro that expands to `native_decide`. The name suggests some proof optimization procedure; in reality, it's an alias. This obscures the trust boundary for readers who don't inspect the macro definition. The paper's code listings show `optimize_proof` in the replicator dynamics theorems but explain it only parenthetically. This should use `native_decide` directly for transparency.

**m5: Mirror match win rates are unexplained.** The paper notes in a footnote that mirror match WRs fall below 50% (e.g., 49.4%, 48.5%) due to the tie convention. This is mathematically expected, but several mirror matches (e.g., Gholdengo 48.8%, Grimmsnarl 48.5%) deviate by 1–2 points, suggesting either small sample noise or systematic effects. The paper doesn't analyze whether these deviations are within confidence bounds.

**m6: Figure 3 (metagame cycle) is hand-drawn and selective.** The four-deck cycle (Grimmsnarl → Dragapult, Mega Absol → Grimmsnarl, Raging Bolt → Mega Absol) is compelling, but the directed graph omits the Raging Bolt → Dragapult edge (51.0%) and the Grimmsnarl → Raging Bolt edge (47.3%, losing). The cycle is partially cherry-picked from the 4×4 submatrix. The paper acknowledges this but could be more explicit about what edges are omitted and why.

**m7: No discussion of player-skill confounding.** Matchup win rates aggregate across all skill levels. If Dragapult attracts weaker pilots (e.g., because it's popular and "easy"), its observed win rates could be suppressed by player-quality effects rather than deck-strength effects. The paper treats matchup data as reflecting deck properties alone. This is a standard assumption in metagame analysis but should be acknowledged as a limitation, especially given the paper's formal rigor elsewhere.

**m8: The sensitivity analysis is Python, not Lean.** Table I's 10,000-iteration resampling is conducted via Python (acknowledged in the paper). This is the most important uncertainty quantification in the paper, and it sits outside the formal verification boundary. The paper treats this as a future-work item but it weakens the end-to-end formal verification claim.

---

## 5. Questions for Authors

**Q1:** Can you provide a concrete example where the Lean formalization caught an error that would have gone undetected in an equivalent Python implementation? The paper argues for "proof-carrying analytics" as a methodology, but without a demonstrated error-catching episode, the value proposition remains theoretical.

**Q2:** The replicator dynamics results in `EvolutionaryDynamics.lean` are primarily over 4-deck and 5-deck subgames, while `FullReplicator.lean` provides full 14-deck results. The paper text discusses "full 14-deck replicator dynamics" prominently but the `EvolutionaryDynamics.lean` file—which contains the bulk of the replicator theorems—works with 3-, 4-, and 5-deck subsets. Can you clarify what fraction of the replicator dynamics theorems cited in the paper are over the full 14-deck game versus reduced subgames? The `FullReplicator.lean` file appears to contain ~15 theorems, while `EvolutionaryDynamics.lean` contains ~70 theorems, mostly on toy or reduced games.

**Q3:** You note that `decide` is "structurally precluded" by `Fin.foldl` opacity. Have you investigated alternative summation implementations (e.g., `List.foldl` over `List.finRange`, or recursive definitions over `Fin`) that might be kernel-transparent? If so, what specific failures did you encounter? This is important for assessing whether the `native_decide` dependency is a fundamental limitation or an engineering choice.

**Q4:** The predictive validation (Section VI.A) tested one day out-of-sample and found 1/3 directional predictions incorrect. Have you since collected data from subsequent weeks that could strengthen or weaken the model's predictive validity? For a paper submitted in late February 2026, at least 1–2 additional weeks of data should be available.

---

## 6. Overall Assessment and Recommendation

This paper represents a substantial engineering effort and an interesting methodological experiment: can proof assistants add value to competitive game analytics? The Lean artifact is real, buildable, and impressively comprehensive in scope. The writing is clear, the threats-to-validity section is commendably honest, and the dual Nash equilibrium verification (bimatrix + symmetric) is a genuine formal contribution.

However, the paper suffers from a persistent gap between its claims and its evidence. The "formally verified" headline is qualified by universal dependence on `native_decide`, which the authors themselves acknowledge does not produce kernel-checkable proof terms. The "rules to data bridge" is a manual type-assignment correlation check, not a formal derivation from game mechanics. The practical value over scripting is asserted but not demonstrated with a concrete error-catching example. The three-week temporal window is too narrow to support claims of structural persistence, and the preliminary predictive validation partially failed. The game theory is textbook-routine, with no new theoretical results.

The paper would benefit substantially from: (1) a rolling-window analysis demonstrating temporal stability, (2) a concrete error-catching case study motivating the Lean overhead, (3) honest qualification of "formally verified" given the `native_decide` dependency, and (4) either deepening the game-theoretic contribution (e.g., proving general convergence results for the replicator dynamics, not just point evaluations) or strengthening the empirical contribution (e.g., multi-season analysis, cross-game portability demonstration).

As it stands, the paper is an interesting proof-of-concept with notable engineering merit, but the gap between ambition and evidence, the routine game theory, and the narrow empirical scope place it below the acceptance threshold for IEEE Transactions on Games.

**Recommendation: Weak Reject**

The paper has clear merit and could become acceptable with a major revision addressing temporal scope, the `native_decide` qualification, and a stronger practical-value demonstration. I would encourage resubmission after collecting rolling-window data across at least 8–12 weeks and either achieving kernel-checked proofs for the headline theorems or explicitly scoping the "formal verification" claim.

---

## 7. Confidence

**Confidence: 4/5 (High).** I have expertise in formal methods (including Lean 4), finite game theory, and metagame analysis for competitive card games. I read the full paper, inspected the key Lean source files (`NashEquilibrium.lean`, `SymmetricNash.lean`, `EvolutionaryDynamics.lean`, `FullReplicator.lean`, `ArchetypeAnalysis.lean`, `RealMetagame.lean`, `TypeEffectiveness.lean`, `Core/Types.lean`), verified the `native_decide` usage patterns, and cross-checked theorem statements against the paper's prose claims. I did not rebuild the full artifact from source.
