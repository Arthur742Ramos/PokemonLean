# IEEE Transactions on Games — Reviewer Report

**Submission #753:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

**Reviewer:** Reviewer 3 (esports analytics / competitive game ecosystems)

**Date:** 2026-02-20

---

## 1. Summary

This paper constructs a formally verified metagame analysis pipeline for the competitive Pokémon Trading Card Game using Lean 4 and real tournament data (Trainer Hill, Jan 29–Feb 19 2026). The authors encode a 14×14 archetype matchup matrix, prove a "popularity paradox" (the most-played deck, Dragapult at 15.5% share, has a sub-50% expected field win rate while Grimmsnarl at 5.1% share leads with 52.7%), derive a machine-checked Nash equilibrium assigning Dragapult zero weight, and run formal replicator dynamics classifying 5 growing and 9 shrinking archetypes. The primary contribution is methodological: demonstrating that proof-carrying analytics can transform qualitative metagame narratives into machine-checkable, reproducible strategic science, bridging game-rule formalization, empirical data, and game-theoretic equilibrium within a single verified artifact (~30K lines, ~2,500 theorems, no `sorry`).

---

## 2. Strengths

**S1. Genuinely novel methodological contribution.** No prior work applies interactive theorem proving to real competitive metagame analysis with empirical tournament data. The paper convincingly demonstrates that proof-carrying analytics is *feasible* for this domain—a non-obvious result given the scale of the artifact (80 files, ~30K LoC, 14×14 matrix). The pipeline from rules formalization → data ingestion → expected-value computation → Nash certification → replicator dynamics → tournament transforms is end-to-end and well-architected. The closest prior work (Li et al. on card-game effects) stops well short of equilibrium computation over real data.

**S2. Rigorous Nash equilibrium certification over a non-trivial game.** The six-deck Nash equilibrium is verified by exhaustive best-response checks over all 14 pure strategies for both players, which is genuinely useful: a 196-cell verification is error-prone by hand. The addition of the symmetrized constant-sum formulation (Section VII, `SymmetricNash.lean`) yielding a seven-deck symmetric equilibrium with game value exactly 500 is a thoughtful response to the asymmetry concern and strengthens the result. The 10,000-iteration sensitivity analysis (Table I) showing core support decks in >96% of resampled equilibria adds credibility.

**S3. Honest and detailed trust-boundary discussion.** The `native_decide` discussion (Section IX-C) is exemplary. The authors explicitly quantify that 244/2,500 theorems rely on `native_decide`, explain that `decide` is structurally precluded by `Fin.foldl` opacity, and articulate the concentrated risk. They also candidly note the Python dependency for the sensitivity analysis and the data provenance trust boundary (Section V-E). This level of transparency is rare and commendable.

**S4. Well-designed robustness analysis.** The "Other" segment robustness bounds (Robustness.lean) are machine-checked and show that Dragapult needs >57.6% win rate against *all* unmodeled archetypes to reach 50% overall—a demanding threshold. The share-perturbation theorems (SharePerturbation.lean) proving the paradox survives across the entire 1–30% Dragapult share range demonstrate structural rather than snapshot-dependent conclusions. Together these address the most natural objections to the headline finding.

**S5. Practical bridge between rules and data.** The ArchetypeAnalysis.lean module connecting the formalized type-effectiveness chart to empirical matchup outcomes (83% alignment, 13/15 Dark→Psychic) is a creative contribution. It demonstrates that the rules formalization is not mere decoration but generates falsifiable predictions. The explicit counter-examples (N's Zoroark losing despite type advantage) and the binomial significance test (p < 0.001) add rigor. This bridge is the strongest argument for why the rules formalization belongs in the same paper as the metagame analysis.

---

## 3. Weaknesses

**W1. Player-skill confounding is acknowledged but not addressed.** The paper treats matchup win rates as reflecting deck properties alone (Section X, "Player-skill confounding"). This is a critical limitation for the headline "popularity paradox" claim. The most popular deck plausibly attracts less experienced players, inflating its loss rate for reasons orthogonal to deck quality. The authors acknowledge this but offer no mitigation—no stratification by player rating, no proxy analysis, not even a back-of-envelope sensitivity estimate for how large the skill effect would need to be to reverse the paradox. For a paper that emphasizes formal rigor, this uncontrolled confound is a significant gap. The Trainer Hill dataset likely contains player Elo or match-point data; even a crude stratification (top-32 finishers vs. field) would substantially strengthen the empirical foundation.

**W2. The 3-week temporal window is insufficiently justified.** The window (Jan 29–Feb 19 2026) is presented as a fixed choice with minimal rationale. Why these exact dates? Was there a set rotation, ban list change, or major event boundary? The paper notes "short windows reduce hidden confounding from major ruleset changes" (Section X) but does not confirm whether any such changes occurred near the window boundaries. The predictive validation (Section VII-A) checks only one day after the window and finds 1/3 predictions wrong (Grimmsnarl declining despite highest predicted fitness). This limited validation cannot distinguish a poor window choice from model limitations. A rolling-window analysis or at minimum a second non-overlapping validation window would be needed to claim temporal robustness.

**W3. The case for formal methods over simpler alternatives is incomplete.** The paper argues three advantages: compositional guarantees, robustness proofs, and reproducibility infrastructure. However:
- **Compositional guarantees:** A Python script checking all 14 best-response conditions is ~20 lines and runs in milliseconds. The claim that this is "error-prone by hand" is true but the relevant comparison is scripted, not manual.
- **Robustness proofs:** The symbolic bounds in Robustness.lean *are* genuinely useful, but interval arithmetic in Python (e.g., `mpmath`) achieves the same with far less effort.
- **Reproducibility:** The strongest argument, but CI/CD pipelines with property-based testing (Hypothesis, QuickCheck) provide comparable drift detection without 30K lines of proof code.

The anecdote about catching data-entry errors during development (Section IX-E) is compelling but narrow. The cost-benefit table (Table VIII: ~30K LoC, ~10 min build vs. ~100 LoC Python) needs more honest framing: under what conditions does the 300× code increase pay for itself?

**W4. Practical value for competitive players is limited.** The paper correctly disclaims competitive-tactical ambitions, stating the contribution is methodological. But this limits the audience for an esports-analytics venue. The headline findings (Dragapult is overplayed, Grimmsnarl is underplayed) are not actionable insights that competitive players couldn't derive from existing community tools like Trainer Hill itself—which already displays win rates and matchup matrices. The Bo3 amplification analysis (Section VIII) is textbook probability. The equilibrium and replicator results are the most novel outputs for players, but the predictive validation (1/3 correct after one day) undermines confidence in their practical utility. The paper would benefit from a clearer articulation of who the target user is.

**W5. The paper is long for its analytical depth.** At 14 pages (IEEE two-column), the paper dedicates substantial space to: (a) rules formalization details that are supporting infrastructure (Section III, ~2 pages), (b) probability/resource theory that is largely standard (Section IV, ~1 page), (c) methodology discussion that, while well-written, repeats the same cost-benefit argument multiple times (Section IX, ~3 pages). The core analytical contributions (Sections VI–VII) could be presented in ~6 pages with the rules and methodology material condensed. Several Lean code listings are transcribed verbatim where a summary would suffice (e.g., the full `dragapult_popularity_paradox` listing in Section VI could be a one-line description pointing to the artifact).

---

## 4. Must-Do Revisions

**M1. Address player-skill confounding with at least one empirical mitigation.** The claim that Dragapult is "suboptimal" is meaningless if its low win rate reflects pilot quality rather than deck quality. Either (a) stratify the matchup matrix by player rating/finish position and show the paradox survives, (b) cite existing PTCG research on the magnitude of pilot-vs-deck effects, or (c) add a formal sensitivity analysis: "the skill effect would need to shift Dragapult's matchups by X percentage points to reverse the paradox." Option (c) is most aligned with the paper's methodology and could be done in Lean.

**M2. Justify the temporal window explicitly.** State whether the window boundaries coincide with set releases, ban announcements, or tournament-circuit phases. Provide at least one additional validation window (even if the Lean verification is not re-run for it). The current 1/3 predictive hit rate after one day is not encouraging and requires either better validation or a frank discussion of why single-step replicator predictions are expected to fail at short horizons.

**M3. Tighten the paper to 11–12 pages.** The current length is not justified by proportional analytical content. Specific cuts: condense Section IV (probability/resources) to ≤0.5 page, merge Sections IX-E and IX-F (case study and continuous monitoring) into a single paragraph, move the full module breakdown table (Table VII) to supplementary material, and reduce inline Lean listings by 40% (point to artifact line numbers instead).

---

## 5. Should-Do Revisions

1. **Fix the Gholdengo em-dash in Table I.** The "—" under "Point Est." for Gholdengo Lunatone is unexplained in the caption. Either add a footnote or include the value (which should be 0.0% if it's outside the baseline support).

2. **Number all code listings consistently.** The replicator dynamics code block on p.8 (right column) lacks a listing number, inconsistent with Listing 1.

3. **Correct the typo in `GrimssnarlFroslass`.** The footnote acknowledging the double-s/single-m inconsistency is appreciated, but consider fixing the identifier in the artifact for the camera-ready version. Typographic bugs in formal artifacts undermine the precision narrative.

4. **Propagate Wilson intervals through expected WR computation.** The paper notes that Wilson intervals are "not directly propagated through the Nash equilibrium computation" (Section V-D). At minimum, propagate them through the expected field WR to report a formal confidence interval on the 46.7% and 52.7% values (which the text does informally as [45.5%, 47.9%] and [51.0%, 54.4%]—make this rigorous or clearly label it as approximate).

5. **Discuss the "Other" segment's strategic composition.** The 30.5% unmodeled share is large. Even a qualitative description of what archetypes comprise it (rogue decks? older archetypes? specific lower-tier strategies?) would help readers assess whether the robustness bounds are plausible.

6. **Clarify the predictive validation methodology.** "One day after the analysis window" (Section VII-A) is vague. Is this based on a single tournament? Aggregate Trainer Hill trends? What sample size? The 1/3 failure (Grimmsnarl declining due to Mega Absol rise) is interesting but needs more methodological detail.

7. **Add a limitations paragraph on the two-player game model.** The paper notes the Swiss-system mismatch (Section VII) but should also discuss that tournament metagames are population games with N>>2 players, where deck selection is a symmetric game and the bimatrix formulation is an approximation. The symmetrized Nash partially addresses this but deserves explicit framing.

8. **Consider presenting the replicator dynamics as a figure.** A time-series plot of share trajectories under iterated replicator steps (even 10–20 steps) would be far more informative than the current text-only presentation and would directly address the concern about single-step vs. trajectory predictions.

---

## 6. Questions for Authors

**Q1.** The sensitivity analysis (Table I) shows the exact Nash support is recovered in only 2.1% of resampled equilibria, yet the paper presents the six-deck equilibrium as a primary result. How should readers interpret a point equilibrium that is fragile to small perturbations? Would a "robust equilibrium" or "ε-equilibrium" framing be more appropriate for the practical conclusions?

**Q2.** You note that `native_decide` is structurally required because `Fin.foldl` is opaque to the Lean 4 kernel reducer. Have you explored reformulating the matrix operations using `Vector` or recursive `List` patterns that *are* kernel-reducible? If so, what were the barriers? This is important for assessing whether the `native_decide` dependency is a fundamental limitation or an engineering choice.

**Q3.** The type-advantage bridge (Section III-A) assigns primary attack and defense types based on "domain-expert" judgment. How sensitive are the alignment results (83%) to these assignments? For instance, Dragapult is classified as Psychic-defending, but Dragapult Charizard variant includes a Fire secondary attacker. If you varied the type assignments within reasonable bounds, would the alignment rate change substantially? A small ablation would strengthen this contribution.

---

## 7. Scores

| Criterion         | Score (1–5) | Justification |
|-------------------|:-----------:|---------------|
| **Novelty**       | 4           | First application of ITP to real competitive metagame analysis with empirical data. The methodological template is genuinely new, though the specific game-theoretic techniques (Nash, replicator) are standard. |
| **Technical Soundness** | 3     | The formal verification is sound modulo `native_decide`, and the authors are transparent about this. However, the empirical foundation has uncontrolled confounds (player skill, temporal locality) that weaken the interpretive claims. The 30.5% unmodeled share is large. |
| **Significance**  | 3           | High significance for the formal-methods-in-games niche; moderate for competitive game science broadly. Limited practical value for players. The methodology template is the lasting contribution, but uptake depends on whether the 300× code overhead is justified for other domains. |
| **Clarity**       | 4           | Well-written with clear structure, honest limitations, and good use of tables/figures. Slightly over-long with repetitive cost-benefit arguments. The trust-boundary discussion is exemplary. Minor formatting inconsistencies (unlabeled listings, Table I em-dash). |
| **Reproducibility** | 5         | Exceptional. Full Lean source, build instructions (`lake build`, ~10 min), exact data constants, and theorem-to-claim traceability. This is the gold standard for reproducibility in this domain. |

---

## 8. Overall Recommendation

### **Weak Accept**

This is a well-executed methodological contribution that demonstrates, for the first time, that proof-carrying analytics can be applied to real competitive game ecosystems at non-trivial scale. The Lean artifact is impressive, the trust-boundary discussion is exemplary, and the reproducibility is exceptional. However, the paper has meaningful empirical gaps (player-skill confounding, thin temporal validation, large unmodeled share) that weaken the interpretive claims, and the cost-benefit case for formal methods over scripted alternatives needs sharper framing. The paper is also 2–3 pages longer than its analytical content warrants. If the authors address M1 (skill confounding mitigation) and M3 (length), this becomes a solid accept—the methodological novelty and artifact quality are sufficient to clear the bar for IEEE Transactions on Games, provided the empirical claims are appropriately hedged or strengthened.
