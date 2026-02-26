# Review — IEEE Transactions on Games (Submission #753)

**Paper Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game

**Reviewer Confidence:** High (familiar with formal verification in Lean 4, game theory, and competitive TCG metagame analysis)

---

## 1. Summary

This paper presents a formally verified metagame analysis pipeline for the Pokémon Trading Card Game, implemented in Lean 4 (~30K lines, 80 files, 2,500+ theorems, zero `sorry`). Using real Trainer Hill tournament data (Jan–Feb 2026) over a 14-archetype pairwise matchup matrix, the authors prove a "popularity paradox" (the most-played deck, Dragapult at 15.5% share, has only 46.7% expected field win rate), compute and machine-check a Nash equilibrium that assigns Dragapult 0% weight, verify full 14-deck replicator dynamics, and perform sensitivity analysis. The primary contribution is methodological: demonstrating that formal verification can transform informal metagame narratives into machine-checkable, reproducible strategic science.

---

## 2. Strengths

1. **Ambitious and novel integration of formal methods with empirical game analysis.** To my knowledge, this is the first work to machine-check Nash equilibrium certification and replicator dynamics over real tournament data in a proof assistant. The methodological template (formalize rules → encode data → prove strategic claims) is genuinely portable and could influence future work in computational game science.

2. **Impressively complete artifact.** The zero-`sorry`, zero-`admit`, zero-axiom standard across ~30K lines and 2,500+ theorems is a strong engineering achievement. The artifact covers game rules, card effects, probability, resource theory, matchup analysis, Nash equilibrium (bimatrix + symmetric), full 14-deck replicator dynamics, robustness bounds, and tournament transforms. The reviewed source files (`NashEquilibrium.lean`, `FullReplicator.lean`, `SymmetricNash.lean`, `RealMetagame.lean`) are well-structured and readable.

3. **Thorough treatment of the Nash equilibrium.** The paper does not merely claim an equilibrium; it machine-checks best-response conditions for all 14 pure strategies for both players, presents both the bimatrix and symmetrized constant-sum formulations, and correctly identifies that the row/column support difference arises from the non-constant-sum tie convention. The symmetrized equilibrium (seven-deck support, game value exactly 500) is a clean confirmation.

4. **Honest and well-articulated threat model.** The paper is commendably explicit about the trust boundary (`native_decide` vs. `decide`, data provenance from Trainer Hill, top-14 normalization, temporal locality). The robustness section with worst-case bounds and 10,000-iteration sensitivity analysis is more rigorous than most empirical game-theory papers.

5. **Strong uncertainty quantification.** The Wilson intervals, the sensitivity analysis with inclusion rates (Table 1), and the share-perturbation theorems collectively provide a multi-layered argument for robustness. The distinction between "point estimate verified in Lean" and "sensitivity analysis in Python" is honestly disclosed.

6. **Excellent paper–artifact correspondence.** Theorem names in the paper directly match those in the Lean source. The case study in §VIII-F (end-to-end traceability of a headline claim) is a model of how formal verification papers should document their methodology.

7. **Well-written and well-organized.** The paper is clear, logically structured, and avoids overclaiming. The behavioral-economic interpretation (§VI-B) is appropriately hedged.

---

## 3. Weaknesses

### Critical

*(None identified.)*

### Major

**M1. The rules formalization is loosely coupled to the empirical analysis.**
The paper devotes §III to game rules, card effects, and conservation theorems, but acknowledges that "the rules layer is supporting infrastructure rather than the primary empirical claim." The connection between the type effectiveness triangle or Professor's Research conservation and the 14×14 matchup matrix is conceptual, not formal—there is no Lean theorem linking rule-level semantics to observed win rates. This is intellectually honest but weakens the contribution: the rules formalization is a separate (and less novel) artifact that does not mechanically constrain or derive the empirical analysis. The paper would benefit from being more forthright that these are essentially two parallel contributions sharing a codebase, rather than a single pipeline.

**M2. The "popularity paradox" is a well-known phenomenon dressed in formal clothing.**
The observation that the most popular strategy in a game need not be the highest-EV strategy is a standard result in behavioral game theory and has been documented in TCG communities for years. The paper acknowledges this ("The contribution is not the phenomenon itself but its formal verification"), but the novelty bar for a journal paper requires more than formally verifying a known fact. The verification methodology is novel; the specific metagame insight is not. The paper should more sharply delineate what is new (the pipeline) from what is confirmatory (the paradox).

**M3. Limited predictive validation.**
Section VII-A reports predictive validation against one day of post-window data with 2/3 correct directional predictions. This is too thin to assess predictive power. Worse, the one failure (Grimmsnarl declining despite highest fitness) reveals a fundamental limitation of single-step replicator analysis that is acknowledged but not formally addressed. For a journal-length paper, a rolling-window validation over several weeks would substantially strengthen the empirical contribution.

**M4. The 30.5% "Other" exclusion is a significant modeling gap.**
Nearly a third of the field is excluded from the payoff matrix. While the robustness analysis shows Dragapult would need ≥57.6% vs. Other to reach 50% overall, the Nash equilibrium is computed over a 14-deck subgame that may not reflect equilibrium behavior in the full field. The paper correctly identifies this as a limitation but does not explore how the equilibrium support might change if even 2–3 additional archetypes were included. This is especially relevant because several "Other" archetypes may have extreme matchup profiles against Nash-support decks.

### Minor

**m1. `native_decide` trust assumption deserves more discussion.**
The paper correctly notes that `Fin.foldl` is opaque to the kernel, precluding `decide`. However, the trust implications of `native_decide` (relying on Lean's compiler codegen correctness) are somewhat underplayed. While `native_decide` is standard practice, a paragraph comparing the trust level to, e.g., verified extraction in Coq/OCaml or reflective tactics in Isabelle would help readers assess the guarantee level.

**m2. The scatter plot (Figure 1) is drawn in LaTeX `picture` environment.**
The TODO comment ("Replace picture environment with TikZ/pgfplots for camera-ready") is still present. For a journal submission, this should use proper plotting infrastructure. More importantly, only 6 of 14 decks are plotted, which understates the density of the C-tier cluster and could mislead readers about the paradox's structure.

**m3. The paper claims ~80 files but the artifact has 85+ `.lean` files.**
The `find` command returns a large file count. The discrepancy between the paper's "80 files" and the actual count should be reconciled. Table VI reports 80 files / 29,793 lines; the actual line count appears consistent but file count may have drifted.

**m4. Replicator dynamics time-step choice (dt = 1/10) is arbitrary.**
The discrete replicator step uses `dt = 1/10` without justification. While the qualitative direction (above/below average fitness) is dt-independent, the magnitude of share changes and conservation properties should be discussed. The paper proves `full_replicator_step_conservation` (sum = 1 after one step), but does not discuss whether this holds for all dt or only specific values.

**m5. The tie convention (T/3) deserves more scrutiny.**
The paper notes that mirror win rates fall below 50% due to the tie convention but does not explore alternatives (e.g., T/2 or excluding ties). Since the tie convention affects the constant-sum deviation and thus the bimatrix vs. symmetric equilibrium difference, a brief sensitivity comparison would be informative.

**m6. Several expected-WR values in Table IV appear surprisingly low.**
Ten of 14 decks have expected WR below 50%. This is mathematically possible due to the tie convention depressing the overall average below 50%, but it should be explicitly discussed—readers may find it counterintuitive that only 4 of 14 decks are "above average."

**m7. The Bo3 section (§VII) is somewhat detached from the main analysis.**
The Bo3 amplification is verified for generic probabilities but is not applied back to the Nash equilibrium or replicator dynamics. A Bo3-adjusted Nash equilibrium would be a stronger contribution.

### Typographic

**t1.** The Lean identifier `GrimssnarlFroslass` (single-m, double-s) is noted in a footnote but is distracting. Consider a Lean-level `abbrev` alias for presentation clarity.

**t2.** The `optimize_proof` macro is described as "project-local" but is simply `native_decide`. The indirection adds complexity without benefit; consider using `native_decide` directly in displayed listings for transparency.

**t3.** Table III caption says "Cross-tier subset view" but the tier labels (S/A/B/C) are not defined until Table IV.

**t4.** The paper uses both "six-deck support" and "seven-deck support" in different contexts (bimatrix vs. symmetric) without always clarifying which formulation is meant. A consistent convention would help.

---

## 4. Questions for Authors

1. **Could you formalize the connection between rule-level semantics and matchup win rates, even for a single archetype pair?** For example, proving that Dragapult's type weakness to [some type] implies a structural disadvantage against Gardevoir would close the gap between §III and §VI.

2. **What is the build time for the full artifact on commodity hardware (e.g., 8-core x86)?** The paper mentions ~10 minutes on Apple M-series; CI reproducibility on standard academic infrastructure matters.

3. **Have you considered formalizing the sensitivity analysis within Lean using interval arithmetic?** You mention this as future work—how far is current Mathlib from supporting the required LP operations?

4. **For the replicator dynamics, do the qualitative predictions (growers/shrinkers classification) remain identical under iterated steps (k=10, 100)?** The paper only verifies single-step direction.

5. **The symmetric Nash has 7-deck support while the bimatrix has 6-deck support per player. Is this difference solely due to the symmetrization, or does it also reflect numerical sensitivity?** The sensitivity analysis (Table 1) shows Gholdengo at 40.5% inclusion, suggesting it is near-marginal.

6. **Why not include win-loss-tie triples in the Lean encoding rather than pre-computed WR values?** This would allow in-Lean confidence interval computation and eliminate one step from the trust boundary.

---

## 5. Overall Assessment

This is a well-executed paper that makes a genuine methodological contribution: it demonstrates, for the first time, that formal verification can be practically applied to real-world metagame analysis at journal scale. The artifact is impressive in scope and rigor (zero sorry across ~30K lines), the game-theoretic analysis is sound, and the paper is honest about limitations.

The main weaknesses are: (a) the rules formalization and the empirical analysis are loosely coupled, (b) the specific metagame findings are confirmatory rather than surprising, (c) predictive validation is thin, and (d) the 30.5% field exclusion is a non-trivial modeling gap. None of these are fatal, but together they somewhat limit the depth of the contribution for a top venue.

The paper is strongest as a methodological demonstration and weakest as an empirical game-theory contribution. The authors should consider whether foregrounding the pipeline methodology even more (perhaps with a brief second domain to show portability) would strengthen the submission.

---

## 6. Overall Recommendation

**Weak Accept**

The paper is above the acceptance threshold on novelty (first formally verified metagame analysis), rigor (zero-sorry artifact with machine-checked Nash equilibrium), and presentation quality. The weaknesses (loose rules–data coupling, thin predictive validation, known paradox phenomenon) prevent a stronger recommendation but do not outweigh the methodological contribution. I would support acceptance conditional on addressing M2 (sharper novelty delineation), m2 (proper figures), and m6 (explicit discussion of the sub-50% average effect).

---

*Reviewer: Anonymous (IEEE ToG Review #753)*
*Date: 2026-02-20*
