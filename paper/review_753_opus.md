# Review — Submission #753

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"  
**Venue:** IEEE Transactions on Games  
**Reviewer:** (anonymous)  
**Date:** 2026-02-20

---

## 1. Summary

This paper presents a Lean 4 formalization (~30K lines, 79 files, 2500+ theorems, zero `sorry`) that couples Pokémon TCG rule semantics with real tournament matchup data (Trainer Hill, Jan–Feb 2026) to produce machine-checked metagame analysis. The authors prove a "popularity paradox" — the most-played deck (Dragapult, 15.5% share) has sub-50% expected win rate while the less-played Grimmsnarl achieves 52.7% — and verify a six-deck Nash equilibrium (with zero Dragapult weight), full 14-deck replicator dynamics, and Bo3 amplification results. The primary contribution is methodological: demonstrating that formal verification can transform informal metagame narratives into reproducible, machine-checkable strategic science.

---

## 2. Strengths

1. **Novel methodological contribution.** This is, to my knowledge, the first formally verified metagame analysis of a competitive card game grounded in real tournament data. The idea of "proof-carrying analytics" for competitive game ecosystems is genuinely new and well-articulated.

2. **Substantial, high-quality artifact.** The Lean development is impressively scoped: 79 project files, ~30K lines, 2,555 theorems/lemmas, with zero `sorry`/`admit`/custom axioms verified by independent grep of the source tree. The artifact structure is well-organized with clear module boundaries (rules, probability, game theory, empirical analysis).

3. **End-to-end verified pipeline.** The chain from data encoding → expected value computation → Nash equilibrium certification (including all 196 best-response cells) → replicator dynamics → Bo3 amplification is fully machine-checked. The Nash certification over 14 pure strategies with explicit best-response quantification for both players is nontrivial and valuable.

4. **Honest and thorough threats-to-validity section.** The paper is admirably transparent about the trust boundary (`native_decide`), temporal locality, top-14 normalization, the "Other" 30.5%, and the mismatch between the single-match payoff model and Swiss-system tournament objectives. The robustness analysis (worst-case bounds on the "Other" segment, share perturbation theorems, 10K-iteration sensitivity analysis) is more rigorous than typical applied game theory papers.

5. **Dual Nash formulations.** Presenting both the bimatrix Nash (which reveals asymmetric row/col supports due to tie weighting) and the symmetrized constant-sum Nash (which gives the population-game interpretation with a 7-deck support) demonstrates methodological care and addresses an obvious criticism proactively.

6. **Clean paper↔artifact correspondence.** Spot-checking confirms that theorem names, line references, and numeric values in the manuscript match the Lean source. The traceability case study (Section IX-F) is an exemplary description of formal methods workflow.

7. **Predictive validation attempt.** Including a (partial) out-of-sample test of replicator predictions — and honestly reporting the Grimmsnarl failure due to multi-step cascade effects — adds scientific credibility rather than diminishing it.

8. **Well-written.** The paper is generally clear, well-organized, and appropriately scoped. The motivating tournament scenario effectively grounds the formalism.

---

## 3. Weaknesses

### Critical

*(None identified.)*

### Major

**M1. The rules formalization is loosely connected to the empirical analysis.** The paper claims the rules layer provides "structural integrity checks on the data pipeline" and ensures "only tournament-legal configurations enter the analysis." However, the actual matchup matrix is sourced from Trainer Hill as a black box — the rules formalization never actually validates or derives any matchup win rate. The deck legality checker `checkDeckLegal_iff` validates deck *structure*, not the provenance of empirical win rates. The paper acknowledges this ("the rules layer is supporting infrastructure rather than the primary empirical claim") but the Section III presentation still overstates the connection. The rules formalization is interesting future infrastructure; its contribution to the *present* paper's empirical claims is minimal. **Recommendation:** Either scale back rules formalization to ≤1 page and reframe as "infrastructure for future work," or demonstrate a concrete instance where the rules layer catches or prevents a data-pipeline error.

**M2. Limited novelty in the game-theoretic results themselves.** The popularity paradox (most-played ≠ highest-EV) is a well-known phenomenon in competitive gaming communities and follows straightforwardly from weighted averaging. The Nash equilibrium computation is a standard LP. The replicator dynamics are textbook. The novelty is *that these are formally verified*, but the underlying strategic insights are not new to the game theory or esports analytics literature. The paper would benefit from more clearly delineating what is novel (the verification methodology) from what is routine (the game theory).

**M3. Sensitivity analysis is external to Lean.** The 10,000-iteration sensitivity analysis — arguably the most important robustness check — is performed in Python and explicitly marked as "external to the Lean-verified theorems." This is the paper's Achilles' heel: the strongest evidence for robustness comes from the unverified component. The authors acknowledge this and propose future Lean-internal interval arithmetic, but it weakens the "everything is machine-checked" narrative. Table I results should be more clearly flagged as unverified.

**M4. Single-step replicator dynamics are of limited predictive value.** The predictive validation (Section VII-A) shows 2/3 directional hits but fails on the headline prediction (Grimmsnarl). The authors correctly diagnose the multi-step cascade issue, but this undermines the practical utility of the replicator results. Since the paper positions replicator dynamics as a key contribution, the demonstrated failure to capture even one-step-ahead dynamics for the top-fitness deck is a significant limitation.

### Minor

**m1. Figure quality.** Figure 1 uses a LaTeX `picture` environment with manual coordinate placement. The TODO comment ("Replace picture environment with TikZ/pgfplots for camera-ready") is still in the source. For a journal submission, this needs proper data visualization. The figure is also missing several of the 14 archetypes.

**m2. The `optimize_proof` macro obscures proof strategy.** The paper says `optimize_proof` expands to `native_decide`, but this indirection is unnecessary and potentially confusing. If the macro exists purely for build-time performance, this should be stated explicitly. As written, it reads like there might be additional proof engineering hidden behind the macro.

**m3. Mirror match win rates below 50%.** The footnote explaining why mirror matches are sub-50% (tie convention) is important but buried. This is a non-obvious artifact of the $T/3$ weighting that could confuse readers. Consider promoting to main text or adding a brief worked example.

**m4. The "Behavioral-Economic Interpretation" subsection (VI-B) is speculative.** Citations to Kahneman, Tversky, Banerjee, and Bikhchandani are appropriate but the connection to this specific dataset is entirely hypothetical. The paper acknowledges this ("we do not claim causal identification") but the section is still somewhat overextended for what it delivers.

**m5. Module statistics double-counting or inflation concern.** The paper claims ~30K lines and 2,510 theorems. My grep of the project directory yields 30,441 lines and 2,555 theorems — close but not matching. The discrepancy is small but should be reconciled for a journal paper claiming formal precision. Also, the "Additional Specialized Modules" row in Table VII (35 files, 1,284 theorems) is opaque — what do these modules contain? Some may be boilerplate or auto-generated infrastructure that inflates the count.

**m6. Theorem statement in Listing 1 vs. prose.** The paper states Dragapult has "losing matchups against 9 of 13 non-mirror decks," but the Lean theorem `dragapult_popularity_paradox` only shows 9 conjuncts with `matchupWR < 500`. This is consistent but the theorem name suggests the *paradox* whereas the theorem body only proves losing matchups. The actual expected-value computation that constitutes the paradox appears elsewhere. Naming could be more precise.

**m7. Swiss-system modeling is shallow.** Section VIII mentions the Swiss cut-line probability formula but does not verify it in Lean or connect it to the Nash analysis. The iid rounds assumption underlying the binomial formula is acknowledged as approximate but not analyzed further.

**m8. No comparison with alternative verification approaches.** The paper does not discuss why Lean 4 was chosen over alternatives (Coq, Isabelle, Agda) or whether the methodology is portable. A brief discussion of trade-offs would strengthen the methodological contribution.

### Typographical / Presentation

**t1.** The identifier `GrimssnarlFroslass` (single-m, double-s) is acknowledged in a footnote but should ideally be fixed in the artifact for the camera-ready version, as it introduces a gratuitous inconsistency.

**t2.** Table II caption says "Top-6 subset view" but the table shows 6 archetypes from a 14-archetype matrix without explaining the selection criterion.

**t3.** The Wilson interval formula in Section V-D has a presentation issue: the $\tilde{p} \pm$ expression gives the interval bounds but the text doesn't clearly state that $\hat{p}$ is the raw sample proportion.

**t4.** In Section VII (Nash), the paper says `realNashValue ≈ 479.665` (on the 0–1000 scale) which is 47.97%. The text then says "sub-50% game value reflects the tie convention." This connection could be made more explicit — specifically, the theoretical game value of a perfectly constant-sum game is 500, and the deviation is quantified.

**t5.** Reference [19] (Kowalski & Miernik) has a year discrepancy: published 2023 but cited as `kowalski2020summon`. The BibTeX key should match the actual year.

---

## 4. Questions for Authors

**Q1.** Can you provide a concrete example where the rules formalization (deck legality, card conservation) actually caught or prevented an error in the metagame analysis pipeline? If not, how do you justify its prominence in the paper (dedicated section, contribution claim)?

**Q2.** The symmetric Nash has 7-deck support while the bimatrix Nash has 6-deck support per player. Is Gholdengo's appearance only in the symmetric formulation (and the column support) an artifact of the symmetrization, or does it reflect genuine strategic relevance?

**Q3.** You mention `Fin.foldl` is opaque to the Lean 4 kernel, precluding `decide`. Have you investigated reformulating your matrix operations using kernel-transparent recursive definitions? What is the estimated engineering effort?

**Q4.** The 10,000-iteration sensitivity analysis finds the exact support set in only 2.1% of iterations. Does this suggest the Nash equilibrium is essentially degenerate, with multiple near-optimal support configurations? If so, how does this affect the practical recommendations?

**Q5.** Your predictive validation covers a single one-day-ahead check. Do you have access to subsequent weekly snapshots that could provide a more systematic evaluation of the replicator predictions?

**Q6.** The paper normalizes over the top-14 (69.5% of field). Have you considered a 15th "Other" archetype with a parametric win-rate profile, rather than excluding it entirely? This would allow the Nash computation to account for the residual field.

---

## 5. Overall Recommendation

**Weak Accept**

### Justification

This is a well-executed, clearly written paper with a genuinely novel methodological contribution: the first formally verified metagame analysis of a real competitive game using a modern proof assistant. The artifact is impressive in scope and quality. The paper is honest about limitations and demonstrates commendable scientific discipline.

However, the game-theoretic results themselves are straightforward applications of standard techniques to a specific dataset, and the rules formalization — while interesting as infrastructure — is loosely coupled to the empirical claims. The most critical robustness analysis (sensitivity) lives outside Lean, partially undermining the verification narrative. The predictive validation, while admirably included, demonstrates a notable failure mode.

The paper is above the acceptance threshold for IEEE Transactions on Games because (a) the proof-carrying analytics methodology is novel and portable, (b) the artifact quality is exceptional, and (c) the domain application (competitive TCGs) is squarely within scope. Addressing M1 (tightening the rules-to-analysis connection or reducing its prominence) and m1 (figures) would meaningfully strengthen the camera-ready version. The paper would move to a clear Accept if the sensitivity analysis were brought inside Lean, but this is acknowledged as future work and is not a blocking issue.

The work opens a productive research direction at the intersection of formal methods and competitive game science, and the artifact represents a significant community resource.
