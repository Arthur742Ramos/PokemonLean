# Review — Submission #753 (v3)

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"
**Venue:** IEEE Transactions on Games
**Reviewer:** R3 (anonymous)
**Date:** 2026-02-20
**Expertise:** Competitive card game AI, esports analytics, theorem proving (Lean 4 / Coq)

---

## Scores

| Criterion        | Score | Notes |
|------------------|:-----:|-------|
| Novelty          | 3     | First-of-kind methodology; routine game theory underneath |
| Technical Soundness | 4   | Machine-checked core; external sensitivity analysis weakens guarantee chain |
| Significance     | 3     | Promising template, limited demonstrated impact on actual competitive play |
| Clarity          | 3     | Dense but honest; code-heavy for a ToG audience |
| Reproducibility  | 5     | Exceptional: zero-sorry Lean artifact, concrete data, ~10 min build |

---

## 1. Summary

The paper formalizes a 14-archetype Pokémon TCG metagame (Trainer Hill, Jan–Feb 2026) in ~30K lines of Lean 4 with 2,567 theorems and zero `sorry`. The core pipeline is: encode a 14×14 matchup matrix from tournament data → prove a "popularity paradox" (Dragapult, 15.5% share, has only 46.7% field EV) → certify a Nash equilibrium (6-deck support, Dragapult weight = 0) → run full 14-deck discrete replicator dynamics → perform sensitivity analysis. A new v3 contribution (`ArchetypeAnalysis.lean`) bridges the rules formalization to empirical data by assigning primary types to archetypes and showing 83%+ alignment between the type chart and observed matchup winners. The paper claims this constitutes "proof-carrying analytics" for competitive games.

---

## 2. Strengths

**S1. Genuinely novel methodology.** To my knowledge, no prior work machine-checks Nash equilibrium certification and evolutionary dynamics over real tournament data in a proof assistant. The "proof-carrying analytics" framing is compelling and the template is clearly portable — the abstract game-theoretic machinery (replicator dynamics, best-response verification over `Fin n`) is game-agnostic. This is a real methodological contribution.

**S2. Exceptional artifact rigor and reproducibility.** I verified via grep that `sorry`, `admit`, and custom axioms are absent from proof-bearing positions across 78 files and 30,146 lines. The 2,567 theorem/lemma count is consistent with the source. The modular architecture (rules → probability → data → equilibrium → dynamics → robustness) is well-factored. The `native_decide` trust boundary is clearly documented. This is the gold standard for artifact quality in a games paper.

**S3. Complete Nash certification is nontrivial.** Checking best-response conditions for all 14 pure strategies for both players — 196 inequality verifications — is genuinely error-prone by hand or even in a "well-tested Python script." The dual formulation (bimatrix with 6-deck support vs. symmetrized constant-sum with 7-deck support and game value exactly 500) demonstrates methodological care and addresses the natural concern about tie-induced asymmetry. The proof that a natural candidate (Mega Absol + Dragapult two-deck profile) is *not* a Nash equilibrium via an explicit Raging Bolt deviation is a clean illustration of the verification's value.

**S4. Honest and thorough uncertainty treatment.** The paper is admirably explicit about what is and is not verified: Wilson intervals, the 10K-iteration sensitivity analysis (Python, external to Lean), the `native_decide` trust boundary, the 30.5% "Other" exclusion, temporal locality, and Swiss-system modeling limitations. The worst-case robustness bounds for the "Other" segment and the share-perturbation theorems are more careful than typical esports analytics papers. The 2.1% exact-support recovery rate in sensitivity analysis is reported rather than hidden.

**S5. The v3 bridge (`ArchetypeAnalysis.lean`) is a meaningful improvement.** Having reviewed the actual source, the bridge does more than is obvious from the paper description. It formally connects type assignments → weakness predicates → empirical matchup directions for 18 type-advantaged pairs, proves 83% alignment, and — critically — documents the 3 counter-examples (NsZoroark×Dragapult at 490, NsZoroark×DragapultCharizard at 391, CharizardNoctowl×Gholdengo at 480) with mechanistic explanations. The `dragapult_type_vulnerability` theorem linking rules-level weakness + population share + all three Dark attackers winning is the strongest single bridge result.

**S6. Predictive validation is included and honest.** The comparison against post-window trend data with 2/3 directional accuracy — and the transparent report that the headline prediction (Grimmsnarl decline despite highest fitness) failed due to multi-step cascading — demonstrates scientific integrity rather than undermining the paper.

**S7. The matchup matrix reveals genuine strategic structure.** The data itself is interesting: Alakazam vs. Kangaskhan at 77.2%/19.8% is one of the most extreme matchup polarities I have seen in a competitive TCG dataset, and the extended rock-paper-scissors cycle (RagingBolt > MegaAbsol > Grimmsnarl > Dragapult > CharizardNoctowl > Gardevoir > Dragapult) is formally verified and strategically informative.

---

## 3. Weaknesses

### Major

**M1. Practical value for competitive players is undemonstrated and likely weak.**
The paper positions itself as producing "actionable strategic recommendations," but a competitive player or team would gain the same insights — Dragapult is overplayed, Grimmsnarl has the best matchup spread, the Nash equilibrium excludes Dragapult — from 30 minutes with a spreadsheet and the same Trainer Hill data. The formal verification adds epistemic guarantees that the arithmetic is correct, but competitive players' uncertainty is dominated by (a) the data's temporal validity (3-week window), (b) the 30.5% unmodeled field, and (c) their own skill differentials in specific matchups — none of which Lean addresses. I would like the authors to name a specific strategic decision that a player or team would make differently because of the formal verification, as opposed to the same analysis in Python/Excel. Without this, the "practical value" claim is aspirational rather than demonstrated.

**M2. The bridge is formally sound but intellectually thin.**
Having examined `ArchetypeAnalysis.lean` in detail, I must note that every theorem reduces to `decide` or `native_decide` over hardcoded constants. The "bridge" is: (1) manually assign types to archetypes (a lookup table), (2) check `weakness` (a lookup table), (3) compare `matchupWR` to 500 (a lookup table). There is no predictive model, no quantitative bound on the *magnitude* of type advantage's effect, and no formal connection to the damage-doubling mechanics of weakness. The 83% alignment figure is computed by counting conjuncts — it is not a statistical test, has no confidence interval, and has no null model (what alignment would random type assignments achieve?). Any TCG player knows "Dark beats Psychic"; the formal verification adds that the Lean compiler agrees with this assessment. The counter-examples (Section 6 of the file) are more interesting than the confirmations, but they are explained informally in comments rather than formally. **Recommendation:** Either formalize a quantitative model (e.g., type advantage implies WR ≥ 500 + δ for some proven δ) or provide a proper statistical test with a null hypothesis.

**M3. Missing baselines make the 30K-line overhead unjustifiable.**
The paper provides no comparison to simpler methods. A Python script computing the same Nash equilibrium via `scipy.optimize.linprog` would be ~50 lines, run in milliseconds, and produce identical numerical results. The `nashpy` library can certify support enumeration with vertex enumeration in <100 lines. The replicator dynamics are 10 lines of NumPy. The paper must argue why 30K lines of Lean (a 300-600× expansion factor) are worth the engineering investment. The argument "formal verification catches arithmetic errors" would be compelling if the authors could point to a single error that was caught during development — if none were, the verification confirmed what testing would have confirmed, at vastly greater cost. The argument "this is infrastructure for future work" is valid but should be stated as such.

**M4. No portability demonstration weakens the generality claim.**
The paper claims the methodology is "portable to Magic: The Gathering, Yu-Gi-Oh!, and Hearthstone," but does not demonstrate this even minimally. The type-assignment bridge is specific to Pokémon TCG's single-weakness system; MTG's five-color mana system, Yu-Gi-Oh!'s attribute/type interactions, and Hearthstone's class system are structurally different. A brief worked example showing how the abstract game-theoretic layer (which *is* game-agnostic) could be instantiated for a 5-archetype MTG metagame would substantially strengthen this claim.

**M5. The sensitivity analysis — the paper's most important robustness argument — lives outside Lean.**
The 10,000-iteration sensitivity analysis is performed in Python and explicitly noted as external to the verified chain. This is the paper's central tension: the most compelling evidence for the Nash equilibrium's robustness (core support decks appear in >96% of iterations) comes from the unverified component, while the verified component certifies a point estimate that the sensitivity analysis shows is fragile (exact support in 2.1% of iterations). The paper handles this honestly, but it undercuts the verification narrative. If the claim is "you should trust these results because they are machine-checked," then the robustness results — arguably the ones that matter most for practical recommendations — are not machine-checked.

### Minor

**m1. Figure 1 is below publication standard.** The LaTeX `picture` environment with manual coordinates and a TODO comment ("Replace picture environment with TikZ/pgfplots for camera-ready") is present in the source. Only 6 of 14 archetypes are plotted. For IEEE ToG, this needs proper data visualization with all 14 points, axis labels, gridlines, and tier-shading regions.

**m2. Comparison to existing metagame tools is superficial.** Limitless TCG already provides matchup matrices, expected win rates, and metagame share trends — the same raw analysis pipeline — for free, updated daily, covering 100% of the field. HSReplay provides Bayesian matchup estimates with confidence intervals for Hearthstone. The paper does not adequately explain what the formal verification layer provides *beyond* these existing tools. A direct comparison (Table: Limitless features vs. this paper's features, with the formal verification column highlighted) would make the contribution crisper.

**m3. The `optimize_proof` macro is an unnecessary abstraction.** Inspecting the source, `optimize_proof` is literally `native_decide`. The macro name suggests "optimization" when the actual content is a trust-boundary decision. Using `native_decide` directly in listings would be more transparent, and the current indirection may cause readers to suspect hidden proof engineering.

**m4. Temporal validity is not addressed structurally.** The 3-week data window (Jan 29 – Feb 19, 2026) spans a single format with no set releases or ban list changes. The paper acknowledges temporal locality but does not discuss how the verified results would be invalidated by a new set release (which would require re-encoding the entire matchup matrix and re-proving every theorem). If the infrastructure is meant for "continuous monitoring" (Section VIII-G), the re-verification cost per metagame update should be estimated.

**m5. The replicator dynamics use dt = 1/10 without justification.** While the directional predictions (above/below average fitness) are dt-independent, the magnitude of predicted share changes depends on dt. The paper proves share conservation for this specific dt but does not discuss whether results are qualitatively stable across dt ∈ {1/100, 1/10, 1/2, 1}. The `replicatorIter` function is defined in the source but multi-step trajectories are not analyzed.

**m6. The "behavioral-economic interpretation" (Section VI-B) is speculative padding.** The citations to Kahneman/Tversky and herding literature are appropriate but the connection to this specific dataset is entirely hypothetical. The paper correctly hedges ("we do not claim causal identification"), but the section consumes ~0.5 pages that could be better used for baseline comparisons or portability demonstrations.

**m7. Code listings consume excessive page space.** For a 13-page IEEE ToG paper, the balance tilts too heavily toward Lean code. The ToG readership includes game designers, AI researchers, and esports analysts who are unlikely to read Lean syntax. Consider moving detailed listings to a supplementary appendix and replacing them with pseudocode or structured prose descriptions of key theorem statements.

**m8. The paper does not discuss Nash equilibrium uniqueness.** For a 14-strategy bimatrix game, multiple equilibria are generic. The sensitivity analysis indirectly addresses this (different matrices → different supports), but a direct discussion of whether the point-estimate equilibrium is unique — or one of many — would strengthen the game-theoretic analysis.

---

## 4. Questions for Authors

**Q1.** Can you name a specific strategic decision that a competitive player or team would make differently because of the formal verification, as opposed to the same numerical analysis in an unverified Python script? (This is the key question for practical significance.)

**Q2.** The bridge claims 83% alignment between type advantage and empirical matchup winners. What alignment would you expect under a null model where type assignments are random permutations of the actual assignments? If the null gives 50% (since you are checking > 500 on a near-symmetric matrix), then 83% is 15/18 and a binomial test gives p ≈ 0.001 — but this calculation is absent from both the paper and the Lean formalization. Can you formalize or at least report it?

**Q3.** The `replicatorIter` function is defined in the artifact but multi-step trajectories are not analyzed. Have you run 5-step or 10-step iterations? If so, does the Grimmsnarl decline (observed empirically) eventually appear via the Mega Absol cascade?

**Q4.** What is the estimated engineering effort (person-hours or person-weeks) to update the analysis for a new metagame snapshot (e.g., after a set release changes the matchup matrix)? This is critical for the "continuous monitoring" claim.

**Q5.** Have you attempted to instantiate the abstract game-theoretic layer for a non-Pokémon TCG (even a toy 3-archetype MTG metagame) to validate portability? If not, what would be required?

---

## 5. Detailed Assessment of Focus Areas

### 5.1 Practical Value (Rating: Low-Medium)

The methodology is intellectually sound but the practical value proposition for competitive players is thin. Competitive TCG players already have access to matchup matrices (Limitless, Play Pokémon), expected win rates (Trainer Hill), and informal Nash-style reasoning ("play the deck that beats the popular decks") through community analysis. The formal verification guarantees that the arithmetic is correct, but arithmetic errors in a 14×14 spreadsheet are easily caught by cross-validation (row/column sums, mirror match checks). The real sources of uncertainty — data staleness, unmodeled archetypes, skill-dependent matchup variance — are outside the verification boundary.

The methodology *would* become practically valuable if: (a) the data ingestion were automated and the re-verification time were fast enough for weekly updates, (b) the analysis covered the full field (not just 69.5%), or (c) the rules formalization were deep enough to predict matchup shifts from card pool changes before tournament data is available.

### 5.2 Novelty vs. Existing Tools

Limitless TCG provides: matchup matrices (full field), metagame shares (daily), trend plots, deck lists, and tournament results. It does not provide: Nash equilibria, replicator dynamics, or formal verification. HSReplay (Hearthstone) additionally provides Bayesian win-rate estimates with credible intervals and automated archetype classification.

The paper's novelty lies in: (a) the formal verification layer (unique), (b) the Nash equilibrium certification (not available from existing tools), and (c) the replicator dynamics (available as informal community analysis but not formally verified). The bridge from rules to data is the weakest novel contribution — it formalizes common knowledge.

A well-tested Python script with unit tests would achieve 95% of the practical value at 1% of the engineering cost. The remaining 5% — the guarantee that no arithmetic error exists in the Nash certification — is genuinely valuable for publication (reproducibility, trust) but marginally valuable for competitive practice.

### 5.3 Bridge Quality

The bridge is mechanically correct and the v3 additions address a real gap in earlier versions. However, the intellectual depth is limited:

- **Type assignment** is manual (a 14-entry lookup table). No formal criterion determines whether Dragapult is "Psychic" or "Dragon" — the paper chooses based on competitive context, which is reasonable but subjective.
- **Alignment checking** is Boolean (WR > 500 or not). A more interesting bridge would prove quantitative bounds: "type advantage implies WR ≥ 500 + δ" for some provable δ, or relate the damage-doubling mechanic to expected percentage-point advantages.
- **Counter-examples** are the most interesting part. The formal proof that NsZoroark has Dark-type advantage over Dragapult but loses (490) demonstrates that deck construction overrides type advantage. But the explanation is in comments, not in formal statements.
- **No null model.** Without knowing what alignment rate random type assignments would produce, the 83% figure lacks statistical context.

The bridge is not trivial (it required thoughtful type assignments and documenting exceptions), but it is not deeply novel either. It formalizes folk knowledge rather than generating new strategic insight.

### 5.4 Missing Baselines

This is a significant gap. The paper should include a table:

| Method | Lines of Code | Time to Result | Catches Arithmetic Errors | Catches Modeling Errors | Nash Certification |
|--------|:---:|:---:|:---:|:---:|:---:|
| Spreadsheet EV | ~50 cells | 30 min | Manual review | No | No |
| Python + scipy | ~100 | <1s | Unit tests | No | No |
| Monte Carlo (1M sims) | ~200 | ~10s | Statistical | Partially | Approximate |
| Lean 4 (this paper) | ~30K | ~10 min build | Formal proof | No | Machine-checked |

Without this comparison, the reader cannot assess the cost-benefit tradeoff. The 30K lines are justified primarily as a *research contribution* (demonstrating feasibility of the methodology), not as a *practical tool* — but the paper should say this explicitly.

### 5.5 Presentation Balance

The paper is too code-heavy for IEEE ToG. I estimate ~3 pages of Lean listings that could be compressed to ~1 page of pseudocode + theorem statements in mathematical notation, with full listings in a supplementary appendix. The behavioral-economic section and the Swiss-system section are undercooked and could be cut to make room for baseline comparisons and a portability sketch.

---

## 6. Minor Technical Notes

- The matchup matrix is not quite antisymmetric: `matchupWR A B + matchupWR B A` varies between 958 and 980 across pairs (due to the tie convention), not always summing to 1000. This is correctly handled by the dual Nash formulation but could confuse readers who assume a constant-sum game.
- The `Fin.foldl` opacity issue preventing `decide` is a Lean 4 kernel limitation, not a fundamental issue. The paper correctly uses `native_decide` but should note that this may be resolved in future Lean versions, reducing the trust boundary.
- The `GrimssnarlFroslass` typo (single-m) is a minor artifact quality issue. A Lean `abbrev Grimmsnarl := GrimssnarlFroslass` would fix the presentation without breaking the codebase.

---

## 7. Recommendation

**Weak Accept** (borderline — could go either way with revisions)

### Justification

The paper makes a genuine first-of-kind methodological contribution: machine-checked metagame analysis with a complete Nash certification over real tournament data. The artifact quality is outstanding (zero sorry, 2,567 theorems, reproducible build). The v3 bridge is a meaningful improvement over earlier versions.

However, the practical value for competitive players remains undemonstrated (M1), the bridge formalizes folk knowledge without deep quantitative insight (M2), the missing baselines leave the cost-benefit ratio unjustified (M3), and the portability claim is unsupported (M4). The paper reads as an impressive proof-of-concept — which is valuable for a venue like ToG — but overstates its practical impact.

For acceptance, I would require:
1. An honest framing of practical limitations (M1): acknowledge that the current system's value is primarily methodological/scientific rather than competitive-tactical.
2. A baseline comparison table (M3): even informal, show what Lean adds beyond Python + unit tests.
3. Fix Figure 1 (m1) and reduce code listing density (m7).

Desirable but not required:
- A null model for the bridge alignment (M2/Q2).
- Multi-step replicator trajectories (Q3).
- A brief portability sketch (M4).

### Confidence

**4/5** — I have reviewed the Lean source files in detail, verified the sorry/admit/axiom claims, and have direct experience with both competitive TCG metagame analysis and Lean 4 proof engineering. My uncertainty is primarily about the appropriate novelty bar for IEEE ToG (vs. a formal methods venue).

---

*Reviewer: R3 (anonymous)*
*IEEE Transactions on Games — Submission #753 (v3)*
*Review date: 2026-02-20*
