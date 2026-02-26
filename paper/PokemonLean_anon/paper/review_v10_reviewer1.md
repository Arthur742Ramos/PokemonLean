# IEEE Transactions on Games — Review of Submission #753 v10

**Title:** From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game  
**Reviewer:** Reviewer 1 (Game Theory specialist)  
**Date:** 2026-02-20  
**Version reviewed:** v10 (12 pages, ~30K-line Lean 4 artifact)

---

## Summary

The paper presents a formally verified metagame analysis of the Pokémon TCG, encoding a 14×14 empirical matchup matrix in Lean 4 and proving a "popularity paradox" (the most-played deck is suboptimal), computing a machine-checked Nash equilibrium, and running verified discrete replicator dynamics over the full 14-deck game. v10 adds an Int↔Rat bridge in `StepSizeGeneral.lean`, reframes an unsourced skill benchmark as an author estimate, and separates verified from unverified evidence in the equilibrium multiplicity argument.

---

## Scores

| Criterion | Score (1–5) | Rationale |
|---|---|---|
| **Novelty** | 3 | First proof-carrying metagame analytics pipeline for a real TCG; the *application* of formal verification to empirical game theory is genuinely novel. However, the game-theoretic content itself (finite Nash via LP, single-step replicator, Bo3 amplification) is textbook. |
| **Technical** | 4 | The Lean artifact is impressively engineered: 2,500 theorems, zero sorry, full 14-deck coverage, cross-module matrix consistency (`MatrixConsistency.lean`), and the `DragapultDominated.lean` strict-suboptimality proof is clean. The v10 Int↔Rat bridge is an improvement but still has a compositional gap (see Must-Do #1). The `native_decide` trust boundary is honestly disclosed and unavoidable given current Lean 4 kernel limitations. Sensitivity analysis is external Python—adequate but ideally internalized. |
| **Significance** | 3 | Strong methodological demonstration. Competitive impact is limited: the headline result (popular deck is suboptimal) is unsurprising to tournament players, and the specific metagame window is already stale. The lasting value is the *template*, not the Pokémon-specific findings. Significance for ToG readership depends on whether formal-methods-as-methodology papers are in scope (they should be). |
| **Clarity** | 4 | Well organized and unusually transparent about trust boundaries. The v10 separation of verified vs. unverified evidence (§VII) is a significant improvement. Minor issues: the paper is dense for 12 pages, and the rules formalization (§III) takes disproportionate space relative to its analytical role. |
| **Reproducibility** | 5 | Exemplary. `lake build` reproduces all claims. The artifact is self-contained with explicit data provenance. This is the paper's strongest dimension and a model for the field. |

---

## Assessment of v10 Changes

### 1. Int↔Rat bridge (`StepSizeGeneral.lean`)

**Improvement:** The file now contains a clear `Rational bridge` section explaining that clearing denominators reduces the Rat sign question to the proven Int result. The prose in the paper references the "bridging corollary."

**Remaining gap:** The bridge section is a *comment block*, not a theorem. The actual compositional link is deferred to `StepSizeInvariance.lean`'s `native_decide` checks at specific dt values (1/10, 1/100, 1). This is concrete verification at three points, not a general Rat lemma. The comment correctly notes that `Lean.Rat` lacks ordering/multiplication lemmas for a general proof, but the paper's language ("A bridging corollary extends this result from integers to the rational arithmetic") oversells what exists: there is no `theorem` named as a bridging corollary in `StepSizeGeneral.lean`. The namespace `StepSizeGeneralBridge` is empty of theorems—it contains only a comment pointing to `StepSizeInvariance.lean`.

**Verdict:** Fixable. Either (a) add a minimal Rat sign lemma (even if it requires `native_decide` over the specific rational expressions), or (b) soften the paper's language from "bridging corollary" to "concrete verification at representative step sizes, consistent with the symbolic Int proof."

### 2. Skill benchmark reframing

**Improvement:** The "2–5pp" figure is now framed as an author estimate based on competitive experience, not an unsourced empirical claim. This is honest and appropriate.

**Remaining concern:** The estimate still does meaningful argumentative work (bounding the skill confound). Adding even one citation to player-skill variance in organized play (e.g., from Magic: The Gathering analytics, which has published ELO distributions) would strengthen this paragraph without requiring Pokémon-specific data.

### 3. Verified/unverified evidence separation

**Improvement:** The equilibrium multiplicity discussion now uses labeled paragraphs ("Formally verified evidence" / "Complementary unverified evidence"). This is exactly what was needed and is cleanly executed.

**No remaining issue.**

---

## Are the Remaining Gaps Fixable or Fundamental?

**Fixable gaps:**
- The Int↔Rat bridge is a naming/documentation issue, not a soundness issue. The concrete `StepSizeInvariance.lean` checks do verify the composition at all 14 decks × 3 step sizes, which is sufficient for the paper's claims.
- The skill-confound estimate needs one supporting citation.
- The `native_decide` concentration (244 of ~2,500 theorems, but covering 100% of the game-theoretic core) is an inherent Lean 4 limitation, not a paper defect. The disclosure is honest.

**Near-fundamental limitation (but not blocking):**
- The paper proves properties of *one* Nash equilibrium, not uniqueness or the full equilibrium set. The `DragapultDominated.lean` theorem `dragapult_strictly_suboptimal` shows Dragapult is not a best response to *this specific* column strategy, which is weaker than "Dragapult is excluded from all equilibria." The paper's v10 language in §VII is now careful about this ("cannot appear in ANY best-response support *to this column strategy*"), but Table I's framing and the abstract's "assigns Dragapult 0% weight" could still mislead casual readers into thinking uniqueness is proven. The Python sensitivity analysis (77.9% exclusion) is complementary but unverified. This is a real limitation but the paper handles it adequately with the v10 caveats.

**Not a gap:**
- The `native_decide` trust boundary is standard practice and honestly disclosed. Demanding kernel-checked proofs would reject most large-scale Lean 4 computational work.

---

## Recommendation

### **Weak Accept**

The paper makes a genuine methodological contribution: it is the first proof-carrying metagame analytics pipeline applied to real tournament data, and the artifact quality is exceptional. The game theory is standard but correctly applied and honestly bounded. The v10 revisions address the major concerns from prior rounds. Three targeted fixes (below) would bring it to clear acceptance.

---

## 3 Must-Do Revisions

1. **Fix the bridging corollary claim.** Either (a) add an actual theorem to `StepSizeGeneralBridge` (even a `native_decide`-backed one stating the Rat sign invariance for the 14 concrete decks), or (b) change the paper text from "A bridging corollary extends this result" to something like "Concrete `native_decide` verification in `StepSizeInvariance.lean` confirms the identical 5/9 classification at dt = 1/10, 1/100, and 1 for all 14 decks, composing with the symbolic Int proof." The current state has the paper referencing a corollary that does not exist as a theorem in the artifact. This is a truth-in-advertising fix, not a deep technical problem.

2. **Add one citation for the skill-differential estimate.** The 5pp bound does significant work in §X. Cite at least one source on within-event skill variance in organized card-game play (e.g., Haworth's chess rating analyses, or Frank Karsten's MTG win-rate-by-rating data, or any ELO-stratified TCG study). If no published source exists, state this explicitly ("To our knowledge, no published study quantifies within-event TCG skill variance; our estimate is a conservative upper bound based on the authors' experience") so the reader knows the evidential status.

3. **Clarify equilibrium multiplicity in the abstract and Table V caption.** The abstract says the Nash equilibrium "assigns Dragapult 0% weight," which reads as if this is the unique equilibrium. Add a qualifier: "A machine-checked Nash equilibrium" → already done in v10 abstract, good. But Table V's caption ("Lean-verified real Nash supports") should add "(one verified equilibrium; uniqueness not proven)" to avoid misreading. Similarly, in §VII, after the `dragapult_strictly_suboptimal` theorem, add one sentence: "This excludes Dragapult from all equilibria sharing this column strategy but does not rule out equilibria with different column supports."

---

## 3 Questions for the Authors

1. **Raging Bolt in Nash vs. replicator:** Raging Bolt Ogerpon receives the second-highest Nash weight (28.7% row) but is classified as a *shrinker* in replicator dynamics (fitness below average). This is not contradictory—Nash and replicator dynamics operate on different objects—but it is strategically puzzling and unexplained. Can you add a sentence interpreting this? Is it because Raging Bolt's fitness is below average at *current* shares but would be above average at Nash shares?

2. **Sensitivity to tie convention:** You state the tie convention WR = (W + T/3)/(W+L+T) is a Trainer Hill default and that results are "insensitive to this choice" (§V), but I don't see a formal robustness check for alternative tie weights (e.g., T/2). The mirror matches (49.4% Dragapult, 48.5% Grimmsnarl) already show the convention pulls mirrors below 50%. Have you checked whether a T/2 convention changes any directional conclusion? If so, this deserves a sentence; if not, it's a quick `native_decide` check worth adding.

3. **Why not prove Dragapult is weakly dominated?** `DragapultDominated.lean` proves strict suboptimality against one column mix but stops short of proving weak or strict dominance by a specific pure or mixed strategy. Is Dragapult actually dominated (i.e., does there exist a mixed strategy σ such that for all opponent strategies j, payoff(σ, j) ≥ payoff(Dragapult, j) with strict inequality for some j)? If so, this would be a much stronger result than Nash exclusion; if not, it clarifies the strategic structure. This seems within reach of `native_decide` over a candidate dominating mix.

---

## Minor Comments

- The identifier `GrimssnarlFroslass` (single-m, double-s) is acknowledged in a footnote but jarring. Consider a Lean type alias for display purposes.
- Table III's "95% Range" column header should note these are sensitivity ranges, not confidence intervals, to avoid confusion with Wilson intervals in §V. (The caption does say this but the header alone is ambiguous.)
- The predictive validation (§VII-C) showing 2/3 correct directional predictions is interesting but statistically meaningless at n=3. Consider framing it as "anecdotal" rather than "preliminary."
- §III takes ~1.5 pages on rules formalization (type triangles, card conservation) that, while nice, could be compressed to make room for the more analytically central sensitivity and robustness material.

---

*Reviewer 1, IEEE Transactions on Games*
