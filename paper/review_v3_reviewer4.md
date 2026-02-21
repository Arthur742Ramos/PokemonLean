# IEEE Transactions on Games — Review of Submission #753 (v3)

## Reviewer 4

**Paper:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"

---

## 1. Summary

This paper presents a ~30,000-line Lean 4 formalization of competitive Pokémon TCG metagame analysis, encompassing 2,510 theorems with zero `sorry`/`admit`/custom axioms. Using Trainer Hill tournament data from a 3-week window (Jan 29–Feb 19, 2026) covering 14 archetypes in 50+ player events, the authors encode the full 14×14 pairwise matchup matrix and observed popularity shares, then prove a "popularity paradox" (Dragapult: 15.5% share yet 46.7% expected WR; Grimmsnarl: 5.1% share, 52.7% WR). They certify a bimatrix Nash equilibrium over the 14-deck game (6-deck support per player, 0% Dragapult weight), a symmetric Nash equilibrium on a constant-sum symmetrization (7-deck support, game value exactly 500), and run full 14-deck discrete replicator dynamics classifying 5 growing and 9 shrinking archetypes. A 10,000-iteration sensitivity analysis (in Python, external to Lean) confirms the core equilibrium support is robust. The paper positions itself as a methodological contribution—proof-carrying analytics for competitive game ecosystems—rather than a competitive-tactical tool.

---

## 2. Scores

| Criterion         | Score (1–5) | Rationale |
|--------------------|:-----------:|-----------|
| **Novelty**        | 3           | First-of-kind application domain, but the game theory is textbook and the verification pattern (encode constants, `native_decide`) is not technically novel in the Lean ecosystem. |
| **Technical Soundness** | 3      | All claims are machine-checked *modulo* the `native_decide` trust boundary, which covers 100% of the headline theorems. The sensitivity analysis is external Python, unverified. |
| **Significance**   | 3           | Demonstrates feasibility of proof-carrying analytics for TCGs, but practical impact is uncertain. The gap between what Lean provides and what 100 lines of Python provides is not convincingly argued. |
| **Clarity**        | 4           | Well-structured paper with good theorem–prose linkage. Honest about limitations. Some sections are repetitive. |
| **Reproducibility**| 4           | Lean artifact appears complete and self-contained. Data provenance is clearly stated. Python sensitivity script is supplementary. |

---

## 3. Strengths

**S1: Genuine first-of-kind domain application.**
To my knowledge, no prior work has applied interactive theorem proving to real competitive TCG metagame analysis at this scale. The coupling of a rules-layer formalization, an empirical matchup matrix, Nash equilibrium certification, and replicator dynamics within a single verified artifact is a novel systems-level contribution, even if each individual piece is standard.

**S2: The Nash equilibrium certification is the strongest verified object in the paper.**
The bimatrix Nash equilibrium (`real_nash_equilibrium_verified` in `NashEquilibrium.lean`) checks best-response conditions for all 14 pure strategies on both sides of the game—a 196-cell verification. This is precisely the kind of tedious, error-prone computation where formal verification adds genuine value over manual or even scripted checking. The symmetric Nash (`symmetric_nash_equilibrium_verified` in `SymmetricNash.lean`) with its exact game value of 500 provides a satisfying complementary result. The fact that both formulations independently assign 0% to Dragapult is a robust and cleanly stated conclusion.

**S3: Transparent and honest treatment of limitations.**
The paper is commendably forthright about its trust boundaries. Section IX's discussion of `native_decide` (lines ~860–890 of the LaTeX) explicitly acknowledges that no kernel-checked proof term is produced, that a compiler bug could invalidate all 244 `native_decide` proofs simultaneously, and that `Fin.foldl` opacity is a structural barrier to using `decide`. The authors also note the temporal locality, top-14 normalization, and archetype granularity limitations without attempting to minimize them. This level of transparency is rare and appreciated.

**S4: Full 14-deck replicator dynamics over real data.**
The `FullReplicator.lean` module goes beyond toy examples. Computing fitness rankings and growth/decline classifications for all 14 archetypes against the observed population (`full_replicator_grimmsnarl_fittest`, `full_replicator_alakazam_worst`, `full_replicator_dragapult_decline`) over the complete matchup matrix demonstrates that the verification infrastructure scales to the full problem, not just cherry-picked subsets.

**S5: Sensitivity analysis addresses the right concern.**
The 10,000-iteration resampling study (Table I in the paper) directly targets the fragility of exact Nash support under matchup uncertainty. The finding that exact support recovery is rare (2.1%) but core decks appear in >96% of iterations is a nuanced and informative result. The distinction between "the exact equilibrium is fragile" and "the qualitative conclusions are robust" is correctly drawn.

**S6: Clean modular architecture.**
The artifact is organized into well-separated modules (Core types → Type effectiveness → Real metagame data → Nash equilibrium → Symmetric Nash → Evolutionary dynamics → Full replicator → Archetype analysis → Share perturbation → Robustness). Each module has a clear responsibility, and the import graph is tractable. This modular design supports the paper's claim about updatability for future metagame windows.

**S7: Effective use of the "popularity paradox" as a unifying narrative.**
The paper weaves a single clean finding—Dragapult is overplayed relative to its expected performance—through multiple analytical lenses (weighted expected value, Nash equilibrium support, replicator fitness, type-effectiveness structural vulnerability). This gives the paper a coherent story rather than a disconnected bag of theorems.

---

## 4. Weaknesses

### Major

**M1: The `native_decide` trust boundary is concentrated and cannot be mitigated, undermining the verification's headline value.**

The paper's central selling point is *machine-checked guarantees*. Yet all 244 computational theorems that carry the paper's strategic claims—every Nash equilibrium, every replicator fitness ordering, every bridge alignment result—rely on `native_decide`, which trusts the Lean compiler's code generation end-to-end without producing a kernel-verifiable proof term.

The authors correctly acknowledge this (Section IX), but the implications are more severe than the paper suggests. The guarantee degrades from "verified by the Lean kernel" to "verified by the Lean compiler's native code generation pipeline"—a much larger trusted computing base that includes LLVM or the GCC backend. This is qualitatively different from the kind of verification achieved by, say, Gonthier's four-color theorem proof (cited in the paper), where the kernel checks the proof certificate directly.

The authors state that `decide` is "structurally precluded" due to `Fin.foldl` opacity. This is a genuine technical limitation of Lean 4's current kernel, but it also means the paper cannot deliver on its strongest implicit promise. The comparison to a Python script (Table VII) lists "machine-checked" as the Lean guarantee—but `native_decide` is closer to "compiled and executed" than "kernel-checked." A more accurate characterization would position the guarantee between unit-tested Python and fully kernel-verified proofs.

I would like to see the authors either (a) demonstrate at least one headline theorem (e.g., the symmetric Nash) via `decide` by restructuring the fold, or (b) more prominently qualify the guarantee level throughout the paper, not just in Section IX.

**M2: The rules-to-data bridge (`ArchetypeAnalysis.lean`) is a correlational consistency check, not a formal derivation.**

The paper claims a "machine-checked bridge from type-effectiveness rules to empirical matchup outcomes" (Introduction). However, examining `ArchetypeAnalysis.lean`, the bridge consists of:

1. *Manual* domain-expert type assignments (`Deck.primaryAttackType`, `Deck.primaryDefenseType`)—these are modeling choices, not formally derived from deck composition.
2. A lookup comparing `weakness(defenseType, attackType)` against `matchupWR > 500`.
3. Counting that 13/15 Dark→Psychic pairs align.

This is valuable as a sanity check, but calling it a "bridge" overstates the connection. The type assignments are external inputs that could be adjusted until alignment is achieved. The 83% alignment statistic (15/18 matchups) is interesting but is not a *formal* result—it's a manually curated correlation. The `theorem type_advantage_not_sufficient` honestly shows cases where the bridge breaks, which is good, but it also reveals that the type chart is a weak predictor: a 17% failure rate for the strongest type-advantage pairing (Dark→Psychic) is substantial.

I recommend the authors reframe this as a "correlational consistency audit" rather than a "bridge," and acknowledge that the type assignments are modeling assumptions (essentially free parameters) rather than formally derived quantities.

**M3: Missing baselines make the cost-benefit case unconvincing.**

Table VII (Methodology comparison) compares Lean (~30K LoC, ~10 min) against Python+scipy (~100 LoC, <1s) and a spreadsheet (~50 cells, minutes). The "Guarantee" column lists "machine-checked" for Lean, "unit tests" for Python, and "manual review" for spreadsheets. But the paper never demonstrates a concrete error that the Lean formalization caught that a Python script with standard test coverage would miss.

The claim about "silent index transpositions" and "off-by-one in 196-cell best-response checks" (Section IX) is plausible in principle but hypothetical. If the authors have encountered such bugs during development—or can construct a realistic scenario where the Lean formalization catches a bug that passes scipy.optimize.linprog's output validation—that would substantially strengthen the case. Without such evidence, the 300× engineering cost multiplier (30K LoC vs. 100 LoC) is hard to justify for the stated results.

**M4: The 3-week temporal window is thin, and the paper's structure suggests stronger generality than warranted.**

The analysis covers January 29 to February 19, 2026—21 days. The paper acknowledges temporal locality in Section X but simultaneously makes claims like "the paradox is structural: it derives from the matchup matrix, not the share vector, so the central finding is not an artifact of a particular metagame snapshot but reflects a persistent property of the underlying strategic landscape" (Section X, robustness analysis).

This claim of structural persistence is not supported by the evidence. The matchup matrix itself is a temporal snapshot. If the card pool changes (new set release, ban list update, rotation), the entire matrix—and all downstream conclusions—may shift. The preliminary predictive validation (Section VII) confirms this concern: Grimmsnarl, predicted to be the fittest, actually *declined* one day after the window, due to a "multi-step cascade" the model does not capture.

The paper would benefit from either (a) a second temporal window demonstrating consistency, or (b) substantially toning down the "persistent property" language.

**M5: The game-theoretic content is routine for this venue.**

The Nash equilibrium certification is a *verification* of a solution presumably obtained by an external LP solver (the paper does not explain how the exact rational Nash weights in `realNashDenom` were computed). The replicator dynamics are textbook discrete steps. The minimax theorem example (`minimax_theorem_2x2_concrete`) is a 2×2 special case decided by brute force. The RPS Nash uniqueness proof (`symmetric_rps_unique_uniform_on_thirds_grid`) searches a 1/3-resolution grid, establishing uniqueness only on that grid rather than over the full simplex.

None of these represent new game-theoretic results or methods. The contribution is applying them in a theorem prover—which is novel as engineering—but the game theory itself would not pass review at a game theory venue. For IEEE Transactions on Games, the question is whether the *application* is sufficiently interesting. I lean toward yes, but the paper should acknowledge more clearly that the game theory is applied, not contributed.

### Minor

**m1: The `FiniteGame` structure is oddly designed.**
`FiniteGame` has fields `n` (number of players), `m` (strategies), `payoff` (a function `Fin n → Fin m → Rat` that is never meaningfully used), and `matrix` (the actual payoff matrix). In practice, `n` is always 2, and `payoff` is always `fun _ _ => 0`. This dead structure suggests the formalization was designed for generality but never achieved it. The `NashEquilibrium` definition ignores `payoff` entirely and uses only `matrix`. This is not a soundness issue but clutters the API.

**m2: Typo in identifier: `GrimssnarlFroslass`.**
Acknowledged in a footnote, but it persists across the entire codebase. In a formalization that stakes its reputation on precision, persistent spelling errors in identifiers undermine presentation quality.

**m3: The replicator dynamics use multiple ad-hoc deck subsets (3-deck, 4-deck, 5-deck) before the full 14-deck analysis.**
`EvolutionaryDynamics.lean` devotes ~350 lines to toy RPS examples and 4-deck/5-deck subsets before the full 14-deck analysis appears in `FullReplicator.lean`. While pedagogically reasonable, this creates an impression that the full 14-deck analysis was an afterthought. The paper text (Section VII) foregrounds the full 14-deck results but the artifact tells a different development story.

**m4: The sensitivity analysis is entirely external to Lean.**
The 10,000-iteration Monte Carlo study is a Python script. This means the robustness conclusions that the paper presents alongside formally verified results are *not* formally verified. The paper notes this, but the juxtaposition in the narrative may mislead readers into thinking the sensitivity analysis enjoys the same guarantees as the Nash certification. Consider visually distinguishing verified and unverified results (e.g., a symbol or font convention).

**m5: `optimize_proof` is a confusing macro name.**
This macro expands to `native_decide` but its name suggests an optimization rather than a proof strategy delegation. A more transparent name (e.g., `compute_native` or simply inlining `native_decide`) would improve artifact readability.

**m6: The paper does not explain how the Nash equilibrium weights were computed.**
The exact rational Nash weights (e.g., `realNashDenom = 338129962783`) appear fully formed in the Lean source. The paper never describes the LP solver or algorithm used to find these weights. The Lean artifact *verifies* them, but the *discovery* process is opaque. Was this computed by an external LP solver? By hand? By Mathematica? This matters because verification of a given solution is much easier than finding one; the paper should document the toolchain.

**m7: The behavioral-economic interpretation (Section VI.B) is speculative and unsupported.**
Citations to Kahneman, Tversky, and herd-behavior literature are appropriate as motivation but the paper provides no player-level data to distinguish between familiarity bias, cost constraints, social diffusion, or simple information lag. The section reads as post-hoc narrative decoration rather than contributing analysis.

**m8: The paper exceeds typical length for IEEE Transactions on Games.**
At approximately 1,070 lines of LaTeX (excluding preamble), the paper is dense. Some sections—particularly the probability/resource theory (Section IV) and tournament strategy (Section VIII)—contribute little to the core narrative and could be shortened or moved to supplementary material without loss.

---

## 5. Questions for Authors

**Q1:** How were the exact rational Nash equilibrium weights (`realNashRowData`, `realNashColData`, `symNashStrategy`) obtained? Please describe the complete toolchain from matchup matrix to candidate equilibrium to Lean verification. If an external solver was used, which one, and what precision guarantees does it provide?

**Q2:** You claim the popularity paradox is "structural" and persists across share perturbations. But the matchup matrix itself is a temporal artifact. Have you checked whether the Dragapult popularity paradox holds in data from *outside* your 3-week window? Even one additional week (before or after) would substantially strengthen the "structural" claim. Alternatively, can you characterize what class of matchup matrix perturbations would reverse the paradox?

**Q3:** The paper positions proof-carrying analytics as a general methodology for competitive games. What is the realistic porting cost to a second domain (e.g., Magic: The Gathering, or a different Pokémon TCG format/era)? Specifically, which of the 30K lines are game-generic (Nash, replicator dynamics, probability infrastructure) versus Pokémon-specific (type chart, deck legality, archetype assignments)? A rough breakdown would help readers assess portability.

**Q4:** Given that `native_decide` is the sole proof strategy for all headline results, and that `decide` is structurally precluded, have you considered alternative formalization strategies that avoid `Fin.foldl`? For instance, encoding the matchup matrix as a recursive function over `Fin` constructors (rather than array indexing) might enable kernel reduction. Has this been attempted?

---

## 6. Overall Assessment and Recommendation

This is an ambitious and well-executed interdisciplinary project that breaks genuinely new ground in applying interactive theorem proving to competitive gaming analytics. The artifact is large, well-organized, and clearly documented. The paper is honest about its limitations—more so than many formalization papers I have reviewed.

However, I have significant reservations about the depth of the contribution along any single axis. The game theory is routine. The formal verification, while impressive in scale, rests entirely on `native_decide`, which provides weaker guarantees than the paper's framing suggests. The rules-to-data bridge is a consistency check, not a derivation. The practical utility over scripted alternatives is asserted but not demonstrated with concrete bug-catching evidence. And the 3-week empirical window is thin for the structural claims made.

The paper's strongest contribution is methodological proof-of-concept: it shows that proof-carrying metagame analytics *can be done* for a real competitive ecosystem at meaningful scale. This is a worthwhile contribution to IEEE Transactions on Games, where the intersection of formal methods and game analysis is underexplored. But the paper needs to be more precise about what the verification actually guarantees (given `native_decide`), and needs to either demonstrate concrete practical value or more forthrightly position itself as a feasibility study.

**Recommendation: Weak Accept**

The work is novel in its application domain and scale, the artifact is substantial, and the paper is well-written with unusual transparency about limitations. These strengths outweigh the concerns about the `native_decide` trust boundary, the thin empirical window, and the missing baselines—but only if the authors address the framing issues raised in M1–M3 in revision. Specifically: (1) prominently qualify the `native_decide` guarantee level beyond Section IX, (2) reframe the type-effectiveness bridge as a consistency audit, and (3) either provide a concrete bug-catching example or reposition as a pure feasibility study.

---

## 7. Confidence

**Confidence: 4/5 (High)**

I have deep familiarity with formal verification in Lean 4 (including the `native_decide` vs. `decide` distinction), game-theoretic equilibrium computation, and evolutionary dynamics. I have less domain expertise in competitive Pokémon TCG, which limits my ability to evaluate the empirical modeling choices (archetype type assignments, tie-weighting conventions) from a practitioner perspective. I have read the paper in full, examined all key Lean source files, and verified the artifact structure and theorem counts.

---

*Reviewer 4 — IEEE Transactions on Games, Submission #753 (v3)*
*Review date: February 20, 2026*
