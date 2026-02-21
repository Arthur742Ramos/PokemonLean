# IEEE Transactions on Games — Submission #753
## Reviewer 3 Report (Proof Engineering Specialist)
### Date: 2026-02-20

---

## Summary

This paper presents a formally verified metagame analysis of the competitive Pokémon TCG, using Lean 4 to machine-check claims about expected win rates, Nash equilibria, and replicator dynamics over a 14-archetype matchup matrix derived from tournament data. The central finding is a "popularity paradox": the most played deck (Dragapult) is suboptimal under weighted expected value, while an underplayed deck (Grimmsnarl) achieves the highest expected win rate and dominates the Nash equilibrium support. The artifact spans ~30,000 lines with no `sorry` or `admit`.

---

## Scores

| Criterion         | Score | Comment |
|-------------------|-------|---------|
| **Novelty**       | 4     | Applying formal verification to empirical metagame analysis is genuinely original. The methodology-as-contribution framing is appropriate. |
| **Technical Soundness** | 3 | Core claims are well-supported within stated boundaries, but several technical characterizations require correction or further precision. See detailed comments. |
| **Significance**  | 3     | Methodological contribution is real but impact is constrained by the `native_decide` dependency and the relatively modest strategic conclusions. |
| **Clarity**       | 4     | Paper is well-organized and generally clear. The trust boundary and limitation discussions are notably improved over what one typically sees. |
| **Reproducibility** | 4   | `lake build` reproducibility is excellent. Python sensitivity analysis being external is appropriately flagged. |

---

## Overall Recommendation: **Weak Accept**

The paper makes a legitimate methodological contribution by demonstrating that proof-carrying analytics is feasible for real game ecosystems. The authors are commendably honest about most limitations. However, several technical characterizations need tightening before publication. My concerns are enumerable and mostly addressable in revision.

---

## Detailed Comments

### 1. `native_decide` Trust Boundary (Adequate and Honest: Yes, with caveats)

The Section IX discussion of `native_decide` is among the most forthright I have seen in a Lean-based publication. The authors:

- Correctly state that `native_decide` does not produce a kernel-verified proof term
- Acknowledge the correlated-failure risk (all 244 theorems share the same trust assumption)
- Explain the structural reason `decide` fails (`Fin.foldl` opacity to the kernel reducer)
- Note the absence of defense-in-depth for the game-theoretic core

**This is good.** Two minor improvements I would suggest:

(a) The paper should state explicitly that `native_decide` trusts not only the Lean compiler backend but also the C compiler used to compile it, and transitively the hardware. This is standard but worth noting when 244/2500 theorems (including *all* headline results) pass through this path.

(b) The footnote in Table VII ("Modulo `native_decide`") is easy to miss. The abstract says "formally verified (modulo the `native_decide` trust boundary discussed in Section IX)" which is good, but I would recommend the same parenthetical appear in the Conclusion's first sentence as well, which currently says "verified modulo native code generation in Lean 4" — a weaker phrasing that could be read as referring to Lean's own compilation rather than the specific tactic trust issue.

### 2. CausalChain.lean: "Cross-Module Integration Tests" (Technically Accurate: Mostly)

The paper's reframing of CausalChain.lean's theorems as "conjunctions of independently verified facts from different modules, serving as cross-module integration tests rather than compositional derivations" is a significant improvement and is **technically accurate** for 11 of the 12 theorems described.

The key sentence distinguishing conjunction from composition is:

> "the algebraic sufficiency inequality above is the one theorem where multiple module outputs are arithmetically *combined* rather than merely conjoined"

This is an important and correct distinction. However, the preceding paragraph still uses language that could mislead:

> "a summary theorem (`the_complete_story`) that conjoins 11 cross-module facts—from the single game rule *Psychic is weak to Dark* through population shares, matchup losses, expected value, Bo3 amplification, variance reduction, and Swiss tournament exposure—into one machine-checked consistency check."

The phrasing "from the single game rule ... through ... into" still implies a derivation chain even though the sentence ends with "consistency check." I recommend removing the "from...through...into" construction entirely and instead saying something like: "a summary theorem that simultaneously asserts 11 facts spanning type rules, population shares, matchup data, expected value, Bo3 conversion, and Swiss exposure." This removes any residual implication of logical flow.

**Minor technical point:** The paper should clarify whether `the_complete_story` is proved by `native_decide` on the conjunction or by `And.intro` assembling individually proved conjuncts. The proof strategy matters for understanding what "integration test" means here — if it's a single `native_decide` on the conjunction, it's genuinely testing that all 11 facts are simultaneously satisfiable under the same definitions, which is stronger than assembling pre-proved pieces.

### 3. "Algebraic Sufficiency" Theorem (Genuinely Compositional: Partially)

The algebraic sufficiency theorem (`dark_weakness_sufficient_for_suboptimality`) is the paper's strongest claim to compositionality. The inequality:

$$\sum_{j \in \text{Dark}} s_j \cdot w_{\text{Drag},j} + (695 - 131) \times 500 < 500 \times 695$$

does combine outputs from multiple modules: type assignments (which Dark attackers exist), meta shares ($s_j$), and matchup win rates ($w_{\text{Drag},j}$). The "best-case non-Dark" term (granting 50% against all non-Dark opponents) is the compositional insight — it shows the Dark weakness alone is sufficient regardless of other matchups.

**However**, I have a concern about the strength of the "compositional" claim:

- The theorem uses *concrete numerical values* for $s_j$ and $w_{\text{Drag},j}$, not symbolic/parametric reasoning over abstract matchup structures. It is a numerical inequality verified by `native_decide` over specific constants, not a general algebraic lemma.
- A truly compositional result would be: "For any matchup matrix $M$ and share vector $s$ where Dark attackers have total share $\geq \alpha$ and win rates $\geq \beta$ against Dragapult, Dragapult's expected value is below 50%." This would be a universally quantified statement.

The paper says this is "a machine-checked derivation from a single game rule," but it is more precisely a machine-checked numerical verification that *this particular* combination of type weakness, population shares, and win rates produces sub-50% fitness. The game rule provides structural *explanation* but does not *entail* the conclusion without the specific empirical constants.

I recommend the authors soften "algebraically sufficient" to "numerically verified as sufficient for the observed data" or add a brief remark acknowledging the distinction between parametric and concrete sufficiency.

### 4. StepSizeGeneral.lean Symbolic Proof (Properly Described: Yes, with one gap)

The paper describes two related results:

1. `replicator_sign_independent_of_dt` — a general symbolic lemma showing sign independence from step size
2. `rat_replicator_sign_independent_of_dt` — extends to `Lean.Rat` arithmetic, proved "symbolically without `native_decide`"

This is **properly described** and represents one of the stronger verification contributions. The fact that this result does *not* use `native_decide` is correctly highlighted and provides genuine defense-in-depth for the replicator direction claims.

**One gap:** The paper does not specify which tactic(s) prove the symbolic lemma. Given that the paper catalogs four proof patterns (Section IX-B), identifying which pattern applies here would strengthen the description. If it's proved by `omega`/`nlinarith` over the algebraic structure, that's meaningful — it means the sign-independence result has full kernel-level assurance, making it the most trustworthy result in the game-theoretic core.

### 5. Verified vs. Unverified Distinction (Clear: Mostly, with specific lapses)

The paper generally does a good job distinguishing verified from unverified results:

**Good practices:**
- Table I footnote marking `native_decide` dependency
- Explicit labeling of Python sensitivity analysis as "external to the Lean-verified theorems"
- "Complementary unverified evidence" paragraph header in Section VII
- Wilson intervals clearly marked as computed rather than verified
- "produced by an external Python script; these results complement but do not inherit the formal guarantees" for sensitivity analysis

**Lapses requiring attention:**

(a) **Type assignments as modeling assumptions.** The paper correctly notes these are "domain-expert modeling choices, not formally derived from deck composition" — but the downstream 83% alignment claim and the p < 0.001 binomial test are computed informally (or at least not described as Lean-verified). Are these statistics verified in Lean? If not, this should be stated.

(b) **Nash equilibrium discovery.** The paper says weights "were obtained by solving the linear program externally using Python's `scipy.optimize.linprog` with exact rational conversion; Lean then independently verifies the best-response conditions." This is appropriately described. However, the phrase "Lean-verified real Nash supports" in Table IV's caption could imply Lean verified the weights themselves rather than just the best-response conditions *given* those weights. A more precise caption would be: "Nash supports verified via best-response certification in Lean."

(c) **Swiss probability formula.** The binomial Swiss cut-line probability formula in Section VIII appears without any indication of whether it is verified in Lean. Given the paper's methodology claims, this omission is notable.

(d) **Sensitivity analysis confidence intervals.** Table II is carefully labeled, but the column header "95% Range" could be confused with a confidence interval. The caption's clarification ("not frequentist confidence intervals") is good but should appear in the column header itself, e.g., "95% Sens. Range."

### 6. Additional Technical Concerns

**(a) Equilibrium uniqueness.** The paper correctly states uniqueness is not proven, but should be more explicit about the implications. The sensitivity analysis shows the *exact* support is recovered in only 2.1% of iterations — this suggests the verified equilibrium may be quite fragile as a point prediction, even though the *qualitative* conclusions (Dragapult exclusion, core trio) are robust.

**(b) Constant-sum approximation.** The paper verifies equilibria for both the raw bimatrix and the symmetrized constant-sum game, which is good. However, the relationship between these two equilibria is not formally established. Are they close in any metric? The seven-deck symmetric support vs. six-deck asymmetric support already shows structural differences.

**(c) Replicator dynamics: single-step limitation.** The paper is honest about single-step limitations, and the preliminary directional check (Section VII-C) where Grimmsnarl declined despite predicted highest fitness is a valuable negative result. However, the paper could note more explicitly that single-step discrete replicator dynamics with step size dt=1/10 is an extremely crude approximation — the verified result is essentially just the sign of $f_i - \bar{f}$, which is simply "which decks have above/below average fitness." This is a useful fact but calling it "replicator dynamics" somewhat oversells it.

**(d) The 83% alignment p-value.** The binomial test uses a null hypothesis of 50% random alignment, but this null is not obviously correct. If type assignments are constrained to the actual type chart (which has structure — not all types are equally common among archetypes), the null may not be 50%. This statistical claim should either be verified in Lean or more carefully qualified.

### 7. Minor Issues

- The identifier `GrimssnarlFroslass` (single-m, double-s) is acknowledged but should be fixed in the artifact for a camera-ready version.
- The claim "approximately 190 theorems directly verify empirical claims" appears in both the abstract and Section IX-D but the basis for this count is not explained. What distinguishes an "empirical claim" theorem from an infrastructure theorem?
- The paper could benefit from a single consolidated table mapping each headline claim to its Lean theorem name, file, and proof method (native_decide/decide/symbolic), making the verified/unverified boundary immediately auditable.

---

## Questions for the Authors

1. Is `the_complete_story` proved by a single `native_decide` or by assembling pre-proved conjuncts?
2. What tactics prove `rat_replicator_sign_independent_of_dt`? Is this fully kernel-checked?
3. Are the 83% alignment rate and p < 0.001 binomial test verified in Lean?
4. Has any independent party successfully run `lake build` on the artifact?

---

## Summary Assessment

This is a well-executed methodological contribution with genuine novelty. The trust boundary discussion is honest and detailed — better than most Lean-based papers I have reviewed. The main weaknesses are (a) the residual compositional overclaiming around CausalChain.lean and algebraic sufficiency, (b) a few boundary cases where the verified/unverified distinction blurs, and (c) the inherent limitation that all game-theoretic headline results pass through `native_decide` with no kernel-level fallback. These are addressable in revision. I recommend **Weak Accept** contingent on the authors addressing the technical precision issues raised above.
