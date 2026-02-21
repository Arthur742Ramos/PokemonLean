# IEEE Transactions on Games — Reviewer Report

**Submission #753:** "From Rules to Nash Equilibria: Formally Verified Game-Theoretic Analysis of a Competitive Trading Card Game"  
**Version:** 8 (12 pages)  
**Review Date:** 2026-02-20  
**Reviewer Expertise:** Game theory (Nash equilibrium computation, evolutionary dynamics, equilibrium selection)

---

## Summary

The paper presents a Lean 4-verified metagame analysis of competitive Pokémon TCG deck selection, modeled as a finite strategic-form game. Using Trainer Hill tournament data (Jan–Feb 2026) over 14 archetypes, the authors prove a "popularity paradox" (the most-played deck is suboptimal), compute and verify a Nash equilibrium via saddle-point conditions, run replicator dynamics over the full 14-deck game, and provide sensitivity/robustness analyses. The artifact is ~30K lines with ~2,500 theorems and no `sorry` or custom axioms. V8 adds a strict suboptimality proof for Dragapult, a matrix cross-consistency theorem, replacement of a custom macro with direct `native_decide`, clarified saddle-point vs. bimatrix definitions, reframed step-size invariance, and an equilibrium multiplicity argument.

---

## Evaluation of V8 Changes (Game Theory Focus)

### 1. Equilibrium Uniqueness/Multiplicity Argument

**Improved but still incomplete.** The v8 argument is layered: (a) Dragapult gets 0% weight in the asymmetric row strategy, asymmetric column strategy, and symmetric equilibrium; (b) `dragapult_strictly_suboptimal` proves Dragapult's pure-strategy payoff is strictly below the game value against the Nash column mix; (c) the authors correctly note this means Dragapult cannot appear in *any* best response to this particular column strategy.

However, the multiplicity argument has a logical gap the authors partially acknowledge but understate. The strict suboptimality result (b) shows Dragapult is excluded from any equilibrium *that uses this specific column strategy*. But Nash equilibria in bimatrix games can have entirely different column strategies. The paper's language — "strong evidence that Dragapult's exclusion is not an artifact of equilibrium selection" — is appropriately hedged, but the underlying formal claim is weaker than a reader might infer. True uniqueness would require showing that Dragapult is iteratively strictly dominated (which would eliminate it from *all* equilibria), or proving equilibrium uniqueness directly. The authors verify exclusion from two specific equilibria (asymmetric and symmetric) and one best-response argument, which is suggestive but not a proof of universal exclusion.

**Assessment:** The argument is significantly stronger than v7 and adequate for the paper's stated claims, but the distinction between "excluded from all equilibria sharing this column mix" and "excluded from all equilibria" should be stated more precisely.

### 2. Step-Size Invariance Reframing

**Appropriate and well-handled.** The v8 reframing correctly identifies step-size invariance as an algebraic tautology: since $x_i' - x_i = x_i \cdot dt \cdot (f_i - \bar{f})$, the sign depends only on $f_i - \bar{f}$, not on $dt$ (for $dt > 0$, $x_i > 0$). The paper now frames the concrete verification at dt=1/10, 1/100, and 1 as confirming this algebraic fact rather than presenting it as a surprising empirical finding. This is the correct framing.

One minor concern: the `StepSizeInvariance.lean` file verifies the claim by checking three specific step sizes rather than proving it symbolically for all positive dt. Given the algebraic triviality, a general proof (`∀ dt > 0, sign(x_i' - x_i) = sign(f_i - f_bar)`) would be straightforward in Lean and would be strictly stronger. The current approach is not wrong but represents an odd choice — verifying a universally-quantified algebraic identity by spot-checking instances is exactly the kind of methodology gap the paper's own framing criticizes.

### 3. Saddle-Point vs. Bimatrix Nash Clarification

**Substantially improved.** The `NashEquilibrium` definition in `NashEquilibrium.lean` now clearly encodes a saddle-point condition:

```
(∀ i, rowPurePayoff g i s2 ≤ expectedPayoff g s1 s2) ∧
(∀ j, expectedPayoff g s1 s2 ≤ colPurePayoff g s1 j)
```

The paper correctly explains that this is *stronger* than the standard bimatrix best-response condition and implies Nash equilibrium in both zero-sum and general settings. The text now explicitly acknowledges that the matrix is not exactly constant-sum (due to tie conventions) and that the row/column support difference is a natural consequence.

The one remaining subtlety: the saddle-point condition as stated certifies a Nash equilibrium of the *zero-sum game* where the column player's payoff is the negative of the row player's. For the original bimatrix game where column player j's payoff is $M_{ji}$ (not $-M_{ij}$), the saddle-point condition is sufficient but conceptually distinct. The paper acknowledges this ("which is stronger than the standard bimatrix best-response condition and implies Nash equilibrium in both the zero-sum and general bimatrix senses") but the formal implication could be made explicit — a one-line lemma showing `SaddlePoint → BimatrixNash` would complete the argument.

---

## Scores

| Criterion | Score | Justification |
|-----------|-------|---------------|
| **Novelty** | 3/5 | The formal verification methodology applied to real metagame data is genuinely novel. The game-theoretic content itself (Nash computation, replicator dynamics on finite games) is standard. The bridge from rules to equilibrium is the distinctive contribution. |
| **Technical Soundness** | 4/5 | The formal artifact is impressive and the `native_decide` trust boundary is honestly disclosed. The equilibrium multiplicity argument, while improved, still falls short of proving universal exclusion. The saddle-point clarification resolves the previous definitional concern. All computations are machine-checked over exact rationals. |
| **Significance** | 3/5 | Methodological significance is real: this is, to my knowledge, the first formally verified Nash equilibrium computation over a real competitive game's empirical payoff matrix. The specific metagame findings are time-limited and domain-specific. The template is portable but the paper doesn't demonstrate portability. |
| **Clarity** | 4/5 | Well-written for a cross-disciplinary audience. The game-theory exposition is accurate. The paper does a good job of separating what is formally verified from what is externally computed (Python sensitivity analysis) or assumed (data provenance). Minor: the extensive Lean listings may alienate game-theory readers who would benefit from more mathematical notation. |
| **Reproducibility** | 5/5 | Exceptional. Full Lean 4 source with `lake build` instructions, ~10 min build time, no sorry/admit/axiom, exact rational arithmetic. The `MatrixConsistency.lean` cross-check eliminates a real class of copy-paste errors. The Python sensitivity script is included. This is a gold standard for computational reproducibility. |

---

## Recommendation: **Weak Accept**

The paper makes a genuine methodological contribution at the intersection of formal verification and applied game theory. The v8 revisions address most prior concerns: the saddle-point definition is now clear, the step-size framing is appropriate, and the Dragapult exclusion argument is substantially strengthened. The equilibrium multiplicity argument remains incomplete but is honestly presented. The artifact quality is exceptional and sets a high bar for reproducibility in game-theoretic analysis of competitive games.

---

## 3 Must-Do Revisions

1. **Sharpen the equilibrium multiplicity claim.** The current text says Dragapult's exclusion is "not an artifact of equilibrium selection," but the formal result only proves exclusion from equilibria sharing the verified column mix. Either (a) prove that Dragapult is iteratively strictly dominated (which would give universal exclusion across all equilibria), (b) prove equilibrium uniqueness for this game, or (c) revise the language to precisely state that the result covers all equilibria with this column strategy and two specific equilibrium instances, not all possible equilibria. Option (c) is acceptable — the evidence is already compelling — but the current phrasing overstates what has been proven.

2. **Prove step-size invariance symbolically.** Replace or supplement the three-instance spot check in `StepSizeInvariance.lean` with a general proof: `∀ dt > 0, ∀ i, x_i > 0 → (replicatorStep ... dt i > x i ↔ fitness ... i > avgFitness ...)`. The algebraic argument is given informally in the text; formalizing it would take a few lines and would eliminate the irony of using instance-checking in a paper advocating for formal verification over spot-checking. At minimum, add a comment acknowledging this gap.

3. **Add the `SaddlePoint → BimatrixNash` bridging lemma.** The paper claims the saddle-point condition "implies Nash equilibrium in both the zero-sum and general bimatrix senses." This implication should be a proven Lean theorem, not a prose claim. The proof is short (the saddle-point condition for the row player directly gives the best-response condition; for the column player in the bimatrix game where column payoffs are $M_{ji}$, the column condition follows from the saddle-point column inequality plus the near-constant-sum structure). If the implication requires the constant-sum assumption, state that explicitly.

---

## 3 Questions for Authors

1. **On equilibrium uniqueness:** Have you checked whether Dragapult is iteratively strictly dominated in the reduced game (i.e., after removing strategies that are strictly dominated in earlier rounds)? If Dragapult is eliminated in the first round of IESDS, that would give the universal exclusion result essentially for free and would be a much stronger statement than the current best-response argument against one specific column mix. The 14×14 game is small enough for exhaustive IESDS.

2. **On the sensitivity analysis methodology:** The 10,000-iteration sensitivity analysis samples each matchup cell *independently* from its Wilson interval. In reality, estimation errors are correlated within rows (a weak Dragapult pilot depresses all of Dragapult's row entries simultaneously). Have you considered row-correlated perturbation models (e.g., a random row effect)? This could substantially tighten the inclusion rates and would directly connect to the skill-confounding analysis in `SkillSensitivity.lean`.

3. **On the symmetric equilibrium:** The symmetrized game $S_{ij} = (M_{ij} + 1000 - M_{ji})/2$ has a seven-deck support equilibrium, while the original bimatrix game has six-deck support per player. The symmetric equilibrium includes Gholdengo (9.2%) which is absent from the asymmetric row strategy, and excludes Alakazam which appears in the asymmetric row strategy (5.8%). How should a practitioner interpret these support differences — do they reflect genuine strategic ambiguity about these marginal decks, or are they artifacts of the symmetrization distorting the payoff structure?

---

*Reviewer 1 — Game Theory Specialist*
