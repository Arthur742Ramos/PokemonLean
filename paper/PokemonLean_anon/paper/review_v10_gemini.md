# Review of Submission #753 v10: "From Rules to Nash Equilibria"

**Reviewer:** Expert in Empirical Game Theory and Esports Analytics

## Scores
*   **Novelty:** 4/5
*   **Technical Soundness:** 5/5
*   **Significance:** 3/5
*   **Clarity:** 5/5
*   **Reproducibility:** 5/5

**Recommendation:** Accept

## Strengths

1.  **Rigorous Methodological Pipeline:** The paper successfully demonstrates a "proof-carrying analytics" workflow. By formalizing the entire chain from data ingestion (`MatrixConsistency.lean`) to equilibrium certification (`NashEquilibrium.lean`) and dynamics (`FullReplicator.lean`), the authors establish a higher standard for reproducibility in esports analytics. The use of `native_decide` to bridge the gap between large data matrices and formal proofs is a pragmatic and well-documented engineering choice.

2.  **Symbolic Robustness Guarantees:** Beyond merely calculating numbers, the artifact proves structural properties that ensure robustness. `StepSizeGeneral.lean` provides a valuable symbolic proof that the direction of replicator dynamics is independent of the step size, guarding against numerical artifacts. `SkillSensitivity.lean` rigorously quantifies the exact "skill confounding" (3.4pp) required to explain away the popularity paradox, replacing hand-wavy discussions with verified bounds.

3.  **Comprehensive Empirical Claims:** The analysis of the "popularity paradox" is thorough. It triangulates the result through multiple lenses: unweighted win rates, Nash equilibrium exclusion (both asymmetric and symmetric), and evolutionary fitness decline. The 10,000-iteration sensitivity analysis (even if external) and the verified share perturbation theorems (`SharePerturbation.lean`) provide strong evidence that the result is not a fluke of the specific sample window.

## Weaknesses

1.  **The "Garbage In, Verified Garbage Out" Problem:** As the authors honestly note, the formal verification boundary stops at the data ingestion. If the Trainer Hill data has selection bias (e.g., better players uploading logs), the formal proofs rigorously certify a false conclusion. While `ArchetypeAnalysis.lean` attempts to ground outcomes in type effectiveness rules, this is a correlation check, not a causal proof. The paper would be stronger with a cross-validation against a second data source to empirically validate the input matrix before formally verifying its consequences.

2.  **Limited Mathematical Depth vs. Infrastructure Cost:** The ratio of "lines of code" (30k) to "mathematical insight" is high. The core verified results—checking best-response inequalities for a 14x14 matrix—are computationally trivial. While the *infrastructure* is impressive, the *theorems* themselves (e.g., `dragapult_zero_row`) are essentially just large arithmetic checks. The value lies entirely in the *process* and *trust*, not in the complexity of the deductions.

3.  **Stationarity Assumption:** The analysis treats archetypes as fixed strategies with constant win rates. In high-level TCG play, "Dragapult" is not a single strategy but a cloud of lists that evolve daily to counter the meta. The replicator dynamics model assumes a static payoff matrix, which fails to capture the co-evolution of deck lists *within* archetypes. This limitation of the "species-level" view (vs "gene-level" or specific card-level view) restricts the predictive power of the dynamics analysis.
