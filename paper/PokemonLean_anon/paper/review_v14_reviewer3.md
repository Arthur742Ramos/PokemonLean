# IEEE Transactions on Games — Submission #753 (v14, Revision Round 4)
## Reviewer 3 — Proof Engineering / Formal Verification Specialist

**Date:** 2026-02-20
**Reviewer history:** v12 (Weak Accept), v13 (Weak Accept → minor revisions for Accept), v14 (this review)

---

## Summary of v14 Changes Relative to v13 Review Requests

| # | Requested Change (v13) | Status in v14 | Assessment |
|---|------------------------|---------------|------------|
| 1 | Rename `CausalChain.lean` to reflect actual content | **Deferred** (artifact-only, no paper text impact) | Acceptable — cosmetic artifact hygiene, not a publication gate |
| 2 | More prominent `native_decide` caveat in abstract | **Done** — Abstract sentence 2 now explicitly states compiler-trust scope | Fully addresses concern |
| 3 | Kernel-vs-compiler assurance summary table | **Done** — New Table VIII with ~2,256 kernel / ~244 compiler breakdown | Exceeds expectations |

**Verdict on prior requests:** 2 of 3 substantive changes completed. The remaining item (file rename) is an artifact maintenance task with zero impact on the paper's claims, readability, or reproducibility. I do not consider it grounds for withholding acceptance.

---

## Criteria Scores (1–5)

| Criterion | Score | Comments |
|-----------|-------|----------|
| **Novelty** | 4 | Applying Lean 4 formal verification to competitive Pokémon strategy remains, to my knowledge, unique in the literature. The kernel-vs-compiler decomposition (Table VIII) now makes the novelty claim more honest and precise. |
| **Technical Soundness** | 4 | The native_decide trust boundary is now clearly delineated at every level — abstract, body, and the new Table VIII. The ~91% kernel / ~9% compiler split is a credible ratio for a project mixing decidable game-theoretic enumeration with symbolic tactic proofs. Step-size invariance via `simp`, `ring`, `omega` (all kernel-level) is correctly characterized. The softened replicator language ("fitness pressure" rather than "predict decline/dominance") is appropriately cautious for a deterministic model applied to a stochastic metagame. |
| **Significance** | 3 | Unchanged from v13. The contribution is a compelling proof-of-concept for formal methods in game AI, but practical impact on either the Pokémon competitive community or the broader formal verification community remains to be demonstrated. The Avis-Fukuda future-work discussion is a welcome addition that sketches a path toward exhaustive equilibrium enumeration. |
| **Clarity** | 4 | Improved from v13 (was 3.5, rounded to 4). Table VIII is well-structured and immediately readable. The abstract caveat is concise without being buried. |
| **Reproducibility** | 4 | The artifact builds, the Lean version is pinned, and the trust boundaries are documented. The deferred `CausalChain.lean` rename is a minor ergonomic issue for artifact reviewers but does not impede `lake build` or proof checking. I recommend the authors address it in the camera-ready artifact nonetheless. |

---

## Detailed Comments

### What works well

1. **Table VIII** is exactly what I asked for and is arguably the single most valuable addition across the revision rounds. It lets any reader instantly assess which results carry kernel-level assurance and which depend on compiler correctness. This is the kind of transparency that formal verification papers should aspire to.

2. The abstract now front-loads the `native_decide` trust caveat in sentence 2 — before any claim enumeration. This is the right editorial choice. A reader who stops after the abstract still leaves with an accurate understanding of the assurance level.

3. The replicator dynamics language change is small but important. "Indicate downward/upward fitness pressure" is a defensible claim from a deterministic payoff model; "predict decline/dominance" was not.

### Minor suggestions (non-blocking)

- **Camera-ready artifact:** Please rename `CausalChain.lean` to something reflecting its actual content (e.g., `TypeMatchupChain.lean` or `StrategyComposition.lean`). This was requested in v13 and deferred; it would improve artifact navigability for readers attempting to reproduce results.

- **Table VIII footnote:** Consider adding a one-line footnote clarifying that "compiler-trust" means Lean's `native_decide` compiles the decision procedure to native code and trusts the compiled output, not that arbitrary external code is trusted. This distinction matters for readers unfamiliar with Lean's architecture.

- **Avis-Fukuda discussion:** The future-work mention is appropriate in scope. If space permits, a single sentence noting the vertex enumeration complexity (output-sensitive polynomial) would help readers unfamiliar with the algorithm assess feasibility.

---

## Overall Recommendation

### **Accept**

My v13 review stated that the three requested changes were sufficient for acceptance. Two substantive changes (abstract caveat, Table VIII) are completed and well-executed. The third (artifact file rename) is a cosmetic artifact issue that does not affect any claim, proof, or result in the paper. I see no justification for requiring a fifth revision round over a filename.

The paper presents a novel, technically sound, and clearly written application of formal verification to game-theoretic Pokémon analysis, with honest and now prominently disclosed trust boundaries. It meets the acceptance bar for IEEE Transactions on Games.
