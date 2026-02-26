# IEEE Transactions on Games — Submission #753 (v15)
## Reviewer 3 — Revision Round 5

**Date:** 2026-02-21
**Reviewer expertise:** Proof engineering, Lean 4, formal verification, interactive theorem proving
**Prior recommendation (v14):** Accept

---

## Summary of Changes in v15

The authors have added an exhaustive Nash equilibrium enumeration over all 2¹⁴ − 1 = 16,383 non-empty species subsets, confirming uniqueness of the symmetric NE and universal Dragapult exclusion. Swiss-pairing literature has been incorporated, exact theorem counts now appear in Table VIII, and the enumeration methodology is documented in Section IX. The CausalChain.lean rename remains deferred to the artifact only.

---

## Evaluation

### Novelty — 4/5

Unchanged from v14. The exhaustive enumeration is not itself novel methodology, but its application to a fully mechanized metagame model is, to my knowledge, unprecedented. The completeness result (unique NE across the full subset lattice) meaningfully strengthens the contribution beyond the prior version's sampled analysis.

### Technical Soundness — 5/5

**Upgraded from 4/5 (v14).** This is the most significant improvement in v15.

The exhaustive enumeration over all 16,383 subsets closes the gap I had flagged informally at v14: the prior version's NE uniqueness claim rested on a representative subset analysis that, while convincing, was not exhaustive. Now:

- **Completeness:** Every non-empty subset of the 14-species pool is checked. The claim of unique symmetric NE is no longer qualified.
- **Universal Dragapult exclusion:** The result that Dragapult appears in zero equilibrium-support sets across the full lattice is a clean, strong theorem. This is the kind of result that formal verification is *for*.
- **Section IX methodology:** The enumeration procedure is clearly documented. I verified that the described approach (iterate subsets, solve each restricted game via support enumeration, filter for NE conditions) is sound. The Avis-Fukuda complexity note I requested is present, though terse — acceptable for a transactions paper.

The Lean artifact's `#check` output and `sorry`-freedom remain the gold standard for soundness in this domain.

### Significance — 4/5

Unchanged. The exhaustive enumeration modestly increases significance — the universal Dragapult exclusion is now a *theorem about the full game* rather than an empirical observation over sampled subsets. This distinction matters for the formal methods audience.

### Clarity — 4/5

Slightly improved. The Swiss-pairing literature addition smooths a transition that previously felt abrupt. Table VIII with exact theorem counts is cleaner and more useful than the prior version's approximate ranges. Section IX is well-organized.

Minor issues remaining:
- The CausalChain.lean filename in the artifact still doesn't match the module name used in-text (`CausalGraph`). I understand the deferral rationale (avoiding artifact hash churn before camera-ready), but the camera-ready version **must** reconcile this. A footnote acknowledging the discrepancy would cost one line and save reader confusion.
- Table VIII footnote: present now but could be more specific about which counts are decidable lemmas vs. propositional theorems. This is a nit.

### Reproducibility — 5/5

Unchanged. `lake build` with `sorry`-grep remains the reviewer's best friend.

---

## Disposition

| Criterion        | v14 | v15 |
|------------------|-----|-----|
| Novelty          |  4  |  4  |
| Technical Sound. |  4  | **5** |
| Significance     |  4  |  4  |
| Clarity          |  4  |  4  |
| Reproducibility  |  5  |  5  |

**Overall recommendation: Accept** (no change in disposition; confidence increased)

The exhaustive enumeration resolves my only substantive technical reservation from v14. The paper is ready for publication contingent on the standard camera-ready process.

---

## Camera-Ready Checklist (Carried Forward + New)

1. **CausalChain.lean → CausalGraph.lean rename** — Deferred twice now. Must be completed for camera-ready. Non-negotiable for artifact-paper consistency.
2. **Table VIII footnote granularity** — Optional but recommended: distinguish decidable lemmas from propositional theorems in the count.
3. *(New)* **Section IX, paragraph 2:** "all 16,383 subsets" — consider adding the explicit formula (2¹⁴ − 1) on first mention for readers unfamiliar with the species count. Currently it appears only parenthetically later.

None of these affect the accept decision.

---

*Reviewer 3 — Proof Engineering / Formal Verification*
