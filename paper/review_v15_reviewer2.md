# IEEE Transactions on Games — Submission #753 (v15, Revision Round 5)

## Reviewer 2 — Review

**Reviewer expertise:** Empirical game theory, metagame analysis, competitive esports analytics
**Review date:** 2026-02-21
**Confidence:** 4/5 (High)

---

## Summary of Changes in v15

The authors have addressed two of my four remaining concerns from v14. The Swiss-pairing model paragraph now includes proper references to Glickman and TrueSkill, and Table VIII reports exact theorem counts rather than approximations. The Python sensitivity analysis remains external to Lean, which I accept as a structural limitation of the verification architecture. The novelty concern regarding empirical findings also remains, as expected.

The headline addition in v15 is an exhaustive Nash equilibrium enumeration over all 16,383 non-empty support subsets of the 14-species metagame, confirming that the symmetric NE excluding Dragapult is *unique*. No alternative NE including Dragapult exists. This is a substantial technical upgrade that I did not request but that materially strengthens the paper's central claim.

---

## Scores

| Criterion | Score | Comments |
|---|---|---|
| **Novelty** | 3/5 | Unchanged from v14. The formal verification methodology applied to competitive Pokémon metagames remains novel. The empirical findings about Dragapult's dominance are confirmatory of community knowledge rather than surprising. The exhaustive NE enumeration is a meaningful methodological contribution but does not alter the fundamental novelty profile. |
| **Technical Soundness** | 5/5 | **Upgraded from 4/5 in v14.** The exhaustive enumeration is the difference. In v14, the paper showed *a* Nash equilibrium existed that excluded Dragapult — an existential result that left open whether alternative equilibria might include it. The universal result (no NE over any support subset includes Dragapult) closes this gap completely. Combined with the Lean-verified payoff matrix and the exact theorem counts in Table VIII, the formal machinery is now airtight. The only unverified component is the Python sensitivity analysis, which the authors transparently flag. |
| **Significance** | 3.5/5 | The unique-NE result elevates significance modestly. For the competitive Pokémon community, confirming Dragapult's non-viability via exhaustive equilibrium search is more actionable than an existential proof. For the formal methods community, demonstrating that exhaustive enumeration over a 14-species metagame is tractable in Lean is a useful benchmark. The paper still primarily validates known competitive intuitions rather than generating novel strategic insights. |
| **Clarity** | 4/5 | Unchanged. The paper is well-written. The Swiss-pairing paragraph reads naturally with the Glickman/TrueSkill references integrated. The exhaustive enumeration methodology is clearly described. Minor suggestion: a sentence or two explicitly contrasting the existential (v14) vs. universal (v15) claim in the introduction would help readers immediately grasp the upgrade. |
| **Reproducibility** | 4.5/5 | Unchanged. The Lean proofs are self-contained and reproducible. The Python pipeline remains external but documented. |

---

## Detailed Comments

### 1. Exhaustive NE Enumeration (New, Major Positive)

This is the most significant change across all five revision rounds. The move from "there exists a symmetric NE that excludes Dragapult" to "every symmetric NE excludes Dragapult" transforms the headline result from a possibility claim into a necessity claim. The enumeration over 2^14 − 1 = 16,383 support subsets is computationally modest but formally demanding — each subset requires verifying the NE conditions (best-response and support constraints). That this was done within Lean rather than as an external computation is commendable.

**Question for the authors:** How long does the exhaustive enumeration take to check in Lean? A brief note on compilation/verification time would be informative for readers considering similar approaches at larger scales (e.g., 20+ species metagames).

### 2. Swiss-Pairing Model (Resolved)

The Glickman and TrueSkill references appropriately ground the matchmaking model. No further action needed.

### 3. Table VIII Exact Counts (Resolved)

The removal of "~" and replacement with exact counts is a small but important change for a paper whose core contribution is formal precision. Satisfied.

### 4. Python Sensitivity Analysis (Accepted Limitation)

I continue to note that the sensitivity analysis lives outside the Lean verification boundary. The authors have been transparent about this throughout. I do not consider it a blocking issue, but future work should explore whether perturbation bounds can be internalized (e.g., via interval arithmetic in Lean 4). This would make the robustness claims as strong as the equilibrium claims.

### 5. Empirical Novelty (Structural, Unchanged)

The paper confirms what high-level competitive players already know: Dragapult underperforms in the current metagame despite usage rates. The formal verification adds rigor but not surprise. I flag this for the editors' awareness but do not penalize the score further — the methodological contribution carries the paper.

---

## Minor Comments

- The unique-NE result should be featured more prominently in the abstract. Currently it reads as a technical detail rather than the paper's strongest formal contribution.
- Consider adding a brief discussion of whether uniqueness is fragile — i.e., how much would payoff entries need to change before an alternative NE including Dragapult appears? This connects naturally to the sensitivity analysis.
- Typographical: "equilibria" is used inconsistently as both singular and plural in Section VI.

---

## Overall Recommendation

**Accept (4/5)**

Upgraded from Weak Accept in v14. The exhaustive NE enumeration resolves my primary technical reservation — the gap between existential and universal claims. The paper now presents a clean, formally verified, and exhaustive result: Dragapult is excluded from *every* symmetric Nash equilibrium of the 14-species metagame. Combined with the resolved Swiss-pairing and Table VIII issues, the paper meets the standard for publication in IEEE Transactions on Games.

The remaining concerns (external Python pipeline, confirmatory empirical findings) are genuine but not sufficient to withhold acceptance. The methodological contribution — applying Lean 4 verification with exhaustive equilibrium enumeration to a competitive esports metagame — is novel and technically sound enough to merit publication.

---

*Reviewer 2 — Empirical Game Theory / Competitive Esports Analytics*
*Round 5 (v15) — 2026-02-21*
