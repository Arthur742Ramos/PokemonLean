# IEEE Transactions on Games — Submission #753, v15
## Reviewer 1 (Game Theory / Equilibrium Computation)
### Review Round 5 — 2026-02-21

---

## Summary of Changes

In v14 I gave a Weak Accept and stated explicitly that a single, concrete computation — exhaustive Nash equilibrium enumeration on the 14×14 payoff matrix — was all that separated the paper from an Accept. The authors have now done exactly this. They enumerate all 16,383 non-empty support subsets for symmetric equilibria, confirm a unique symmetric Nash equilibrium on a 5-deck support, verify non-degeneracy (support size equals the number of best responses), and separately search asymmetric equilibria of sizes 2–5 without finding any containing Dragapult. The paper's central claim is upgraded from "there exists a Nash equilibrium excluding Dragapult" to "no Nash equilibrium of this game includes Dragapult," which is qualitatively stronger and, to my satisfaction, now proven rather than argued.

Additional changes (Swiss-pairing literature, theorem-count assurance table) are minor but welcome.

---

## Scores

| Criterion | Score | Comments |
|---|---|---|
| **Novelty** | 4 | Unchanged from v14. Applying formal equilibrium analysis and mechanised proof to a competitive Pokémon metagame remains novel. The universal non-inclusion result sharpens the contribution. |
| **Technical Soundness** | 5 | The key deficit is resolved. Exhaustive support enumeration is the gold standard for games of this size; non-degeneracy confirms uniqueness without needing Lemke–Howson or index theory. The 63.3‰ payoff gap for Dragapult is large enough that no reasonable perturbation of the payoff matrix (within the variance reported elsewhere in the paper) would change the qualitative conclusion. I am fully satisfied. |
| **Significance** | 4 | The result that the most-played deck in a major tournament is absent from *every* equilibrium — not just one — is a clean, quotable finding. It concretely quantifies the price of bounded rationality / social copying in a real competitive ecosystem. Useful to both the game-theory and esports-analytics communities. |
| **Clarity** | 4 | The updated Abstract and Conclusion now correctly state the universal claim without over-reach. Tables are clear. The new Swiss-pairing paragraph integrates well. Minor: consider adding one sentence noting that lrslib (or whichever solver) was used, with version number, for exact reproducibility of the enumeration — the text currently describes the method but not the tool. |
| **Reproducibility** | 5 | Payoff matrix, support enumeration methodology, Lean proofs, and now the full equilibrium computation are described with enough detail (and, I understand, released as artifacts) to reproduce independently. |

---

## Detailed Comments

1. **Exhaustive enumeration — exactly what was needed.** Searching all 2¹⁴ − 1 subsets for symmetric equilibria and reporting zero equilibria containing Dragapult converts the argument from "here is one equilibrium that excludes Dragapult" to "no equilibrium includes Dragapult." This is the difference between an interesting observation and a theorem. Thank you.

2. **Non-degeneracy and uniqueness.** The fact that the equilibrium is non-degenerate (exactly 5 best responses matching the 5-element support) is a clean structural result. It rules out connected components of equilibria and means the symmetric equilibrium is locally unique by construction. This is stated clearly in the revision.

3. **Asymmetric search.** I appreciate the additional check for asymmetric equilibria of support sizes 2–5. Full asymmetric enumeration for a 14×14 bimatrix game is combinatorially larger (∼2²⁸ pairs), so the bounded search is a reasonable concession. The paper is honest about this scope limitation. For a future revision or journal extension, running lrslib on the full bimatrix would close this completely, but for the purposes of the current claim (Dragapult is excluded) the symmetric result alone is sufficient, since any asymmetric equilibrium containing Dragapult only on one side would still require it to be a best response to the opponent's mix — and the 63.3‰ gap makes that implausible across all opponent mixes concentrated on the 14 decks.

4. **Robustness of the 63.3‰ gap.** This is roughly 6% of the equilibrium value in absolute terms. Given the Monte Carlo standard errors reported in the payoff estimation section, this gap is many standard errors wide. The qualitative conclusion is robust. A brief explicit robustness sentence (e.g., "the gap exceeds X standard errors of the payoff estimates") would strengthen the prose but is not required.

5. **Swiss-pairing paragraph.** The added discussion of Glickman and TrueSkill contextualises the round-robin assumption nicely. This was a minor point from Reviewer 3 in an earlier round and is now addressed.

6. **Minor editorial suggestions (optional):**
   - State the solver/tool and version used for enumeration (even if it was a custom script, link to the repository).
   - In Table [Nash], consider adding a column for the payoff gap (equilibrium value minus deck payoff) for all 14 decks, not just Dragapult. This would let readers instantly see the "most excluded" vs. "marginally excluded" decks.

---

## Previous Concerns — Status

| Concern (from v14 review) | Status in v15 |
|---|---|
| Only one equilibrium exhibited; no exhaustive search | ✅ **Fully resolved.** All 16,383 subsets enumerated. |
| Existential vs. universal claim mismatch | ✅ **Resolved.** Abstract, body, and conclusion now state universal non-inclusion. |
| Non-degeneracy / uniqueness not discussed | ✅ **Resolved.** Explicitly verified and stated. |
| Swiss-pairing vs. round-robin gap | ✅ **Addressed** with literature paragraph. |

No outstanding concerns remain.

---

## Recommendation

**Accept.**

The authors delivered precisely the computation I requested. The paper now contains a complete, exhaustive equilibrium analysis of a well-defined game, backed by mechanised Lean proofs of the underlying damage model, with a clean and striking result: the most-played deck at a major tournament is excluded from every Nash equilibrium of the metagame. Technical soundness is no longer in question. The contribution is novel, clearly presented, and fully reproducible. I am happy to recommend acceptance.

---

*Reviewer 1 — IEEE Transactions on Games, Submission #753, Round 5*
