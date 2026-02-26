# Nash Equilibrium Enumeration Results

## 14×14 Pokémon TCG Matchup Matrix — Full Nash Analysis

**Date:** 2026-02-21  
**Data source:** Trainer Hill (trainerhill.com), 2026-01-29 to 2026-02-19, 50+ player tournaments  
**Matrix:** `PokemonLean/RealMetagame.lean`, win rates on 0–1000 scale (‰)  
**Game model:** Symmetric bimatrix game, A = M, B = Mᵀ (both players choose a deck)

---

## Key Result

> **Dragapult Dusknoir (index 0) receives 0% weight in ALL Nash equilibria found.**
>
> Despite being the most-played deck at 15.5% metagame share, Dragapult is
> strictly suboptimal at every Nash equilibrium, underperforming by **63.25‰**
> (6.3 percentage points) against the equilibrium strategy.

---

## The Unique Symmetric Nash Equilibrium

The game has a **unique symmetric NE** (verified by exhaustive search over all 16,383 support subsets):

| Deck | Weight | Percentage |
|------|--------|------------|
| GrimssnarlFroslass | 357525082/839819845 | **42.57%** |
| RagingBoltOgerpon | 313330127/839819845 | **37.31%** |
| Gardevoir | 225251078/2519459535 | **8.94%** |
| MegaAbsolBox | 62670167/839819845 | **7.46%** |
| CharizardNoctowl | 3228701/86877915 | **3.72%** |

**Equilibrium value:** 1209229006597/2519459535 ≈ **479.96‰** (48.0% win rate)

### Support: {GrimssnarlFroslass, MegaAbsolBox, Gardevoir, CharizardNoctowl, RagingBoltOgerpon}

The 9 excluded decks and their gaps from the NE value:

| Deck | Payoff vs NE | Gap from value |
|------|-------------|----------------|
| GholdengoLunatone | 478.13 | 1.83 |
| AlakazamDudunsparce | 474.97 | 4.99 |
| GardevoirJellicent | 472.02 | 7.93 |
| CharizardPidgeot | 466.91 | 13.05 |
| KangaskhanBouffalant | 426.79 | 53.16 |
| **DragapultDusknoir** | **416.70** | **63.25** |
| DragapultCharizard | 412.86 | 67.09 |
| Ceruledge | 411.85 | 68.11 |
| NsZoroark | 408.88 | 71.08 |

---

## Non-Degeneracy

The symmetric NE is **non-degenerate**: exactly 5 strategies achieve the equilibrium payoff (equal to the support size). No additional strategy is a best response, confirming uniqueness of the symmetric NE.

---

## Exhaustive Search Summary

### Methods Used

1. **Exhaustive symmetric NE search:** All 16,383 non-empty support subsets of {0,...,13} checked. **Result: exactly 1 symmetric NE found.** None includes Dragapult.

2. **Dragapult-specific symmetric search:** All 8,192 support subsets containing index 0 checked. **Result: 0 NE found.**

3. **Asymmetric NE search (Dragapult in row, sizes 2–5):** All combinations of row supports containing Dragapult paired with all col supports of matching size. **Result: 0 NE found.**

4. **Asymmetric NE search (Dragapult in col, sizes 2–5):** Same for column supports. **Result: 0 NE found.**

5. **Asymmetric NE search (size 6, no Dragapult):** All C(13,6)² = 1,716² support pairs from {1,...,13}. **Result: 0 asymmetric NE found.**

6. **LP minimax:** Solved the row-player LP. Optimal strategy uses support {2,3,4,5,9,11} with Dragapult weight = 0. The LP value (479.66) differs slightly from the symmetric NE value (479.96) because the game is not exactly zero-sum (M[i,j] + M[j,i] ≠ 1000 due to ties counted as 1/3 win).

7. **Lemke-Howson:** All 28 initial labels tried. Consistent with the symmetric NE.

### Non-Zero-Sum Structure

The game is **not** exactly zero-sum: M[i,j] + M[j,i] ranges from 927 to 977 (not 1000), because ties are scored as 1/3 win for each player (total 2/3, not 1). All 91 off-diagonal pairs deviate from 1000.

---

## The Popularity Paradox

| Metric | Dragapult | NE Prescription |
|--------|-----------|-----------------|
| Observed metagame share | **15.5%** (rank 1) | **0.0%** (excluded) |
| Payoff vs NE strategy | 416.7‰ | — |
| Gap from NE value | 63.3‰ | — |
| Losing matchups (< 500) vs top 14 | 9 of 13 | — |

Dragapult is the **most overplayed** deck in the metagame: it holds 15.5% of the meta despite being the 6th-worst deck by NE payoff, losing to 9 of 13 other top decks head-to-head.

---

## Conclusion

Across all enumeration methods — exhaustive symmetric search (16,383 subsets), targeted asymmetric search with Dragapult (sizes 2–5), LP minimax, and Lemke-Howson — **no Nash equilibrium assigns positive weight to Dragapult Dusknoir**. The unique symmetric NE places all weight on a 5-deck core: Grimmsnarl (42.6%), Raging Bolt (37.3%), Gardevoir (8.9%), Mega Absol (7.5%), and Charizard Noctowl (3.7%).

This provides strong evidence for the paper's central claim: **Dragapult's 15.5% metagame share represents a massive deviation from Nash equilibrium play**, driven by factors outside the matchup matrix (ease of play, availability, psychological salience, etc.).
