# Nash Equilibrium Enumeration Results (Symmetrized Constant-Sum Game)

## 14x14 Pokemon TCG Matchup Matrix - Symmetric Nash Analysis

**Data source:** Trainer Hill (trainerhill.com), 2026-01-29 to 2026-02-19, 50+ player tournaments
**Matrix:** `PokemonLean/RealMetagame.lean`, win rates on 0-1000 scale (permil)
**Game model:** Constant-sum *symmetrization* S_ij = (M_ij + 1000 - M_ji)/2, so S_ij + S_ji = 1000.
**Reproduce:** `python scripts/enumerate_symmetric_nash.py` (exact rational arithmetic).
**Cross-checked against Lean:** `PokemonLean/SymmetricNash.lean`
(`symmetric_nash_equilibrium_verified`, `symmetric_nash_dragapult_strict_gap`).

---

## Key Result

> **Dragapult Dusknoir (index 0) receives 0% weight in the unique symmetric Nash equilibrium,**
> **and is excluded from the support of EVERY equilibrium (symmetric or asymmetric).**
>
> Despite being the most-played deck at 15.5% metagame share, Dragapult's payoff against
> the equilibrium mix is 459.58 permil, a strict gap of **40.42 permil** (4.0 percentage
> points) below the game value of 500.

---

## The Unique Symmetric Nash Equilibrium

Exhaustive search over all 2^14 - 1 = 16,383 support subsets (exact arithmetic) yields
**exactly one** symmetric Nash equilibrium. Game value: **exactly 500 permil (50.0%)**.

| Deck | Weight | Percentage |
|------|--------|-----------|
| GrimssnarlFroslass | 8263687/24079072 | **34.32%** |
| RagingBoltOgerpon | 7082354/24079072 | **29.41%** |
| MegaAbsolBox | 2458226/24079072 | **10.21%** |
| CharizardNoctowl | 2445605/24079072 | **10.16%** |
| GholdengoLunatone | 2203079/24079072 | **9.15%** |
| Gardevoir | 1033093/24079072 | **4.29%** |
| AlakazamDudunsparce | 593028/24079072 | **2.46%** |

**Support (7 decks):** Grimmsnarl, Raging Bolt, Mega Absol, Charizard Noctowl,
Gholdengo, Gardevoir, Alakazam.

### Excluded decks and their payoff gaps from the value (500 permil)

| Deck | Payoff vs NE | Gap from value |
|------|-------------|----------------|
| GardevoirJellicent | 489.65 | -10.35 |
| CharizardPidgeot | 482.99 | -17.01 |
| DragapultCharizard | 460.55 | -39.45 |
| DragapultDusknoir | 459.58 | -40.42 |
| KangaskhanBouffalant | 455.46 | -44.54 |
| Ceruledge | 444.50 | -55.50 |
| NsZoroark | 441.36 | -58.64 |

---

## Uniqueness and Non-Degeneracy

- Exactly one symmetric equilibrium exists over all 16,383 support subsets.
- The equilibrium is non-degenerate: exactly seven pure strategies achieve the value,
  matching the seven-deck support, which implies uniqueness for constant-sum games.
- Of the 8,192 subsets containing Dragapult, **none** yields a valid equilibrium.

## Equilibrium-Independent Exclusion of Dragapult

In a constant-sum game with value v, complementary slackness forces the support of every
optimal strategy to lie in the best-response set of every optimal opponent strategy. The
symmetric strategy is optimal for both players, and Dragapult scores 459.58 < 500 = v
against it. Therefore Dragapult is a best response to no optimal strategy and appears in
the support of **no** Nash equilibrium - symmetric or asymmetric. This is verified in Lean
as `symmetric_nash_dragapult_strict_gap`.

---

*This document supersedes the earlier `nash_enumeration_results.md`, which reported figures
from a non-symmetrized (A=M, B=M^T) model that the manuscript does not use.*
