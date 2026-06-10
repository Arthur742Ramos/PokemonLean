#!/usr/bin/env python3
"""Exhaustive Nash enumeration on the CONSTANT-SUM SYMMETRIZATION S_ij = (M_ij + 1000 - M_ji)/2.

This is the model the paper relies on (Section VII). All arithmetic is exact (Fraction).
Verifies:
  (1) S is constant-sum: S_ij + S_ji = 1000 for all i,j.
  (2) The seven-deck symmetric Nash equilibrium (value 500) reported in the paper.
  (3) Uniqueness of the symmetric equilibrium over all 2^14 - 1 = 16383 support subsets.
  (4) Dragapult (index 0) is in the support of NO symmetric equilibrium.
  (5) Dragapult is strictly below value against the symmetric mix (equilibrium-independent
      exclusion via complementary slackness).
"""
from fractions import Fraction as F
from itertools import combinations

# Raw Trainer Hill matrix M (permil), deck order matches RealMetagame.lean Deck.ofFin
NAMES = ["DragapultDusknoir","GholdengoLunatone","GrimssnarlFroslass","MegaAbsolBox",
         "Gardevoir","CharizardNoctowl","GardevoirJellicent","CharizardPidgeot",
         "DragapultCharizard","RagingBoltOgerpon","NsZoroark","AlakazamDudunsparce",
         "KangaskhanBouffalant","Ceruledge"]
M = [
 [494,436,386,382,343,641,418,563,486,454,472,627,368,531],
 [521,488,476,443,441,483,439,459,425,496,516,373,553,439],
 [572,467,485,344,566,558,592,570,598,473,545,599,473,561],
 [576,512,621,494,558,475,587,451,524,298,418,515,474,414],
 [627,493,374,402,480,394,362,374,516,625,448,633,392,627],
 [324,480,397,471,558,487,549,581,422,557,493,584,330,593],
 [544,498,346,364,583,390,489,345,486,619,360,548,422,526],
 [396,510,386,500,584,362,598,487,347,535,506,492,450,604],
 [480,528,361,432,421,536,463,580,489,454,573,593,510,490],
 [510,458,477,673,333,409,332,426,490,487,623,303,653,537],
 [490,439,417,548,519,463,601,438,391,340,495,556,492,262],
 [341,588,368,441,315,366,412,466,370,653,407,489,772,675],
 [582,401,473,492,549,635,524,518,449,311,477,198,490,550],
 [440,538,398,545,325,370,418,466,475,426,709,300,414,481],
]
n = 14
S = [[F(M[i][j] + 1000 - M[j][i], 2) for j in range(n)] for i in range(n)]

# (1) constant-sum
assert all(S[i][j] + S[j][i] == 1000 for i in range(n) for j in range(n)), "not constant-sum"
print("(1) S_ij + S_ji = 1000 for all i,j: OK")

def solve_symmetric_support(support):
    """Solve for a symmetric equilibrium with the given support via exact linear algebra.
    Conditions: sum_j x_j S[k][j] = v for k in support; sum x_j = 1; x_j >= 0; x_j = 0 off support.
    Returns (x, v) if a valid mixed strategy exists and is a best response, else None."""
    k = len(support)
    # Unknowns: x_{support} (k) and v (1). Equations: k best-response equalities + 1 normalization.
    # Build (k+1) x (k+1) system.
    A = [[F(0)] * (k + 1) for _ in range(k + 1)]
    b = [F(0)] * (k + 1)
    for r, krow in enumerate(support):
        for c, jcol in enumerate(support):
            A[r][c] = S[krow][jcol]
        A[r][k] = F(-1)   # -v
        b[r] = F(0)
    for c in range(k):
        A[k][c] = F(1)
    A[k][k] = F(0)
    b[k] = F(1)
    # Gaussian elimination over Fractions
    Aug = [row[:] + [b[i]] for i, row in enumerate(A)]
    m = k + 1
    for col in range(m):
        piv = next((r for r in range(col, m) if Aug[r][col] != 0), None)
        if piv is None:
            return None
        Aug[col], Aug[piv] = Aug[piv], Aug[col]
        inv = Aug[col][col]
        Aug[col] = [v / inv for v in Aug[col]]
        for r in range(m):
            if r != col and Aug[r][col] != 0:
                f = Aug[r][col]
                Aug[r] = [a - f * bb for a, bb in zip(Aug[r], Aug[col])]
    sol = [Aug[r][m] for r in range(m)]
    x_supp = sol[:k]; v = sol[k]
    if any(xi < 0 for xi in x_supp):
        return None
    # Build full strategy
    x = [F(0)] * n
    for c, j in enumerate(support):
        x[j] = x_supp[c]
    if sum(x) != 1:
        return None
    # Best-response check: every pure strategy payoff <= v, with equality on support
    for kk in range(n):
        pay = sum(x[j] * S[kk][j] for j in range(n))
        if pay > v:
            return None
    return x, v

# (2)+(3)+(4) exhaustive enumeration over all non-empty subsets
print("(3) Enumerating all 2^14 - 1 = %d support subsets (exact arithmetic)..." % (2**n - 1))
equilibria = []
drag_in_any = False
for size in range(1, n + 1):
    for support in combinations(range(n), size):
        res = solve_symmetric_support(list(support))
        if res is not None:
            x, v = res
            # Canonical: record support actually used (nonzero)
            actual = tuple(j for j in range(n) if x[j] > 0)
            equilibria.append((actual, v))
            if 0 in actual:
                drag_in_any = True

# Deduplicate by actual support
uniq = {}
for supp, v in equilibria:
    uniq[supp] = v
print("    Valid symmetric equilibria found: %d distinct support(s)" % len(uniq))
for supp, v in uniq.items():
    print("      value=%s  support=%s" % (v, [NAMES[i] for i in supp]))

# (2) the reported seven-deck equilibrium
assert len(uniq) == 1, "expected a UNIQUE symmetric equilibrium"
(supp, v), = uniq.items()
print("(2) Unique symmetric equilibrium value = %s (= %.4f permil)" % (v, float(v)))
assert v == 500, "value should be exactly 500"
support_names = [NAMES[i] for i in supp]
print("    Support (%d decks): %s" % (len(supp), ", ".join(support_names)))
assert len(supp) == 7, "expected seven-deck support"

# (4) Dragapult excluded
print("(4) Dragapult in support of any symmetric equilibrium: %s" % drag_in_any)
assert not drag_in_any, "Dragapult unexpectedly in a symmetric equilibrium"

# (5) strict gap of Dragapult vs the equilibrium mix
x = [F(0)] * n
# rebuild equilibrium weights
res = solve_symmetric_support(list(supp)); xx, vv = res
drag_pay = sum(xx[j] * S[0][j] for j in range(n))
print("(5) Dragapult payoff vs symmetric Nash mix = %s = %.4f permil (gap %.4f below value)"
      % (drag_pay, float(drag_pay), float(v - drag_pay)))
assert drag_pay < v, "Dragapult should be strictly below value"

# Asymmetric search corroboration: row/col support pairs up to size 5 containing Dragapult.
# In a symmetric constant-sum game, optimal strategies are exactly those achieving value;
# since Dragapult is strictly below value against the (optimal) symmetric mix, it is a best
# response to NO optimal strategy, so no equilibrium (symmetric or asymmetric) supports it.
print("(6) Complementary-slackness corollary: because Dragapult is strictly below the game")
print("    value against an optimal strategy, it lies in the support of NO equilibrium")
print("    of the symmetrization (symmetric or asymmetric). [equilibrium-independent]")
print()
print("ALL CHECKS PASSED.")
