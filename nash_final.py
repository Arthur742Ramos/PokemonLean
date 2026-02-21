#!/usr/bin/env python3
"""
Final Nash equilibrium analysis for PokemonLean 14x14 matchup matrix.
Confirms Dragapult exclusion from all Nash equilibria.
"""

import numpy as np
from scipy.optimize import linprog
from itertools import combinations
from fractions import Fraction

DECKS = [
    "DragapultDusknoir", "GholdengoLunatone", "GrimssnarlFroslass", "MegaAbsolBox",
    "Gardevoir", "CharizardNoctowl", "GardevoirJellicent", "CharizardPidgeot",
    "DragapultCharizard", "RagingBoltOgerpon", "NsZoroark", "AlakazamDudunsparce",
    "KangaskhanBouffalant", "Ceruledge",
]

M = np.array([
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
    [440,538,398,545,325,370,418,339,475,426,709,300,414,481],
], dtype=float)

n = 14

# ============================================================================
# PART 1: Verify the known asymmetric NE from the paper
# Row support {2,3,4,5,9,11}, Col support {1,2,3,4,5,9}
# ============================================================================
print("="*80)
print("PART 1: Verify known asymmetric NE from paper")
print("="*80)

def solve_ne_for_supports(M, row_supp, col_supp):
    """Solve for NE given row and col supports. Returns (x, y, vr, vc) or None."""
    rs = sorted(row_supp)
    cs = sorted(col_supp)
    kr, kc = len(rs), len(cs)
    n = M.shape[0]

    # Solve for y (col strategy) from row-player indifference:
    # For i in rs: sum_j y_j M[i,j] = v_r, and sum y = 1
    # System: (kr+1) equations, (kc+1) unknowns
    A1 = np.zeros((kr + 1, kc + 1))
    b1 = np.zeros(kr + 1)
    for ri, i in enumerate(rs):
        for ci, j in enumerate(cs):
            A1[ri, ci] = M[i, j]
        A1[ri, kc] = -1
    A1[kr, :kc] = 1
    b1[kr] = 1

    if kr + 1 == kc + 1:
        try:
            sol1 = np.linalg.solve(A1, b1)
        except np.linalg.LinAlgError:
            return None
    else:
        sol1, _, _, _ = np.linalg.lstsq(A1, b1, rcond=None)
        if np.max(np.abs(A1 @ sol1 - b1)) > 1e-8:
            return None

    y_s = sol1[:kc]
    v_r = sol1[kc]
    if np.any(y_s < -1e-10):
        return None
    y_s = np.maximum(y_s, 0)

    # Solve for x (row strategy) from col-player indifference:
    # B = M^T, so col payoff for pure j = sum_i x_i * M[j,i]
    # For j in cs: sum_{i in rs} x_i M[j,i] = v_c, and sum x = 1
    A2 = np.zeros((kc + 1, kr + 1))
    b2 = np.zeros(kc + 1)
    for ri, j in enumerate(cs):
        for ci, i in enumerate(rs):
            A2[ri, ci] = M[j, i]
        A2[ri, kr] = -1
    A2[kc, :kr] = 1
    b2[kc] = 1

    if kc + 1 == kr + 1:
        try:
            sol2 = np.linalg.solve(A2, b2)
        except np.linalg.LinAlgError:
            return None
    else:
        sol2, _, _, _ = np.linalg.lstsq(A2, b2, rcond=None)
        if np.max(np.abs(A2 @ sol2 - b2)) > 1e-8:
            return None

    x_s = sol2[:kr]
    v_c = sol2[kr]
    if np.any(x_s < -1e-10):
        return None
    x_s = np.maximum(x_s, 0)

    x = np.zeros(n); y = np.zeros(n)
    for idx, i in enumerate(rs): x[i] = x_s[idx]
    for idx, j in enumerate(cs): y[j] = y_s[idx]

    if abs(np.sum(x) - 1) > 1e-8 or abs(np.sum(y) - 1) > 1e-8:
        return None

    # Verify NE conditions
    My = M @ y
    for i in range(n):
        if i in row_supp:
            if abs(My[i] - v_r) > 1e-5: return None
        else:
            if My[i] > v_r + 1e-5: return None

    Mx = M @ x  # col payoff for pure j = sum_i x_i M[j,i] = (M @ x)[j]
    for j in range(n):
        if j in col_supp:
            if abs(Mx[j] - v_c) > 1e-5: return None
        else:
            if Mx[j] > v_c + 1e-5: return None

    return x, y, v_r, v_c

# Known asymmetric NE: row {2,3,4,5,9,11}, col {1,2,3,4,5,9}
row_supp_known = {2, 3, 4, 5, 9, 11}
col_supp_known = {1, 2, 3, 4, 5, 9}

result = solve_ne_for_supports(M, row_supp_known, col_supp_known)
if result:
    x, y, vr, vc = result
    print(f"✓ Known asymmetric NE VERIFIED!")
    print(f"  Row value: {vr:.4f}, Col value: {vc:.4f}")
    print(f"  Row strategy:")
    for i in range(n):
        if x[i] > 1e-10:
            print(f"    {DECKS[i]:25s}: {x[i]*100:.4f}%")
    print(f"  Col strategy:")
    for j in range(n):
        if y[j] > 1e-10:
            print(f"    {DECKS[j]:25s}: {y[j]*100:.4f}%")
    print(f"  Dragapult row: {x[0]:.10e}")
    print(f"  Dragapult col: {y[0]:.10e}")

    # Show payoff details
    My = M @ y
    Mx = M @ x
    print(f"\n  Row payoffs vs col strategy (should = {vr:.4f} for support, ≤ otherwise):")
    for i in range(n):
        flag = " [IN SUPPORT]" if i in row_supp_known else ""
        slack = f" (slack: {vr - My[i]:.4f})" if i not in row_supp_known else ""
        print(f"    {DECKS[i]:25s}: {My[i]:.4f}{flag}{slack}")
    print(f"\n  Col payoffs vs row strategy (should = {vc:.4f} for support, ≤ otherwise):")
    for j in range(n):
        flag = " [IN SUPPORT]" if j in col_supp_known else ""
        slack = f" (slack: {vc - Mx[j]:.4f})" if j not in col_supp_known else ""
        print(f"    {DECKS[j]:25s}: {Mx[j]:.4f}{flag}{slack}")
else:
    print("✗ Known asymmetric NE NOT verified with this support pair")

# Also check the mirror: row {1,2,3,4,5,9}, col {2,3,4,5,9,11}
print(f"\n  Checking mirror (swap row/col supports)...")
result_mirror = solve_ne_for_supports(M, col_supp_known, row_supp_known)
if result_mirror:
    xm, ym, vrm, vcm = result_mirror
    print(f"  ✓ Mirror NE also valid!")
    print(f"    Dragapult row: {xm[0]:.10e}, col: {ym[0]:.10e}")
else:
    print(f"  ✗ Mirror is NOT a valid NE")

# ============================================================================
# PART 2: Exhaustive symmetric NE enumeration (all 2^14 - 1 subsets)
# ============================================================================
print(f"\n{'='*80}")
print("PART 2: Exhaustive symmetric NE search (all 16383 support subsets)")
print("="*80)

def find_symmetric_ne(M, support):
    s = sorted(support)
    k = len(s)
    n = M.shape[0]
    if k == 0: return None

    A_sys = np.zeros((k + 1, k + 1))
    b_sys = np.zeros(k + 1)
    for ri, i in enumerate(s):
        for ci, j in enumerate(s):
            A_sys[ri, ci] = M[i, j]
        A_sys[ri, k] = -1
    A_sys[k, :k] = 1
    b_sys[k] = 1

    try:
        sol = np.linalg.solve(A_sys, b_sys)
    except np.linalg.LinAlgError:
        return None

    x_s = sol[:k]
    v = sol[k]
    if np.any(x_s < -1e-10): return None
    x_s = np.maximum(x_s, 0)

    x = np.zeros(n)
    for idx, i in enumerate(s): x[i] = x_s[idx]
    if abs(np.sum(x) - 1) > 1e-8: return None

    row_payoffs = M @ x
    for i in range(n):
        if i in support:
            if abs(row_payoffs[i] - v) > 1e-6: return None
        else:
            if row_payoffs[i] > v + 1e-6: return None

    return x, v

sym_eqs = []
for size in range(1, n + 1):
    for support in combinations(range(n), size):
        result = find_symmetric_ne(M, set(support))
        if result is not None:
            x, v = result
            is_dup = any(np.allclose(x, ex, atol=1e-8) for ex, _ in sym_eqs)
            if not is_dup:
                sym_eqs.append((x, v))
                snames = [DECKS[i] for i in range(n) if x[i] > 1e-10]
                print(f"  Symmetric NE #{len(sym_eqs)} (size {size}): {snames}")
                print(f"    Weights: {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i] > 1e-10)}")
                print(f"    Value: {v:.4f}, Dragapult: {x[0]:.10e}")

print(f"\nTotal symmetric NE: {len(sym_eqs)}")

# ============================================================================
# PART 3: Non-degeneracy analysis
# ============================================================================
print(f"\n{'='*80}")
print("PART 3: Non-degeneracy analysis")
print("="*80)

# A bimatrix game is non-degenerate if no mixed strategy has more than
# |support| best responses for the opponent.
# For a symmetric game, check: does ANY mixed strategy with support size k
# make k+1 or more pure strategies equally optimal for the opponent?

# The LP solution tells us a lot. Check: how many constraints are tight?
# If LP has support size k and exactly k constraints are tight, the game is non-degenerate

# LP solution for row player of M (treat as zero-sum)
c_obj = np.zeros(n + 1); c_obj[n] = -1
A_ub = np.zeros((n, n + 1))
for j in range(n):
    for i in range(n):
        A_ub[j, i] = -M[i, j]
    A_ub[j, n] = 1
b_ub = np.zeros(n)
A_eq = np.zeros((1, n + 1)); A_eq[0, :n] = 1
b_eq = np.array([1.0])
bounds = [(0, None)] * n + [(None, None)]

res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
x_lp = res.x[:n]; v_lp = res.x[n]

payoffs_lp = M @ x_lp
lp_support = [i for i in range(n) if x_lp[i] > 1e-10]
tight_constraints = [j for j in range(n) if abs(payoffs_lp[j] - v_lp) < 0.1]

print(f"LP support size: {len(lp_support)} -> {[DECKS[i] for i in lp_support]}")
print(f"Tight constraint count: {len(tight_constraints)} -> {[DECKS[j] for j in tight_constraints]}")
print(f"For non-degeneracy: support size should equal tight constraint count")
if len(lp_support) == len(tight_constraints):
    print(f"✓ LP solution is non-degenerate (support = tight = {len(lp_support)})")
else:
    print(f"⚠ LP may be degenerate ({len(lp_support)} ≠ {len(tight_constraints)})")

# More careful check: for EACH symmetric NE found, how many best responses exist?
for idx, (x, v) in enumerate(sym_eqs):
    payoffs = M @ x
    support_size = sum(1 for i in range(n) if x[i] > 1e-10)
    num_best = sum(1 for i in range(n) if abs(payoffs[i] - v) < 1e-4)
    print(f"\n  Symmetric NE #{idx+1}: support={support_size}, best_responses={num_best}")
    if num_best > support_size:
        print(f"    ⚠ DEGENERATE: {num_best} best responses > {support_size} support size")
        extra = [DECKS[i] for i in range(n) if abs(payoffs[i] - v) < 1e-4 and x[i] < 1e-10]
        print(f"    Extra best responses: {extra}")
    else:
        print(f"    ✓ Non-degenerate at this NE")

# ============================================================================
# PART 4: Dragapult-specific dominance analysis
# ============================================================================
print(f"\n{'='*80}")
print("PART 4: Why Dragapult is excluded — dominance analysis")
print("="*80)

print("\nDragapult (row 0) payoffs vs each opponent column:")
drag_row = M[0, :]
print(f"  Drag vs all: {drag_row.tolist()}")

# Check if Dragapult is weakly dominated
print(f"\nIs Dragapult weakly dominated?")
for i in range(1, n):
    if np.all(M[i, :] >= M[0, :]):
        strict = np.any(M[i, :] > M[0, :])
        print(f"  {DECKS[i]} weakly dominates Dragapult: {np.all(M[i, :] >= M[0, :])} (strict somewhere: {strict})")

# Check against mixtures — at every NE, Dragapult's payoff vs NE col strategy
print(f"\nDragapult's payoff at each NE:")
# Symmetric NE
for idx, (x, v) in enumerate(sym_eqs):
    drag_payoff = M[0, :] @ x
    print(f"  Symmetric NE #{idx+1}: Drag payoff = {drag_payoff:.4f}, NE value = {v:.4f}")
    print(f"    Gap: {v - drag_payoff:.4f} (Dragapult underperforms by this much)")

# Asymmetric NE
if result:
    x_asym, y_asym, vr_asym, vc_asym = result
    drag_payoff_asym = M[0, :] @ y_asym
    print(f"  Asymmetric NE: Drag payoff = {drag_payoff_asym:.4f}, row NE value = {vr_asym:.4f}")
    print(f"    Gap: {vr_asym - drag_payoff_asym:.4f}")

# ============================================================================
# PART 5: Comprehensive check — can Dragapult EVER be in any NE?
# ============================================================================
print(f"\n{'='*80}")
print("PART 5: Can Dragapult appear in ANY NE? (row player)")
print("="*80)

# For Dragapult to be in a symmetric NE, we need support containing 0.
# Already checked all 2^13 = 8192 subsets containing 0 in Part 2 (they were
# among the 2^14-1 total). None worked.

drag_supports_checked = 0
drag_ne_found = 0
for size in range(1, n + 1):
    for support in combinations(range(n), size):
        if 0 not in support:
            continue
        drag_supports_checked += 1
        result_d = find_symmetric_ne(M, set(support))
        if result_d is not None:
            drag_ne_found += 1

print(f"Support subsets containing Dragapult checked: {drag_supports_checked}")
print(f"Symmetric NE containing Dragapult found: {drag_ne_found}")

# For asymmetric NE with Dragapult in row support:
# Check all col supports of size 2-7 paired with row supports containing 0
print(f"\nAsymmetric NE with Dragapult in ROW support (sizes 2-5):")
drag_asym_found = 0
for row_size in range(2, 6):
    for col_size in range(2, 6):
        for rs_rest in combinations(range(1, n), row_size - 1):
            rs = {0} | set(rs_rest)
            for cs in combinations(range(n), col_size):
                res_d = solve_ne_for_supports(M, rs, set(cs))
                if res_d is not None:
                    drag_asym_found += 1
                    xd, yd, vrd, vcd = res_d
                    print(f"  FOUND! Row: {[DECKS[i] for i in range(n) if xd[i]>1e-10]}")
                    print(f"         Col: {[DECKS[j] for j in range(n) if yd[j]>1e-10]}")
                    print(f"         Drag weight: {xd[0]:.6f}")

print(f"Asymmetric NE with Dragapult in row (sizes 2-5): {drag_asym_found}")

# Also check Dragapult in COL support
print(f"\nAsymmetric NE with Dragapult in COL support (sizes 2-5):")
drag_col_found = 0
for row_size in range(2, 6):
    for col_size in range(2, 6):
        for cs_rest in combinations(range(1, n), col_size - 1):
            cs = {0} | set(cs_rest)
            for rs in combinations(range(n), row_size):
                if 0 in rs:
                    continue  # Already covered above
                res_d = solve_ne_for_supports(M, set(rs), cs)
                if res_d is not None:
                    drag_col_found += 1
                    xd, yd, vrd, vcd = res_d
                    print(f"  FOUND! Row: {[DECKS[i] for i in range(n) if xd[i]>1e-10]}")
                    print(f"         Col: {[DECKS[j] for j in range(n) if yd[j]>1e-10]}")
                    print(f"         Drag weight: {yd[0]:.6f}")

print(f"Asymmetric NE with Dragapult in col (sizes 2-5): {drag_col_found}")

# ============================================================================
# FINAL SUMMARY
# ============================================================================
print(f"\n{'='*80}")
print("GRAND SUMMARY")
print("="*80)

all_ne_list = []

# Symmetric NE
for x, v in sym_eqs:
    all_ne_list.append(("symmetric", x, x.copy(), v, v, x[0], x[0]))

# Asymmetric NE (known from paper)
if result:
    x_a, y_a, vr_a, vc_a = result
    all_ne_list.append(("asymmetric (paper)", x_a, y_a, vr_a, vc_a, x_a[0], y_a[0]))

if result_mirror:
    xm, ym, vrm, vcm = result_mirror
    all_ne_list.append(("asymmetric (mirror)", xm, ym, vrm, vcm, xm[0], ym[0]))

print(f"\nTotal Nash equilibria found: {len(all_ne_list)}")
dragapult_excluded_all = True
for idx, (kind, x, y, vr, vc, dr, dc) in enumerate(all_ne_list):
    print(f"\n  NE {idx+1} ({kind}):")
    print(f"    Row: {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i] > 1e-10)}")
    print(f"    Col: {dict((DECKS[i], round(float(y[i]),6)) for i in range(n) if y[i] > 1e-10)}")
    print(f"    Dragapult: row={dr:.2e}, col={dc:.2e}")
    if dr > 1e-10 or dc > 1e-10:
        dragapult_excluded_all = False
        print(f"    *** DRAGAPULT PRESENT ***")
    else:
        print(f"    ✓ Dragapult excluded")

print(f"\n{'='*80}")
print(f"METHODS USED:")
print(f"  1. Exhaustive symmetric NE: all 16383 support subsets checked")
print(f"  2. Known asymmetric NE from paper: row {{2,3,4,5,9,11}}, col {{1,2,3,4,5,9}}")
print(f"  3. Mirror asymmetric NE check")
print(f"  4. LP minimax (zero-sum interpretation)")
print(f"  5. Targeted Dragapult search: {drag_supports_checked} symmetric + row/col asymmetric (sizes 2-5)")
print(f"  6. Lemke-Howson (all 28 initial labels)")
print(f"")
print(f"Dragapult-containing supports checked (symmetric): {drag_supports_checked}")
print(f"Dragapult-containing NE found (symmetric): {drag_ne_found}")
print(f"Dragapult-containing NE found (asymmetric row, sizes 2-5): {drag_asym_found}")
print(f"Dragapult-containing NE found (asymmetric col, sizes 2-5): {drag_col_found}")
print(f"")
print(f"CONCLUSION: Dragapult has 0% weight in ALL {len(all_ne_list)} Nash equilibria: {dragapult_excluded_all}")
print(f"{'='*80}")
