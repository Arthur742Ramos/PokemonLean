#!/usr/bin/env python3
"""
Enumerate ALL Nash equilibria of the 14x14 PokemonLean matchup matrix.
Efficient approach: use nashpy + LP + targeted support enumeration.
"""

import numpy as np
import nashpy as nash
from scipy.optimize import linprog
from itertools import combinations

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

# The game: Row player payoff A = M, Col player payoff B = M^T
# (symmetric bimatrix game: both players choose a deck)
A = M
B = M.T

print("="*80)
print("STEP 1: nashpy support_enumeration")
print("="*80)

game = nash.Game(A, B)

support_eqs = []
for eq in game.support_enumeration():
    row, col = eq
    if np.any(row < -1e-10) or np.any(col < -1e-10):
        continue
    if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
        continue
    support_eqs.append((row.copy(), col.copy()))

print(f"Found {len(support_eqs)} equilibria")
for idx, (row, col) in enumerate(support_eqs):
    rs = [DECKS[i] for i in range(n) if row[i] > 1e-10]
    cs = [DECKS[i] for i in range(n) if col[i] > 1e-10]
    print(f"\n  EQ {idx+1}:")
    print(f"    Row: {dict((DECKS[i], round(float(row[i]),6)) for i in range(n) if row[i] > 1e-10)}")
    print(f"    Col: {dict((DECKS[i], round(float(col[i]),6)) for i in range(n) if col[i] > 1e-10)}")
    print(f"    Dragapult: row={row[0]:.10f}, col={col[0]:.10f}")
    val = row @ A @ col
    print(f"    Value: {val:.4f}")

print("\n" + "="*80)
print("STEP 2: Lemke-Howson (all 14 initial labels)")
print("="*80)

lh_eqs = []
for label in range(n):
    try:
        row, col = game.lemke_howson(initial_label=label)
        if np.any(row < -1e-10) or np.any(col < -1e-10):
            continue
        if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
            continue
        # Check duplicate
        is_dup = False
        for r2, c2 in lh_eqs:
            if np.allclose(row, r2, atol=1e-8) and np.allclose(col, c2, atol=1e-8):
                is_dup = True
                break
        if not is_dup:
            lh_eqs.append((row.copy(), col.copy()))
    except Exception as e:
        print(f"  Label {label}: {e}")

print(f"Found {len(lh_eqs)} unique equilibria")
for idx, (row, col) in enumerate(lh_eqs):
    print(f"\n  EQ {idx+1}:")
    print(f"    Row: {dict((DECKS[i], round(float(row[i]),6)) for i in range(n) if row[i] > 1e-10)}")
    print(f"    Col: {dict((DECKS[i], round(float(col[i]),6)) for i in range(n) if col[i] > 1e-10)}")
    print(f"    Dragapult: row={row[0]:.10f}, col={col[0]:.10f}")

print("\n" + "="*80)
print("STEP 3: LP minimax for zero-sum interpretation")
print("="*80)
# Even though M+M^T != 1000 exactly (ties), let's also solve as if it were zero-sum
# to find the minimax strategy

# Actually, let's check what the actual game structure is
print("\nChecking M[i,j] + M[j,i] for all pairs:")
non_1000 = []
for i in range(n):
    for j in range(i+1, n):
        s = M[i,j] + M[j,i]
        if s != 1000:
            non_1000.append((i,j,s))
if non_1000:
    print(f"  {len(non_1000)} pairs where M[i,j]+M[j,i] != 1000:")
    for i,j,s in non_1000:
        print(f"    ({DECKS[i]} vs {DECKS[j]}): {M[i,j]} + {M[j,i]} = {s}")
else:
    print("  All pairs sum to 1000 -> perfect zero-sum game")

# For the zero-sum version, antisymmetrize: C[i,j] = (M[i,j] - M[j,i]) / 2
# Nash eq of this zero-sum game
C = (M - M.T) / 2  # antisymmetric payoff matrix
print(f"\nAntisymmetric payoff matrix C = (M-M^T)/2:")
print(f"  Verification: C + C^T = 0? max|C+C^T| = {np.max(np.abs(C + C.T))}")

# Solve zero-sum game via LP
c_obj = np.zeros(n + 1)
c_obj[n] = -1  # maximize v

A_ub = np.zeros((n, n + 1))
for j in range(n):
    for i in range(n):
        A_ub[j, i] = -C[i, j]
    A_ub[j, n] = 1
b_ub = np.zeros(n)

A_eq = np.zeros((1, n + 1))
A_eq[0, :n] = 1
b_eq = np.array([1.0])

bounds = [(0, None)] * n + [(None, None)]

result = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
if result.success:
    x_zs = result.x[:n]
    v_zs = result.x[n]
    print(f"\nZero-sum game value: {v_zs:.6f}")
    print(f"Minimax strategy:")
    for i in range(n):
        if x_zs[i] > 1e-10:
            print(f"  {DECKS[i]}: {x_zs[i]:.6f} ({x_zs[i]*100:.2f}%)")
    print(f"  Dragapult: {x_zs[0]:.10f}")
    
    # Check which constraints are tight (active support of opponent)
    payoffs = C.T @ x_zs  # payoff for each pure col strategy against x
    print(f"\n  Payoffs against minimax (should be <= {v_zs:.6f}):")
    for j in range(n):
        flag = " *TIGHT*" if abs(C.T[j] @ x_zs - v_zs) < 1e-8 else ""
        # Actually: sum_i x_i C[i,j] for each j
        pj = sum(x_zs[i] * C[i,j] for i in range(n))
        flag2 = " TIGHT" if abs(pj - v_zs) < 1e-6 else ""
        if abs(pj - v_zs) < 1e-6 or x_zs[j] > 1e-10:
            print(f"    {DECKS[j]}: {pj:.6f}{flag2}")

print("\n" + "="*80)
print("STEP 4: Solve the actual symmetric bimatrix game via LP best-response")
print("="*80)

# For the actual game (A=M, B=M^T), at a symmetric NE (x=y):
# For all i in support: sum_j x_j * M[i,j] = v (row indifference)
# For all i not in support: sum_j x_j * M[i,j] <= v
# AND
# For all j in support: sum_i x_i * M^T[j,i] = w  (col indifference)
# i.e., sum_i x_i * M[i,j] = w
# For all j not in support: sum_i x_i * M[i,j] <= w
# At symmetric NE (x=y), these two conditions give us v and w

# Let's find symmetric NE by checking all subsets
# For symmetric NE with support S: both indifference conditions must hold with same x
# Row: sum_j x_j * M[i,j] = v for i in S
# Col: sum_i x_i * M[i,j] = w for j in S
# With the SAME x.

# This is quite restrictive. Let's enumerate supports up to size 8 or so.
print("\nSearching symmetric Nash equilibria (x = y)...")

def find_symmetric_ne(M, support):
    """Find symmetric NE with given support."""
    n = M.shape[0]
    s = sorted(support)
    k = len(s)
    if k == 0:
        return None
    
    # Row indifference: sum_{j in s} x_j * M[i,j] = v for i in s, plus sum x_j = 1
    # This is k+1 equations in k+1 unknowns (x_{s[0]}, ..., x_{s[k-1]}, v)
    A_sys = np.zeros((k + 1, k + 1))
    b_sys = np.zeros(k + 1)
    
    for row_idx, i in enumerate(s):
        for col_idx, j in enumerate(s):
            A_sys[row_idx, col_idx] = M[i, j]
        A_sys[row_idx, k] = -1
    A_sys[k, :k] = 1
    b_sys[k] = 1
    
    try:
        sol = np.linalg.solve(A_sys, b_sys)
    except np.linalg.LinAlgError:
        return None
    
    x_s = sol[:k]
    v = sol[k]
    
    if np.any(x_s < -1e-10):
        return None
    x_s = np.maximum(x_s, 0)
    
    # Build full strategy
    x = np.zeros(n)
    for idx, i in enumerate(s):
        x[i] = x_s[idx]
    
    # Normalize just in case
    if abs(np.sum(x) - 1) > 1e-8:
        return None
    
    # Check row indifference for out-of-support strategies
    row_payoffs = M @ x  # row_payoffs[i] = sum_j x_j * M[i,j]
    for i in range(n):
        if i in support:
            if abs(row_payoffs[i] - v) > 1e-6:
                return None
        else:
            if row_payoffs[i] > v + 1e-6:
                return None
    
    # Check column indifference: sum_i x_i * M[i,j] for j
    # Col payoff when col plays j = sum_i x_i * B[i,j] = sum_i x_i * M[j,i] = (M @ x)[j]
    # Wait, B[i,j] = M^T[i,j] = M[j,i]
    # So col payoff for pure j = sum_i x_i * M[j,i] = row_payoffs[j] (same!)
    # That means for a symmetric NE, the row and column indifference conditions are identical!
    # So we only need to check row indifference. 
    
    return x, v

sym_eqs = []
for size in range(1, n + 1):
    found_this_size = 0
    for support in combinations(range(n), size):
        result = find_symmetric_ne(M, set(support))
        if result is not None:
            x, v = result
            is_dup = False
            for ex, _ in sym_eqs:
                if np.allclose(x, ex, atol=1e-8):
                    is_dup = True
                    break
            if not is_dup:
                sym_eqs.append((x, v))
                found_this_size += 1
                support_names = [DECKS[i] for i in range(n) if x[i] > 1e-10]
                print(f"  Support size {size}: {support_names}")
                print(f"    Strategy: {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i] > 1e-10)}")
                print(f"    Value: {v:.4f}")
                print(f"    Dragapult weight: {x[0]:.10f}")
    if found_this_size > 0:
        print(f"  -> {found_this_size} equilibria with support size {size}")

print(f"\nTotal symmetric Nash equilibria: {len(sym_eqs)}")

# ============================================================================
# Now search for asymmetric NE (different row and col strategies)
# For the game (A=M, B=M^T):
# Row player indifference: for i in row_support, sum_j y_j * M[i,j] = v_r
# Col player indifference: for j in col_support, sum_i x_i * M^T[j,i] = sum_i x_i * M[i,j] ... 
# Wait. B = M^T. Col payoff for pure j when row mixes x: sum_i x_i * B[i,j] = sum_i x_i * M[j,i]
# At NE, for j in col_support: sum_i x_i * M[j,i] = v_c, and for j not in col_support: sum_i x_i * M[j,i] <= v_c
# So col indifference gives: (M @ x)[j] = v_c for j in col_support

print("\n" + "="*80)
print("STEP 5: Search asymmetric NE (different row/col supports)")
print("="*80)

def find_asymmetric_ne(M, row_support, col_support):
    """Find NE with given row and column supports for game (A=M, B=M^T)."""
    n = M.shape[0]
    rs = sorted(row_support)
    cs = sorted(col_support)
    kr = len(rs)
    kc = len(cs)
    
    # Solve for y (col strategy) from row player indifference:
    # sum_{j in cs} y_j * M[i,j] = v_r for i in rs
    # sum y_j = 1
    if kc + 1 != kr + 1:
        # Need kc = kr for square system. For non-square, use lstsq
        pass
    
    # System for y: (kr equations from indifference + 1 from normalization) in (kc + 1) unknowns
    A1 = np.zeros((kr + 1, kc + 1))
    b1 = np.zeros(kr + 1)
    for row_idx, i in enumerate(rs):
        for col_idx, j in enumerate(cs):
            A1[row_idx, col_idx] = M[i, j]
        A1[row_idx, kc] = -1
    A1[kr, :kc] = 1
    b1[kr] = 1
    
    if kr + 1 == kc + 1:
        try:
            sol_y = np.linalg.solve(A1, b1)
        except np.linalg.LinAlgError:
            return None
    else:
        sol_y, res, _, _ = np.linalg.lstsq(A1, b1, rcond=None)
        # Check residual
        if np.max(np.abs(A1 @ sol_y - b1)) > 1e-8:
            return None
    
    y_s = sol_y[:kc]
    v_r = sol_y[kc]
    if np.any(y_s < -1e-10):
        return None
    y_s = np.maximum(y_s, 0)
    
    # System for x: col player indifference
    # sum_{i in rs} x_i * M[i,j] = v_c for j in cs (col payoff = sum_i x_i * M[j,i]... 
    # Wait. Col payoff for pure j = sum_i x_i * M[j,i]. This involves M[j,i], not M[i,j].
    # So: for j in cs: sum_{i in rs} x_i * M[j, i] = v_c
    # sum x_i = 1
    
    A2 = np.zeros((kc + 1, kr + 1))
    b2 = np.zeros(kc + 1)
    for row_idx, j in enumerate(cs):
        for col_idx, i in enumerate(rs):
            A2[row_idx, col_idx] = M[j, i]  # M[j,i] = B[i,j] = M^T[i,j]
        A2[row_idx, kr] = -1
    A2[kc, :kr] = 1
    b2[kc] = 1
    
    if kc + 1 == kr + 1:
        try:
            sol_x = np.linalg.solve(A2, b2)
        except np.linalg.LinAlgError:
            return None
    else:
        sol_x, res, _, _ = np.linalg.lstsq(A2, b2, rcond=None)
        if np.max(np.abs(A2 @ sol_x - b2)) > 1e-8:
            return None
    
    x_s = sol_x[:kr]
    v_c = sol_x[kr]
    if np.any(x_s < -1e-10):
        return None
    x_s = np.maximum(x_s, 0)
    
    # Build full strategies
    x = np.zeros(n)
    for idx, i in enumerate(rs):
        x[i] = x_s[idx]
    y = np.zeros(n)
    for idx, j in enumerate(cs):
        y[j] = y_s[idx]
    
    if abs(np.sum(x) - 1) > 1e-8 or abs(np.sum(y) - 1) > 1e-8:
        return None
    
    # Verify all NE conditions
    # Row: for i in rs: (M @ y)[i] = v_r. For i not in rs: (M @ y)[i] <= v_r
    My = M @ y
    for i in range(n):
        if i in row_support:
            if abs(My[i] - v_r) > 1e-6:
                return None
        else:
            if My[i] > v_r + 1e-6:
                return None
    
    # Col: for j in cs: (M @ x)[j] = v_c (this is sum_i x_i M[j,i]).
    # For j not in cs: (M @ x)[j] <= v_c
    Mx = M @ x
    for j in range(n):
        if j in col_support:
            if abs(Mx[j] - v_c) > 1e-6:
                return None
        else:
            if Mx[j] > v_c + 1e-6:
                return None
    
    return x, y, v_r, v_c

all_ne = []

# Add symmetric NE first
for x, v in sym_eqs:
    all_ne.append((x, x.copy(), v, v))

# Add nashpy results
for row, col in support_eqs:
    is_dup = False
    for ex, ey, _, _ in all_ne:
        if np.allclose(row, ex, atol=1e-8) and np.allclose(col, ey, atol=1e-8):
            is_dup = True
            break
    if not is_dup:
        vr = row @ M @ col
        # col value
        vc = row @ M.T @ col  # Hmm, this isn't right either
        all_ne.append((row, col, vr, vc))
        print(f"  Additional from nashpy: Row support {[DECKS[i] for i in range(n) if row[i]>1e-10]}")

# Add Lemke-Howson results
for row, col in lh_eqs:
    is_dup = False
    for ex, ey, _, _ in all_ne:
        if np.allclose(row, ex, atol=1e-8) and np.allclose(col, ey, atol=1e-8):
            is_dup = True
            break
    if not is_dup:
        vr = row @ M @ col
        vc = 0
        all_ne.append((row, col, vr, vc))
        print(f"  Additional from LH: Row support {[DECKS[i] for i in range(n) if row[i]>1e-10]}")

# Search asymmetric NE with equal-sized supports (most common case)
print("\nSearching asymmetric NE with same-size supports...")
for size in range(2, 8):
    found = 0
    for rs in combinations(range(n), size):
        for cs in combinations(range(n), size):
            if set(rs) == set(cs):
                continue  # Already covered by symmetric search
            result = find_asymmetric_ne(M, set(rs), set(cs))
            if result is not None:
                x, y, vr, vc = result
                is_dup = False
                for ex, ey, _, _ in all_ne:
                    if np.allclose(x, ex, atol=1e-8) and np.allclose(y, ey, atol=1e-8):
                        is_dup = True
                        break
                if not is_dup:
                    all_ne.append(result)
                    found += 1
                    print(f"  Size {size}: Row {[DECKS[i] for i in range(n) if x[i]>1e-10]}")
                    print(f"            Col {[DECKS[j] for j in range(n) if y[j]>1e-10]}")
                    print(f"    Dragapult: row={x[0]:.8f}, col={y[0]:.8f}")
    if found > 0:
        print(f"  -> {found} new asymmetric equilibria with support size {size}")

# ============================================================================
# FINAL SUMMARY
# ============================================================================
print("\n" + "="*80)
print("FINAL SUMMARY")  
print("="*80)

print(f"\nTotal Nash equilibria found: {len(all_ne)}")

dragapult_zero_all = True
for idx, (x, y, vr, vc) in enumerate(all_ne):
    rs = [DECKS[i] for i in range(n) if x[i] > 1e-10]
    cs = [DECKS[i] for i in range(n) if y[i] > 1e-10]
    d_row = x[0]
    d_col = y[0]
    
    print(f"\nEquilibrium {idx+1}:")
    print(f"  Row support ({len(rs)}): {rs}")
    print(f"  Col support ({len(cs)}): {cs}")
    print(f"  Row: {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i] > 1e-10)}")
    print(f"  Col: {dict((DECKS[i], round(float(y[i]),6)) for i in range(n) if y[i] > 1e-10)}")
    print(f"  Dragapult row: {d_row:.10f}, col: {d_col:.10f}")
    
    if d_row > 1e-10 or d_col > 1e-10:
        dragapult_zero_all = False
        print(f"  *** DRAGAPULT HAS NON-ZERO WEIGHT ***")

print(f"\n{'='*80}")
print(f"ANSWER: Dragapult has 0% weight in ALL Nash equilibria: {dragapult_zero_all}")
print(f"{'='*80}")
