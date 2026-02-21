#!/usr/bin/env python3
"""
Nash equilibrium enumeration for 14x14 PokemonLean matchup matrix.
Focused approach: LP + symmetric support enumeration + Lemke-Howson.
"""

import numpy as np
from scipy.optimize import linprog
from itertools import combinations
import nashpy as nash
import sys

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

# Check zero-sum structure
print("Zero-sum check: M[i,j] + M[j,i] for non-diagonal pairs:")
all_1000 = True
for i in range(n):
    for j in range(i+1, n):
        s = M[i,j] + M[j,i]
        if s != 1000:
            print(f"  {DECKS[i]} vs {DECKS[j]}: {M[i,j]} + {M[j,i]} = {s}")
            all_1000 = False
if all_1000:
    print("  All pairs sum to 1000 -> zero-sum game")

# APPROACH: This is a SYMMETRIC game with A=M, B=M^T.
# The key insight: for symmetric games, symmetric NE always exist.
# For the zero-sum interpretation: if M[i,j]+M[j,i] ~ 1000, then
# the game is approximately zero-sum, and the minimax strategy is the NE.

# ============================================================================
# STEP 1: Find ONE Nash equilibrium via LP (minimax of antisymmetric part)
# ============================================================================
print("\n" + "="*80)
print("STEP 1: LP minimax solution")
print("="*80)

# For symmetric game A=M, B=M^T, a symmetric NE (x,x) satisfies:
# For all i in support(x): (Mx)[i] = v, for i not in support: (Mx)[i] <= v
# where (Mx)[i] = sum_j x_j * M[i,j]

# This is exactly the minimax LP for the row player of M!
c_obj = np.zeros(n + 1)
c_obj[n] = -1  # maximize v

A_ub = np.zeros((n, n + 1))
for j in range(n):
    for i in range(n):
        A_ub[j, i] = -M[i, j]
    A_ub[j, n] = 1
b_ub = np.zeros(n)

A_eq = np.zeros((1, n + 1))
A_eq[0, :n] = 1
b_eq = np.array([1.0])

bounds = [(0, None)] * n + [(None, None)]

res = linprog(c_obj, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
x_lp = res.x[:n]
v_lp = res.x[n]

print(f"Game value: {v_lp:.6f}")
print(f"Optimal strategy:")
for i in range(n):
    if x_lp[i] > 1e-10:
        print(f"  {DECKS[i]}: {x_lp[i]:.6f} ({x_lp[i]*100:.2f}%)")
print(f"Dragapult weight: {x_lp[0]:.10e}")

# Check all payoffs
payoffs = M @ x_lp
print(f"\nPayoffs against this strategy (value = {v_lp:.4f}):")
for i in range(n):
    tight = " [TIGHT]" if abs(payoffs[i] - v_lp) < 0.01 else ""
    active = " [ACTIVE]" if x_lp[i] > 1e-10 else ""
    print(f"  {DECKS[i]:25s}: {payoffs[i]:.4f}{tight}{active}")

# The LP support tells us which strategies are in the NE
lp_support = set(i for i in range(n) if x_lp[i] > 1e-10)
print(f"\nLP support: {[DECKS[i] for i in sorted(lp_support)]}")

# Tight constraints (these are the strategies the OPPONENT could use)
tight_set = set(i for i in range(n) if abs(payoffs[i] - v_lp) < 0.1)
print(f"Tight constraints: {[DECKS[i] for i in sorted(tight_set)]}")

# ============================================================================
# STEP 2: Enumerate symmetric NE with all support subsets
# ============================================================================
print("\n" + "="*80)
print("STEP 2: Enumerate ALL symmetric Nash equilibria")
print("="*80)

def find_symmetric_ne(M, support):
    n = M.shape[0]
    s = sorted(support)
    k = len(s)
    if k == 0:
        return None
    
    # Indifference: M_sub @ x_sub = v * ones, sum x_sub = 1
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
    
    if np.any(x_s < -1e-10):
        return None
    x_s = np.maximum(x_s, 0)
    
    x = np.zeros(n)
    for idx, i in enumerate(s):
        x[i] = x_s[idx]
    
    if abs(np.sum(x) - 1) > 1e-8:
        return None
    
    # Check out-of-support: M[i,:] @ x <= v for i not in support
    row_payoffs = M @ x
    for i in range(n):
        if i in support:
            if abs(row_payoffs[i] - v) > 1e-6:
                return None
        else:
            if row_payoffs[i] > v + 1e-6:
                return None
    
    return x, v

sym_eqs = []
for size in range(1, n + 1):
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
                support_names = [DECKS[i] for i in range(n) if x[i] > 1e-10]
                print(f"\n  Symmetric NE #{len(sym_eqs)} (support size {size}):")
                print(f"    Support: {support_names}")
                print(f"    Strategy: {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i] > 1e-10)}")
                print(f"    Value: {v:.4f}")
                print(f"    Dragapult weight: {x[0]:.10f}")

print(f"\nTotal symmetric NE found: {len(sym_eqs)}")

# ============================================================================
# STEP 3: Lemke-Howson for asymmetric NE
# ============================================================================
print("\n" + "="*80)
print("STEP 3: Lemke-Howson enumeration")
print("="*80)

A_game = M
B_game = M.T
game = nash.Game(A_game, B_game)

lh_all = []
for label in range(2 * n):
    try:
        row, col = game.lemke_howson(initial_label=label)
        if np.any(row < -1e-10) or np.any(col < -1e-10):
            continue
        if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
            continue
        is_dup = False
        for r2, c2 in lh_all:
            if np.allclose(row, r2, atol=1e-8) and np.allclose(col, c2, atol=1e-8):
                is_dup = True
                break
        if not is_dup:
            lh_all.append((row.copy(), col.copy()))
    except Exception as e:
        pass

print(f"Lemke-Howson found {len(lh_all)} unique equilibria")
for idx, (row, col) in enumerate(lh_all):
    rs = [DECKS[i] for i in range(n) if row[i] > 1e-10]
    cs = [DECKS[i] for i in range(n) if col[i] > 1e-10]
    print(f"\n  LH-EQ {idx+1}:")
    print(f"    Row: {dict((DECKS[i], round(float(row[i]),6)) for i in range(n) if row[i] > 1e-10)}")
    print(f"    Col: {dict((DECKS[i], round(float(col[i]),6)) for i in range(n) if col[i] > 1e-10)}")
    print(f"    Dragapult: row={row[0]:.10f}, col={col[0]:.10f}")
    print(f"    Symmetric? {np.allclose(row, col, atol=1e-8)}")

# ============================================================================
# STEP 4: Check for asymmetric NE by searching supports from LH + LP info
# ============================================================================
print("\n" + "="*80)
print("STEP 4: Targeted asymmetric NE search")
print("="*80)

def find_asymmetric_ne(M, row_support, col_support):
    n = M.shape[0]
    rs = sorted(row_support)
    cs = sorted(col_support)
    kr = len(rs)
    kc = len(cs)
    
    if kr != kc:
        return None  # For square system requirement
    
    # Solve for y from row indifference: M[rs, cs] @ y_sub = v_r * ones, sum y = 1
    A1 = np.zeros((kr + 1, kc + 1))
    b1 = np.zeros(kr + 1)
    for ri, i in enumerate(rs):
        for ci, j in enumerate(cs):
            A1[ri, ci] = M[i, j]
        A1[ri, kc] = -1
    A1[kr, :kc] = 1
    b1[kr] = 1
    
    try:
        sol1 = np.linalg.solve(A1, b1)
    except:
        return None
    
    y_s = sol1[:kc]
    v_r = sol1[kc]
    if np.any(y_s < -1e-10):
        return None
    y_s = np.maximum(y_s, 0)
    
    # Solve for x from col indifference: M[cs, rs] @ x_sub = v_c * ones, sum x = 1
    # Col payoff for pure j = sum_i x_i * M[j,i] (since B=M^T)
    A2 = np.zeros((kc + 1, kr + 1))
    b2 = np.zeros(kc + 1)
    for ri, j in enumerate(cs):
        for ci, i in enumerate(rs):
            A2[ri, ci] = M[j, i]
        A2[ri, kr] = -1
    A2[kc, :kr] = 1
    b2[kc] = 1
    
    try:
        sol2 = np.linalg.solve(A2, b2)
    except:
        return None
    
    x_s = sol2[:kr]
    v_c = sol2[kr]
    if np.any(x_s < -1e-10):
        return None
    x_s = np.maximum(x_s, 0)
    
    x = np.zeros(n)
    y = np.zeros(n)
    for idx, i in enumerate(rs): x[i] = x_s[idx]
    for idx, j in enumerate(cs): y[j] = y_s[idx]
    
    if abs(np.sum(x)-1) > 1e-8 or abs(np.sum(y)-1) > 1e-8:
        return None
    
    # Verify NE conditions
    My = M @ y  # row payoffs
    for i in range(n):
        if i in row_support:
            if abs(My[i] - v_r) > 1e-6: return None
        else:
            if My[i] > v_r + 1e-6: return None
    
    Mx_col = M @ x  # col payoffs (B=M^T, col payoff for j = sum_i x_i M[j,i])
    for j in range(n):
        if j in col_support:
            if abs(Mx_col[j] - v_c) > 1e-6: return None
        else:
            if Mx_col[j] > v_c + 1e-6: return None
    
    return x, y, v_r, v_c

# Search asymmetric NE with support sizes 2-7
asym_eqs = []
for size in range(2, 8):
    count = 0
    for rs in combinations(range(n), size):
        for cs in combinations(range(n), size):
            if set(rs) == set(cs):
                continue
            result = find_asymmetric_ne(M, set(rs), set(cs))
            if result is not None:
                x, y, vr, vc = result
                is_dup = False
                for ex, ey, _, _ in asym_eqs:
                    if np.allclose(x, ex, atol=1e-8) and np.allclose(y, ey, atol=1e-8):
                        is_dup = True
                        break
                # Also check against symmetric
                for ex, _ in sym_eqs:
                    if np.allclose(x, ex, atol=1e-8) and np.allclose(y, ex, atol=1e-8):
                        is_dup = True
                        break
                if not is_dup:
                    asym_eqs.append(result)
                    count += 1
                    print(f"  Asymmetric NE #{len(asym_eqs)} (size {size}):")
                    print(f"    Row: {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i]>1e-10)}")
                    print(f"    Col: {dict((DECKS[j], round(float(y[j]),6)) for j in range(n) if y[j]>1e-10)}")
                    print(f"    Dragapult: row={x[0]:.8f}, col={y[0]:.8f}")
    if size <= 5:
        print(f"  Checked all pairs of size {size}: {count} new asymmetric NE")
    sys.stdout.flush()

print(f"\nTotal asymmetric NE found: {len(asym_eqs)}")

# ============================================================================
# GRAND SUMMARY
# ============================================================================
print("\n" + "="*80)
print("GRAND SUMMARY: ALL NASH EQUILIBRIA")
print("="*80)

all_ne = []
for x, v in sym_eqs:
    all_ne.append((x, x.copy(), "symmetric"))
for x, y, vr, vc in asym_eqs:
    all_ne.append((x, y, "asymmetric"))
# Add LH results not already found
for row, col in lh_all:
    is_dup = False
    for ex, ey, _ in all_ne:
        if np.allclose(row, ex, atol=1e-6) and np.allclose(col, ey, atol=1e-6):
            is_dup = True
            break
    if not is_dup:
        all_ne.append((row, col, "lemke-howson"))
        print(f"  Additional from LH not found by other methods!")

print(f"\nTotal unique Nash equilibria: {len(all_ne)}")

dragapult_zero = True
for idx, (x, y, kind) in enumerate(all_ne):
    d_r = x[0]
    d_c = y[0]
    rs = [DECKS[i] for i in range(n) if x[i] > 1e-10]
    cs = [DECKS[i] for i in range(n) if y[i] > 1e-10]
    print(f"\n  NE {idx+1} ({kind}):")
    print(f"    Row ({len(rs)}): {dict((DECKS[i], round(float(x[i]),6)) for i in range(n) if x[i] > 1e-10)}")
    print(f"    Col ({len(cs)}): {dict((DECKS[i], round(float(y[i]),6)) for i in range(n) if y[i] > 1e-10)}")
    print(f"    Dragapult: row={d_r:.10f}, col={d_c:.10f}")
    if d_r > 1e-10 or d_c > 1e-10:
        dragapult_zero = False
        print(f"    *** DRAGAPULT IS PLAYED ***")
    else:
        print(f"    ✓ Dragapult excluded")

print(f"\n{'='*80}")
print(f"FINAL ANSWER: Dragapult (index 0) has 0% weight in ALL equilibria: {dragapult_zero}")
print(f"Number of equilibria found: {len(all_ne)}")
print(f"{'='*80}")
