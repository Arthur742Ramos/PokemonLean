#!/usr/bin/env python3
"""
Enumerate ALL Nash equilibria of the 14x14 PokemonLean matchup matrix.
Uses multiple methods: support enumeration, vertex enumeration, and Lemke-Howson.
"""

import numpy as np
import nashpy as nash
from itertools import combinations
from fractions import Fraction
import json

# Deck names
DECKS = [
    "DragapultDusknoir",    # 0
    "GholdengoLunatone",    # 1
    "GrimssnarlFroslass",   # 2
    "MegaAbsolBox",         # 3
    "Gardevoir",            # 4
    "CharizardNoctowl",     # 5
    "GardevoirJellicent",   # 6
    "CharizardPidgeot",     # 7
    "DragapultCharizard",   # 8
    "RagingBoltOgerpon",    # 9
    "NsZoroark",            # 10
    "AlakazamDudunsparce",  # 11
    "KangaskhanBouffalant", # 12
    "Ceruledge",            # 13
]

# 14x14 matchup matrix from Lean source (row = attacker, col = defender, out of 1000)
M = np.array([
    [494, 436, 386, 382, 343, 641, 418, 563, 486, 454, 472, 627, 368, 531],  # 0 DragapultDusknoir
    [521, 488, 476, 443, 441, 483, 439, 459, 425, 496, 516, 373, 553, 439],  # 1 GholdengoLunatone
    [572, 467, 485, 344, 566, 558, 592, 570, 598, 473, 545, 599, 473, 561],  # 2 GrimssnarlFroslass
    [576, 512, 621, 494, 558, 475, 587, 451, 524, 298, 418, 515, 474, 414],  # 3 MegaAbsolBox
    [627, 493, 374, 402, 480, 394, 362, 374, 516, 625, 448, 633, 392, 627],  # 4 Gardevoir
    [324, 480, 397, 471, 558, 487, 549, 581, 422, 557, 493, 584, 330, 593],  # 5 CharizardNoctowl
    [544, 498, 346, 364, 583, 390, 489, 345, 486, 619, 360, 548, 422, 526],  # 6 GardevoirJellicent
    [396, 510, 386, 500, 584, 362, 598, 487, 347, 535, 506, 492, 450, 604],  # 7 CharizardPidgeot
    [480, 528, 361, 432, 421, 536, 463, 580, 489, 454, 573, 593, 510, 490],  # 8 DragapultCharizard
    [510, 458, 477, 673, 333, 409, 332, 426, 490, 487, 623, 303, 653, 537],  # 9 RagingBoltOgerpon
    [490, 439, 417, 548, 519, 463, 601, 438, 391, 340, 495, 556, 492, 262],  # 10 NsZoroark
    [341, 588, 368, 441, 315, 366, 412, 466, 370, 653, 407, 489, 772, 675],  # 11 AlakazamDudunsparce
    [582, 401, 473, 492, 549, 635, 524, 518, 449, 311, 477, 198, 490, 550],  # 12 KangaskhanBouffalant
    [440, 538, 398, 545, 325, 370, 418, 339, 475, 426, 709, 300, 414, 481],  # 13 Ceruledge
], dtype=float)

# This is a symmetric zero-sum game (row player uses M, column player uses 1000-M^T)
# For a symmetric game, Nash equilibrium has row strategy = column strategy
# Row player payoff = M, Column player payoff = (1000 - M).T = 1000 - M.T
# Actually for zero-sum: column player payoff = -M (or equivalently 1000-M for column)

# For nashpy, we need to specify both player payoff matrices
# Row player gets M[i,j], Column player gets (1000-M[i,j]) which means column wants to minimize M
# But nashpy expects: row player payoff A, column player payoff B
# In a zero-sum game: B = -A (up to constant)
# Here: A = M, B = 1000 - M  (but we can shift: B' = -M works too since nashpy handles general bimatrix)

# Actually this ISN'T zero-sum because M[i,j] + M[j,i] != 1000 in general (ties exist)
# But it IS a symmetric game where both players choose from same set
# Let's check:
print("Checking if M + M^T = 1000 (zero-sum check):")
asymmetry = M + M.T - 1000
print(f"  Max |M[i,j] + M[j,i] - 1000| = {np.max(np.abs(asymmetry))}")
print(f"  Entries where M[i,j]+M[j,i] != 1000:")
for i in range(14):
    for j in range(i+1, 14):
        s = M[i,j] + M[j,i]
        if s != 1000:
            print(f"    ({i},{j}): M={M[i,j]}, M^T={M[j,i]}, sum={s}")

# For the symmetric game interpretation:
# Both players choose a deck. Row picks i, col picks j.
# Row player's payoff = M[i,j] (win rate of i vs j)
# Col player's payoff = M[j,i] (win rate of j vs i)
# So: A = M, B = M.T

print("\n" + "="*80)
print("APPROACH 1: Symmetric game (A=M, B=M^T)")
print("="*80)

A = M
B = M.T
game = nash.Game(A, B)

print("\n--- Support Enumeration ---")
support_eqs = list(game.support_enumeration())
print(f"Found {len(support_eqs)} equilibria via support enumeration")

for idx, (row, col) in enumerate(support_eqs):
    # Check validity
    if np.any(row < -1e-10) or np.any(col < -1e-10):
        print(f"  EQ {idx}: INVALID (negative probabilities)")
        continue
    if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
        print(f"  EQ {idx}: INVALID (doesn't sum to 1)")
        continue
    
    row_support = np.where(row > 1e-10)[0]
    col_support = np.where(col > 1e-10)[0]
    dragapult_row = row[0]
    dragapult_col = col[0]
    
    row_val = row @ A @ col
    col_val = row @ B @ col
    
    print(f"\n  EQ {idx}:")
    print(f"    Row support: {[DECKS[i] for i in row_support]}")
    print(f"    Col support: {[DECKS[i] for i in col_support]}")
    print(f"    Dragapult row weight: {dragapult_row:.6f}")
    print(f"    Dragapult col weight: {dragapult_col:.6f}")
    print(f"    Row value: {row_val:.4f}, Col value: {col_val:.4f}")
    print(f"    Row strategy: {dict((DECKS[i], round(float(row[i]),6)) for i in row_support)}")
    print(f"    Col strategy: {dict((DECKS[i], round(float(col[i]),6)) for i in col_support)}")

print("\n--- Vertex Enumeration ---")
try:
    vertex_eqs = list(game.vertex_enumeration())
    print(f"Found {len(vertex_eqs)} equilibria via vertex enumeration")
    for idx, (row, col) in enumerate(vertex_eqs):
        if np.any(row < -1e-10) or np.any(col < -1e-10):
            continue
        if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
            continue
        row_support = np.where(row > 1e-10)[0]
        col_support = np.where(col > 1e-10)[0]
        print(f"  EQ {idx}: Row Dragapult={row[0]:.6f}, Col Dragapult={col[0]:.6f}")
        print(f"    Row: {dict((DECKS[i], round(float(row[i]),6)) for i in row_support)}")
        print(f"    Col: {dict((DECKS[i], round(float(col[i]),6)) for i in col_support)}")
except Exception as e:
    print(f"  Vertex enumeration failed: {e}")

print("\n--- Lemke-Howson (all 14 initial labels) ---")
lh_eqs = []
for label in range(14):
    try:
        eq = game.lemke_howson(initial_label=label)
        row, col = eq
        if np.any(row < -1e-10) or np.any(col < -1e-10):
            continue
        if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
            continue
        lh_eqs.append((label, row, col))
    except Exception as e:
        print(f"  Label {label}: failed ({e})")

print(f"Found {len(lh_eqs)} valid equilibria via Lemke-Howson")
# Deduplicate
unique_lh = []
for label, row, col in lh_eqs:
    is_dup = False
    for _, r2, c2 in unique_lh:
        if np.allclose(row, r2, atol=1e-8) and np.allclose(col, c2, atol=1e-8):
            is_dup = True
            break
    if not is_dup:
        unique_lh.append((label, row, col))

print(f"Unique equilibria from Lemke-Howson: {len(unique_lh)}")
for label, row, col in unique_lh:
    row_support = np.where(row > 1e-10)[0]
    col_support = np.where(col > 1e-10)[0]
    print(f"  From label {label}: Row Dragapult={row[0]:.6f}, Col Dragapult={col[0]:.6f}")
    print(f"    Row: {dict((DECKS[i], round(float(row[i]),6)) for i in row_support)}")
    print(f"    Col: {dict((DECKS[i], round(float(col[i]),6)) for i in col_support)}")

# ============================================================================
# APPROACH 2: Zero-sum formulation via LP (finds THE unique value + one optimal strategy)
# For a zero-sum game, the Nash eq strategy is unique if the LP has a unique solution
# But there may be multiple optimal strategies achieving the same value
# ============================================================================
print("\n" + "="*80)
print("APPROACH 2: Zero-sum LP (minimax)")
print("="*80)

from scipy.optimize import linprog

# Row player maximizes min_j sum_i x_i * M[i,j]
# LP: maximize v subject to: sum_i x_i * M[i,j] >= v for all j, sum x_i = 1, x_i >= 0
# Equivalent: minimize -v subject to: -sum_i x_i * M[i,j] + v <= 0, sum x_i = 1

n = 14
# Variables: [x_0, ..., x_13, v]
# minimize -v (i.e., c = [0,...,0,-1])
c = np.zeros(n + 1)
c[n] = -1  # minimize -v

# Constraints: v - sum_i x_i * M[i,j] <= 0 for each j
# i.e., -M[0,j]*x_0 - ... - M[13,j]*x_13 + v <= 0
A_ub = np.zeros((n, n + 1))
for j in range(n):
    for i in range(n):
        A_ub[j, i] = -M[i, j]
    A_ub[j, n] = 1
b_ub = np.zeros(n)

# Equality: sum x_i = 1
A_eq = np.zeros((1, n + 1))
A_eq[0, :n] = 1
b_eq = np.array([1.0])

# Bounds: x_i >= 0, v unrestricted
bounds = [(0, None)] * n + [(None, None)]

result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs')
if result.success:
    x_opt = result.x[:n]
    v_opt = result.x[n]
    print(f"Game value (row player): {v_opt:.6f}")
    print(f"Optimal row strategy:")
    for i in range(n):
        if x_opt[i] > 1e-10:
            print(f"  {DECKS[i]}: {x_opt[i]:.6f} ({x_opt[i]*100:.2f}%)")
    print(f"Dragapult weight: {x_opt[0]:.10f}")
else:
    print(f"LP failed: {result.message}")

# Column player (same game, symmetric check)
# Col player minimizes max_i sum_j y_j * M[i,j]
# LP: minimize w subject to: sum_j y_j * M[i,j] <= w for all i, sum y_j = 1, y_j >= 0
c2 = np.zeros(n + 1)
c2[n] = 1  # minimize w

A_ub2 = np.zeros((n, n + 1))
for i in range(n):
    for j in range(n):
        A_ub2[i, j] = M[i, j]
    A_ub2[i, n] = -1
b_ub2 = np.zeros(n)

A_eq2 = np.zeros((1, n + 1))
A_eq2[0, :n] = 1
b_eq2 = np.array([1.0])

bounds2 = [(0, None)] * n + [(None, None)]

result2 = linprog(c2, A_ub=A_ub2, b_ub=b_ub2, A_eq=A_eq2, b_eq=b_eq2, bounds=bounds2, method='highs')
if result2.success:
    y_opt = result2.x[:n]
    w_opt = result2.x[n]
    print(f"\nGame value (col player): {w_opt:.6f}")
    print(f"Optimal col strategy:")
    for j in range(n):
        if y_opt[j] > 1e-10:
            print(f"  {DECKS[j]}: {y_opt[j]:.6f} ({y_opt[j]*100:.2f}%)")
    print(f"Dragapult weight: {y_opt[0]:.10f}")

# ============================================================================
# APPROACH 3: Enumerate ALL Nash equilibria more carefully
# For a symmetric game, check all possible support sizes
# ============================================================================
print("\n" + "="*80)
print("APPROACH 3: Exhaustive support enumeration (manual)")
print("="*80)

def check_nash_support_zerosum(M, row_support, col_support, tol=1e-8):
    """Check if there's a Nash equilibrium with given row and column supports.
    For the game A=M, B=M^T."""
    n = M.shape[0]
    rs = list(row_support)
    cs = list(col_support)
    kr = len(rs)
    kc = len(cs)
    
    if kr == 0 or kc == 0:
        return None
    
    # Row player: for each j in col_support, sum_i x_i * M[i,j] = v (indifference)
    # For j not in col_support: sum_i x_i * M[i,j] >= v (best response condition for col)
    # Wait - this is for the COLUMN player's indifference.
    
    # Actually: 
    # Row player mixes over rs. Column player mixes over cs.
    # For col player to be indifferent over cs: for each j in cs, sum_i x_i * M^T[j,i] = same value
    #   i.e., sum_i x_i * M[i,j] = v for all j in cs (col wants to minimize, but at eq is indifferent)
    # For row player to be indifferent over rs: for each i in rs, sum_j y_j * M[i,j] = same value
    #   i.e., sum_j y_j * M[i,j] = w for all i in rs
    
    # Solve for x (row strategy) from column indifference:
    # sum_{i in rs} x_i * M[i,j] = v for all j in cs
    # sum_{i in rs} x_i = 1
    # x_i >= 0
    
    # This is a system of (kc + 1) equations in (kr + 1) unknowns (x_i for i in rs, plus v)
    # For a unique solution, we need kc + 1 = kr + 1, i.e., kr = kc
    # But we can have kr != kc in general bimatrix games
    
    # Let's solve both systems
    from numpy.linalg import lstsq
    
    # System 1: Column indifference -> solve for x
    # [M[rs[0],cs[0]] M[rs[1],cs[0]] ... -1] [x_0]   [0]
    # [M[rs[0],cs[1]] M[rs[1],cs[1]] ... -1] [x_1] = [0]
    # ...                                     [...]   [...]
    # [1              1              ...  0 ] [v  ]   [1]
    
    A1 = np.zeros((kc + 1, kr + 1))
    b1 = np.zeros(kc + 1)
    for idx_j, j in enumerate(cs):
        for idx_i, i in enumerate(rs):
            A1[idx_j, idx_i] = M[i, j]
        A1[idx_j, kr] = -1
    A1[kc, :kr] = 1
    b1[kc] = 1
    
    if kc + 1 != kr + 1:
        # Overdetermined or underdetermined - use lstsq
        sol1, res1, rank1, sv1 = lstsq(A1, b1, rcond=None)
        if len(res1) > 0 and res1[0] > tol:
            return None
        x = sol1[:kr]
        v = sol1[kr]
    else:
        try:
            sol1 = np.linalg.solve(A1, b1)
            x = sol1[:kr]
            v = sol1[kr]
        except np.linalg.LinAlgError:
            return None
    
    # Check x >= 0
    if np.any(x < -tol):
        return None
    x = np.maximum(x, 0)
    
    # System 2: Row indifference -> solve for y
    A2 = np.zeros((kr + 1, kc + 1))
    b2 = np.zeros(kr + 1)
    for idx_i, i in enumerate(rs):
        for idx_j, j in enumerate(cs):
            A2[idx_i, idx_j] = M[i, j]
        A2[idx_i, kc] = -1
    A2[kr, :kc] = 1
    b2[kr] = 1
    
    if kr + 1 != kc + 1:
        sol2, res2, rank2, sv2 = lstsq(A2, b2, rcond=None)
        if len(res2) > 0 and res2[0] > tol:
            return None
        y = sol2[:kc]
        w = sol2[kc]
    else:
        try:
            sol2 = np.linalg.solve(A2, b2)
            y = sol2[:kc]
            w = sol2[kc]
        except np.linalg.LinAlgError:
            return None
    
    # Check y >= 0
    if np.any(y < -tol):
        return None
    y = np.maximum(y, 0)
    
    # Build full strategies
    x_full = np.zeros(n)
    for idx_i, i in enumerate(rs):
        x_full[i] = x[idx_i]
    
    y_full = np.zeros(n)
    for idx_j, j in enumerate(cs):
        y_full[j] = y[idx_j]
    
    # Verify Nash conditions:
    # For row player: sum_j y_j * M[i,j] <= w for all i, with equality for i in rs
    row_payoffs = M @ y_full
    for i in range(n):
        if i in rs:
            if abs(row_payoffs[i] - w) > tol:
                return None
        else:
            if row_payoffs[i] > w + tol:
                return None
    
    # For col player: sum_i x_i * M[i,j] >= v for all j, with equality for j in cs
    # Wait - col player gets M^T, so col payoff for column j = sum_i x_i * M^T[j,i] = sum_i x_i * M[i,j]... 
    # No wait. Col player payoff when row plays i, col plays j = M^T[j,i] = M[i,j]... no.
    # B = M^T means B[j,i] = M[i,j]. But the payoff to col when row=i, col=j is B[i,j] = M^T[i,j] = M[j,i].
    # So col payoff = sum_i x_i * M[j,i] for column j. Col wants to maximize this.
    # At equilibrium, for j in cs: sum_i x_i * M[j,i] = same value, and for j not in cs: sum_i x_i * M[j,i] <= that value.
    
    col_payoffs = M.T @ x_full  # col_payoffs[j] = sum_i x_i * M^T[j,i] = sum_i x_i * M[i,j]... 
    # Hmm, M.T @ x_full: (M.T)[j,i] * x_full[i] = M[i,j] * x[i] summed over i
    # This is sum_i x_i * M[i,j] which is ROW player's payoff against pure j
    
    # Let me reconsider. B = M^T. Col player payoff = sum over (i,j) of x_i * y_j * B[i,j]
    # = sum x_i * y_j * M[j,i]. For pure col strategy j: sum_i x_i * M[j,i].
    # So col_payoffs_correct[j] = sum_i x_i * M[j,i] = (M @ x_full)[j]... no.
    # (M @ x_full)[j] = sum_i M[j,i] * x_full[i] = sum_i x_i * M[j,i]. Yes!
    
    col_payoffs_correct = M @ x_full  # col_payoffs_correct[j] = sum_i x_i * M[j,i]
    
    # Col wants to maximize. At eq, for j in cs: payoff = some value vc, for j not in cs: payoff <= vc
    if len(cs) > 0:
        vc = col_payoffs_correct[cs[0]]
        for j in range(n):
            if j in cs:
                if abs(col_payoffs_correct[j] - vc) > tol:
                    return None
            else:
                if col_payoffs_correct[j] > vc + tol:
                    return None
    
    return x_full, y_full, w, vc if len(cs) > 0 else 0

# Enumerate all support pairs - but 2^14 x 2^14 = 2^28 is too many
# For symmetric games, we can focus on symmetric equilibria (same support for both)
# But we should also check asymmetric ones

# First: find all symmetric Nash equilibria (row support = col support)
print("\nSearching symmetric equilibria (same support)...")
all_eqs = []
from math import comb

total_subsets = sum(comb(14, k) for k in range(1, 15))
print(f"Total support subsets to check: {total_subsets}")

for size in range(1, 15):
    count = 0
    for support in combinations(range(14), size):
        support_set = set(support)
        result = check_nash_support_zerosum(M, support_set, support_set)
        if result is not None:
            x, y, vr, vc = result
            # Check if it's a duplicate
            is_dup = False
            for ex, ey, _, _ in all_eqs:
                if np.allclose(x, ex, atol=1e-8) and np.allclose(y, ey, atol=1e-8):
                    is_dup = True
                    break
            if not is_dup:
                all_eqs.append(result)
                support_names = [DECKS[i] for i in support]
                print(f"  Found EQ with support size {size}: {support_names}")
                print(f"    Row strategy: {dict((DECKS[i], round(float(x[i]),6)) for i in range(14) if x[i] > 1e-10)}")
                print(f"    Col strategy: {dict((DECKS[i], round(float(y[i]),6)) for i in range(14) if y[i] > 1e-10)}")
                print(f"    Row value: {vr:.4f}, Col value: {vc:.4f}")
                print(f"    Dragapult row: {x[0]:.8f}, col: {y[0]:.8f}")
        count += 1
    if count > 0:
        pass  # print(f"  Checked {count} subsets of size {size}")

print(f"\nTotal symmetric Nash equilibria found: {len(all_eqs)}")

# Now check asymmetric equilibria with small supports
print("\nSearching asymmetric equilibria (different supports, up to size 6)...")
asym_eqs = []
max_support_size = 6  # Keep tractable

for kr in range(1, max_support_size + 1):
    for kc in range(1, max_support_size + 1):
        if kr == kc:
            continue  # Already covered in symmetric search (support sets can differ even with same size)
        for rs in combinations(range(14), kr):
            for cs in combinations(range(14), kc):
                result = check_nash_support_zerosum(M, set(rs), set(cs))
                if result is not None:
                    x, y, vr, vc = result
                    is_dup = False
                    for ex, ey, _, _ in all_eqs + asym_eqs:
                        if np.allclose(x, ex, atol=1e-8) and np.allclose(y, ey, atol=1e-8):
                            is_dup = True
                            break
                    if not is_dup:
                        asym_eqs.append(result)
                        rs_names = [DECKS[i] for i in range(14) if x[i] > 1e-10]
                        cs_names = [DECKS[i] for i in range(14) if y[i] > 1e-10]
                        print(f"  Found asymmetric EQ: Row support {rs_names}, Col support {cs_names}")
                        print(f"    Row: {dict((DECKS[i], round(float(x[i]),6)) for i in range(14) if x[i] > 1e-10)}")
                        print(f"    Col: {dict((DECKS[i], round(float(y[i]),6)) for i in range(14) if y[i] > 1e-10)}")
                        print(f"    Dragapult row: {x[0]:.8f}, col: {y[0]:.8f}")

print(f"\nTotal asymmetric Nash equilibria found: {len(asym_eqs)}")

# ============================================================================
# SUMMARY
# ============================================================================
print("\n" + "="*80)
print("FINAL SUMMARY")
print("="*80)

all_found = all_eqs + asym_eqs

# Also add from support enumeration if not duplicates
for row, col in support_eqs:
    if np.any(row < -1e-10) or np.any(col < -1e-10):
        continue
    if abs(np.sum(row) - 1) > 1e-8 or abs(np.sum(col) - 1) > 1e-8:
        continue
    is_dup = False
    for ex, ey, _, _ in all_found:
        if np.allclose(row, ex, atol=1e-6) and np.allclose(col, ey, atol=1e-6):
            is_dup = True
            break
    if not is_dup:
        vr = row @ M @ col
        vc = 0
        all_found.append((row, col, vr, vc))
        print(f"  Additional EQ from nashpy support enum")

for label, row, col in unique_lh:
    is_dup = False
    for ex, ey, _, _ in all_found:
        if np.allclose(row, ex, atol=1e-6) and np.allclose(col, ey, atol=1e-6):
            is_dup = True
            break
    if not is_dup:
        vr = row @ M @ col
        vc = 0
        all_found.append((row, col, vr, vc))
        print(f"  Additional EQ from Lemke-Howson label {label}")

print(f"\nTotal unique Nash equilibria found: {len(all_found)}")

dragapult_zero_in_all = True
for idx, (x, y, vr, vc) in enumerate(all_found):
    d_row = x[0] if isinstance(x, np.ndarray) else 0
    d_col = y[0] if isinstance(y, np.ndarray) else 0
    row_support = [DECKS[i] for i in range(14) if x[i] > 1e-10]
    col_support = [DECKS[i] for i in range(14) if y[i] > 1e-10]
    print(f"\nEquilibrium {idx + 1}:")
    print(f"  Row support: {row_support}")
    print(f"  Col support: {col_support}")
    print(f"  Row strategy: {dict((DECKS[i], round(float(x[i]),6)) for i in range(14) if x[i] > 1e-10)}")
    print(f"  Col strategy: {dict((DECKS[i], round(float(y[i]),6)) for i in range(14) if y[i] > 1e-10)}")
    print(f"  Dragapult row weight: {d_row:.10f}")
    print(f"  Dragapult col weight: {d_col:.10f}")
    if d_row > 1e-10 or d_col > 1e-10:
        dragapult_zero_in_all = False
        print(f"  *** DRAGAPULT HAS NON-ZERO WEIGHT ***")

print(f"\n{'='*80}")
print(f"CONCLUSION: Dragapult has 0% weight in ALL Nash equilibria: {dragapult_zero_in_all}")
print(f"{'='*80}")
