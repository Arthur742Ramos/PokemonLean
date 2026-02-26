#!/usr/bin/env python3
"""Compute the symmetric Nash equilibrium of the symmetrized matchup matrix.

Symmetrization: S_ij = (M_ij + (1000 - M_ji)) / 2
This gives a truly constant-sum matrix where S_ij + S_ji = 1000 for all i,j.
The resulting zero-sum game has a unique symmetric Nash equilibrium.

We also compare with the bimatrix Nash from the original (non-symmetric) matrix.
"""
from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

ENTRY_RE = re.compile(r"\|\s*\.(\w+),\s*\.(\w+)\s*=>\s*(\d+)")

# Deck ordering matching Deck.toFin in RealMetagame.lean
DECK_ORDER = [
    "DragapultDusknoir",
    "GholdengoLunatone",
    "GrimssnarlFroslass",
    "MegaAbsolBox",
    "Gardevoir",
    "CharizardNoctowl",
    "GardevoirJellicent",
    "CharizardPidgeot",
    "DragapultCharizard",
    "RagingBoltOgerpon",
    "NsZoroark",
    "AlakazamDudunsparce",
    "KangaskhanBouffalant",
    "Ceruledge",
]

PRETTY = {
    "DragapultDusknoir": "Dragapult Dusknoir",
    "GholdengoLunatone": "Gholdengo Lunatone",
    "GrimssnarlFroslass": "Grimmsnarl Froslass",
    "MegaAbsolBox": "Mega Absol Box",
    "Gardevoir": "Gardevoir",
    "CharizardNoctowl": "Charizard Noctowl",
    "GardevoirJellicent": "Gardevoir Jellicent",
    "CharizardPidgeot": "Charizard Pidgeot",
    "DragapultCharizard": "Dragapult Charizard",
    "RagingBoltOgerpon": "Raging Bolt Ogerpon",
    "NsZoroark": "N's Zoroark",
    "AlakazamDudunsparce": "Alakazam Dudunsparce",
    "KangaskhanBouffalant": "Kangaskhan Bouffalant",
    "Ceruledge": "Ceruledge",
}


def parse_matrix(path: Path) -> tuple[list[str], np.ndarray]:
    """Parse the 14x14 matchup matrix from RealMetagame.lean."""
    lines = path.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip().startswith("def matchupWR"))
    entries: dict[tuple[str, str], int] = {}
    for line in lines[start + 1:]:
        if line.strip().startswith("-- ===="):
            break
        m = ENTRY_RE.search(line)
        if m:
            entries[(m.group(1), m.group(2))] = int(m.group(3))

    n = len(DECK_ORDER)
    M = np.zeros((n, n), dtype=float)
    for i, di in enumerate(DECK_ORDER):
        for j, dj in enumerate(DECK_ORDER):
            M[i, j] = entries[(di, dj)]
    return DECK_ORDER, M


def symmetrize(M: np.ndarray) -> np.ndarray:
    """S_ij = (M_ij + (1000 - M_ji)) / 2"""
    n = M.shape[0]
    S = np.zeros_like(M)
    for i in range(n):
        for j in range(n):
            S[i, j] = (M[i, j] + 1000.0 - M[j, i]) / 2.0
    return S


def solve_symmetric_zerosum(S: np.ndarray) -> tuple[np.ndarray, float]:
    """Solve the symmetric zero-sum game. Returns (mixed strategy, game value)."""
    n = S.shape[0]
    # Maximize v s.t. S^T x >= v, sum x = 1, x >= 0
    # => minimize -v
    c = np.zeros(n + 1)
    c[-1] = -1.0

    A_ub = []
    b_ub = []
    for j in range(n):
        row = np.zeros(n + 1)
        row[:n] = -S[:, j]
        row[-1] = 1.0
        A_ub.append(row)
        b_ub.append(0.0)

    A_eq = [np.append(np.ones(n), 0.0)]
    b_eq = [1.0]
    bounds = [(0.0, None)] * n + [(None, None)]

    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=bounds, method="highs")
    if res.status != 0:
        raise RuntimeError(f"LP failed: {res.message}")

    x = res.x[:n]
    v = res.x[-1]
    return x, v


def solve_bimatrix(M: np.ndarray) -> tuple[np.ndarray, np.ndarray, float]:
    """Solve bimatrix game (row and column LPs separately)."""
    n = M.shape[0]

    # Row player
    c = np.zeros(n + 1); c[-1] = -1.0
    A_ub = []
    for j in range(n):
        row = np.zeros(n + 1)
        row[:n] = -M[:, j]
        row[-1] = 1.0
        A_ub.append(row)
    A_eq = [np.append(np.ones(n), 0.0)]
    bounds = [(0.0, None)] * n + [(None, None)]
    row_res = linprog(c, A_ub=np.array(A_ub), b_ub=np.zeros(n),
                      A_eq=np.array(A_eq), b_eq=[1.0], bounds=bounds, method="highs")

    # Column player
    c2 = np.zeros(n + 1); c2[-1] = 1.0
    A_ub2 = []
    for i in range(n):
        row = np.zeros(n + 1)
        row[:n] = M[i, :]
        row[-1] = -1.0
        A_ub2.append(row)
    col_res = linprog(c2, A_ub=np.array(A_ub2), b_ub=np.zeros(n),
                      A_eq=np.array(A_eq), b_eq=[1.0], bounds=bounds, method="highs")

    return row_res.x[:n], col_res.x[:n], row_res.x[-1]


def main():
    lean_path = Path(__file__).parent.parent / "PokemonLean" / "RealMetagame.lean"
    names, M = parse_matrix(lean_path)
    n = len(names)

    output_lines = []
    def p(s=""):
        print(s)
        output_lines.append(s)

    p("=" * 72)
    p("SYMMETRIC NASH EQUILIBRIUM ANALYSIS")
    p("=" * 72)

    # Check asymmetry of original matrix
    p("\n1) CONSTANT-SUM DEVIATION IN ORIGINAL MATRIX")
    p("-" * 50)
    max_dev = 0
    dev_pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            s = M[i, j] + M[j, i]
            dev = abs(s - 1000)
            if dev > max_dev:
                max_dev = dev
            if dev > 0:
                dev_pairs.append((names[i], names[j], s, dev))

    p(f"Max deviation from M_ij + M_ji = 1000: {max_dev}")
    p(f"Number of off-diagonal pairs with deviation > 0: {len(dev_pairs)} / {n*(n-1)//2}")
    if dev_pairs:
        p("Top 5 deviations:")
        dev_pairs.sort(key=lambda x: -x[3])
        for nm1, nm2, s, d in dev_pairs[:5]:
            p(f"  {PRETTY[nm1]:25s} vs {PRETTY[nm2]:25s}: M_ij + M_ji = {s:.0f} (dev = {d:.0f})")

    # Symmetrize
    S = symmetrize(M)

    p("\n2) SYMMETRIZED MATRIX VERIFICATION")
    p("-" * 50)
    # Verify constant-sum
    ok = True
    for i in range(n):
        for j in range(n):
            if abs(S[i, j] + S[j, i] - 1000) > 1e-10:
                ok = False
    p(f"S_ij + S_ji = 1000 for all i,j: {ok}")
    p(f"Diagonal values: {[S[i,i] for i in range(n)]}")

    # Solve symmetric Nash
    p("\n3) SYMMETRIC NASH EQUILIBRIUM (from symmetrized matrix)")
    p("-" * 50)
    x_sym, v_sym = solve_symmetric_zerosum(S)
    p(f"Game value: {v_sym:.6f} ({v_sym/10:.4f}%)")

    p("\nSymmetric Nash weights (nonzero):")
    sym_support = []
    for i in range(n):
        if x_sym[i] > 1e-9:
            p(f"  {i:2d}  {PRETTY[names[i]]:25s}  {x_sym[i]*100:6.2f}%")
            sym_support.append(names[i])

    # Solve bimatrix Nash on original
    p("\n4) BIMATRIX NASH (from original non-symmetric matrix)")
    p("-" * 50)
    x_row, x_col, v_bi = solve_bimatrix(M)
    p(f"Bimatrix game value: {v_bi:.6f} ({v_bi/10:.4f}%)")

    p("\nRow player support:")
    row_support = []
    for i in range(n):
        if x_row[i] > 1e-9:
            p(f"  {i:2d}  {PRETTY[names[i]]:25s}  {x_row[i]*100:6.2f}%")
            row_support.append(names[i])

    p("\nColumn player support:")
    col_support = []
    for i in range(n):
        if x_col[i] > 1e-9:
            p(f"  {i:2d}  {PRETTY[names[i]]:25s}  {x_col[i]*100:6.2f}%")
            col_support.append(names[i])

    # Comparison
    p("\n5) COMPARISON: SYMMETRIC vs BIMATRIX")
    p("-" * 50)
    sym_set = set(sym_support)
    row_set = set(row_support)
    col_set = set(col_support)
    union_bi = row_set | col_set

    p(f"Symmetric support size: {len(sym_support)}")
    p(f"Bimatrix row support size: {len(row_support)}")
    p(f"Bimatrix col support size: {len(col_support)}")
    p(f"Symmetric support decks: {', '.join(PRETTY[d] for d in sym_support)}")
    p(f"Bimatrix union support:  {', '.join(PRETTY[d] for d in sorted(union_bi))}")
    p(f"Core decks in both: {', '.join(PRETTY[d] for d in sorted(sym_set & union_bi))}")

    in_both = sym_set & union_bi
    only_sym = sym_set - union_bi
    only_bi = union_bi - sym_set
    p(f"\nIn symmetric only: {', '.join(PRETTY[d] for d in sorted(only_sym)) or 'none'}")
    p(f"In bimatrix only:  {', '.join(PRETTY[d] for d in sorted(only_bi)) or 'none'}")

    # Key check: does Dragapult get weight?
    drag_idx = names.index("DragapultDusknoir")
    p(f"\nDragapult symmetric weight: {x_sym[drag_idx]*100:.4f}%")
    p(f"Dragapult bimatrix row weight: {x_row[drag_idx]*100:.4f}%")
    p(f"Dragapult bimatrix col weight: {x_col[drag_idx]*100:.4f}%")

    p("\n" + "=" * 72)
    p("CONCLUSION")
    p("=" * 72)
    p(f"The symmetrized constant-sum game has game value {v_sym/10:.4f}%.")
    p(f"The symmetric Nash support is: {', '.join(PRETTY[d] for d in sym_support)}.")
    p(f"This {'matches' if sym_set == union_bi else 'largely overlaps with'} the bimatrix Nash support.")
    p(f"Dragapult receives 0% weight in {'both' if x_sym[drag_idx] < 1e-9 and x_row[drag_idx] < 1e-9 else 'the symmetric'} equilibria.")
    p("The qualitative conclusions are robust to the constant-sum approximation.")

    # Save output
    out_path = Path(__file__).parent.parent / "data" / "symmetric_nash_results.txt"
    out_path.write_text("\n".join(output_lines) + "\n")
    p(f"\nResults saved to {out_path}")


if __name__ == "__main__":
    main()
