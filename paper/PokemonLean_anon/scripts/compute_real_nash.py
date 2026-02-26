#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

ENTRY_RE = re.compile(r"\|\s*\.(\w+),\s*\.(\w+)\s*=>\s*(\d+)")


def parse_matrix(path: Path) -> tuple[list[str], list[list[Fraction]]]:
    lines = path.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip().startswith("def matchupWR"))
    entries: list[tuple[str, str, int]] = []
    for line in lines[start + 1 :]:
        if line.strip().startswith("-- ============================================================================"):
            break
        m = ENTRY_RE.search(line)
        if m:
            entries.append((m.group(1), m.group(2), int(m.group(3))))

    if not entries:
        raise ValueError(f"No matchup entries found in {path}")

    names: list[str] = []
    rows: list[list[Fraction]] = []
    cur_name = entries[0][0]
    cur_row: list[Fraction] = []
    for attacker, _defender, value in entries:
        if attacker != cur_name:
            names.append(cur_name)
            rows.append(cur_row)
            cur_name = attacker
            cur_row = []
        cur_row.append(Fraction(value, 1))
    names.append(cur_name)
    rows.append(cur_row)

    n = len(rows)
    if n != 14 or any(len(row) != 14 for row in rows):
        raise ValueError(f"Expected 14x14 matrix, got {n}x{sorted({len(r) for r in rows})}")
    return names, rows


def solve_lp(rows: list[list[Fraction]]) -> tuple[np.ndarray, np.ndarray, float]:
    n = len(rows)
    A = np.array([[float(x) for x in row] for row in rows], dtype=float)

    # Row player: maximize v s.t. A^T x >= v, sum x = 1, x >= 0.
    c_row = np.zeros(n + 1)
    c_row[-1] = -1.0
    A_ub_row = []
    b_ub_row = []
    for j in range(n):
        row = np.zeros(n + 1)
        row[:n] = -A[:, j]
        row[-1] = 1.0
        A_ub_row.append(row)
        b_ub_row.append(0.0)

    A_eq = [np.r_[np.ones(n), 0.0]]
    b_eq = [1.0]
    bounds = [(0.0, None)] * n + [(None, None)]

    row_res = linprog(
        c_row,
        A_ub=np.array(A_ub_row),
        b_ub=np.array(b_ub_row),
        A_eq=np.array(A_eq),
        b_eq=np.array(b_eq),
        bounds=bounds,
        method="highs",
    )
    if row_res.status != 0:
        raise RuntimeError(f"Row LP failed: {row_res.message}")

    # Column player: minimize w s.t. A y <= w, sum y = 1, y >= 0.
    c_col = np.zeros(n + 1)
    c_col[-1] = 1.0
    A_ub_col = []
    b_ub_col = []
    for i in range(n):
        row = np.zeros(n + 1)
        row[:n] = A[i, :]
        row[-1] = -1.0
        A_ub_col.append(row)
        b_ub_col.append(0.0)

    col_res = linprog(
        c_col,
        A_ub=np.array(A_ub_col),
        b_ub=np.array(b_ub_col),
        A_eq=np.array(A_eq),
        b_eq=np.array(b_eq),
        bounds=bounds,
        method="highs",
    )
    if col_res.status != 0:
        raise RuntimeError(f"Column LP failed: {col_res.message}")

    return row_res.x[:-1], col_res.x[:-1], row_res.x[-1]


def solve_fraction_system(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError("System must be square")
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]

    pivot_row = 0
    for col in range(n):
        pivot = None
        for r in range(pivot_row, n):
            if aug[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        aug[pivot_row], aug[pivot] = aug[pivot], aug[pivot_row]
        pv = aug[pivot_row][col]
        aug[pivot_row] = [x / pv for x in aug[pivot_row]]
        for r in range(n):
            if r != pivot_row and aug[r][col] != 0:
                factor = aug[r][col]
                aug[r] = [aug[r][c] - factor * aug[pivot_row][c] for c in range(n + 1)]
        pivot_row += 1

    sol = [Fraction(0, 1) for _ in range(n)]
    for r in range(n):
        lead = None
        for c in range(n):
            if aug[r][c] == 1 and all(aug[r2][c] == 0 for r2 in range(n) if r2 != r):
                lead = c
                break
        if lead is None:
            raise ValueError("Singular system while recovering exact solution")
        sol[lead] = aug[r][-1]
    return sol


def recover_exact_equilibrium(
    rows: list[list[Fraction]], row_mix_float: np.ndarray, col_mix_float: np.ndarray, tol: float = 1e-9
) -> tuple[list[Fraction], list[Fraction], Fraction]:
    n = len(rows)
    row_support = [i for i, x in enumerate(row_mix_float) if x > tol]
    col_support = [j for j, y in enumerate(col_mix_float) if y > tol]
    if not row_support or not col_support:
        raise ValueError("Empty support from LP")
    if len(row_support) != len(col_support):
        raise ValueError(
            f"Support sizes differ (row={len(row_support)}, col={len(col_support)}); basis recovery needs equal sizes"
        )

    # Recover row mix x and value v from binding columns in col support.
    k = len(row_support)
    mat_x = [[rows[i][j] for i in row_support] + [Fraction(-1, 1)] for j in col_support]
    mat_x.append([Fraction(1, 1)] * k + [Fraction(0, 1)])
    rhs_x = [Fraction(0, 1) for _ in col_support] + [Fraction(1, 1)]
    sol_x = solve_fraction_system(mat_x, rhs_x)
    v = sol_x[-1]

    # Recover column mix y from binding rows in row support (same v).
    mat_y = [[rows[i][j] for j in col_support] + [Fraction(-1, 1)] for i in row_support]
    mat_y.append([Fraction(1, 1)] * k + [Fraction(0, 1)])
    rhs_y = [Fraction(0, 1) for _ in row_support] + [Fraction(1, 1)]
    sol_y = solve_fraction_system(mat_y, rhs_y)
    v2 = sol_y[-1]
    if v != v2:
        raise ValueError(f"Recovered values differ: {v} vs {v2}")

    x = [Fraction(0, 1) for _ in range(n)]
    for pos, i in enumerate(row_support):
        x[i] = sol_x[pos]
    y = [Fraction(0, 1) for _ in range(n)]
    for pos, j in enumerate(col_support):
        y[j] = sol_y[pos]

    # Exact verification of LP inequalities.
    row_payoffs = [sum(rows[i][j] * y[j] for j in range(n)) for i in range(n)]
    col_payoffs = [sum(x[i] * rows[i][j] for i in range(n)) for j in range(n)]
    if not all(p <= v for p in row_payoffs):
        raise ValueError("Row inequality check failed")
    if not all(v <= p for p in col_payoffs):
        raise ValueError("Column inequality check failed")
    return x, y, v


def fstr(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute exact minimax equilibrium for RealMetagame matrix.")
    parser.add_argument(
        "--lean-file",
        default="PokemonLean/RealMetagame.lean",
        help="Path to RealMetagame.lean containing def matchupWR",
    )
    args = parser.parse_args()

    names, rows = parse_matrix(Path(args.lean_file))
    row_mix_float, col_mix_float, approx_v = solve_lp(rows)
    x, y, v = recover_exact_equilibrium(rows, row_mix_float, col_mix_float)

    print(f"LP approximate game value: {approx_v:.12f}")
    print(f"Exact game value: {fstr(v)}")
    print("\nRow player equilibrium support (index, deck, weight):")
    for i, w in enumerate(x):
        if w:
            print(f"  {i:2d}  {names[i]:<24}  {fstr(w)}")

    print("\nColumn player equilibrium support (index, deck, weight):")
    for j, w in enumerate(y):
        if w:
            print(f"  {j:2d}  {names[j]:<24}  {fstr(w)}")

    print("\nLean literals:")
    print(f"  realNashValue = ({v.numerator} : Rat) / ({v.denominator} : Rat)")
    print("  row strategy non-zero entries:")
    for i, w in enumerate(x):
        if w:
            print(f"    {i} -> ({w.numerator} : Rat) / ({w.denominator} : Rat)")
    print("  col strategy non-zero entries:")
    for j, w in enumerate(y):
        if w:
            print(f"    {j} -> ({w.numerator} : Rat) / ({w.denominator} : Rat)")


if __name__ == "__main__":
    main()
