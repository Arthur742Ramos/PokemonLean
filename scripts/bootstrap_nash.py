#!/usr/bin/env python3
"""Bootstrap Nash equilibrium stability analysis.

Samples matchup win rates from Wilson 95% confidence intervals,
computes Nash equilibrium for each sample, and reports stability metrics.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

# ── Data parsing ─────────────────────────────────────────────────────────────

DECK_NAMES = [
    "Alakazam Dudunsparce",
    "Ceruledge",
    "Charizard Noctowl",
    "Charizard Pidgeot",
    "Dragapult Charizard",
    "Dragapult Dusknoir",
    "Gardevoir",
    "Gardevoir Jellicent",
    "Gholdengo Lunatone",
    "Grimmsnarl Froslass",
    "Kangaskhan Bouffalant",
    "Mega Absol Box",
    "N's Zoroark",
    "Raging Bolt Ogerpon",
]

SHORT_NAMES = [
    "Alak.Dud",
    "Ceruledge",
    "Char.Noct",
    "Char.Pidg",
    "Drag.Char",
    "Drag.Dusk",
    "Gardevoir",
    "Gard.Jell",
    "Ghol.Luna",
    "Grimm.Fro",
    "Kang.Bouf",
    "M.Absol",
    "N.Zoroark",
    "R.Bolt.Og",
]

WLT_RE = re.compile(r"(\d+)-(\d+)-(\d+)")


def parse_matchup_data(path: Path) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Parse the markdown file and return W, L, T matrices (14×14)."""
    text = path.read_text()

    # Split into per-deck sections
    sections = text.split("### ")[1:]  # skip preamble
    W = np.zeros((14, 14), dtype=int)
    L = np.zeros((14, 14), dtype=int)
    T = np.zeros((14, 14), dtype=int)

    for sec in sections:
        lines = sec.strip().split("\n")
        deck_name = lines[0].strip()
        if deck_name not in DECK_NAMES:
            continue
        i = DECK_NAMES.index(deck_name)

        row_idx = 0
        for line in lines:
            if row_idx >= 14:
                break
            if "W-L-T" in line and "WR%" in line:
                continue  # skip header
            m = WLT_RE.search(line)
            if m:
                w, l, t = int(m.group(1)), int(m.group(2)), int(m.group(3))
                W[i, row_idx] = w
                L[i, row_idx] = l
                T[i, row_idx] = t
                row_idx += 1

    return W, L, T


# ── Wilson confidence interval ───────────────────────────────────────────────

def wilson_ci(wins: int, losses: int, ties: int, z: float = 1.96) -> tuple[float, float]:
    """Wilson score 95% CI for win rate = (W + T/3) / (W + L + T)."""
    n = wins + losses + ties
    if n == 0:
        return 0.0, 1.0
    p_hat = (wins + ties / 3.0) / n
    z2 = z * z
    denom = 1 + z2 / n
    centre = (p_hat + z2 / (2 * n)) / denom
    spread = z / denom * np.sqrt(p_hat * (1 - p_hat) / n + z2 / (4 * n * n))
    lo = max(0.0, centre - spread)
    hi = min(1.0, centre + spread)
    return lo, hi


# ── Nash equilibrium via LP ──────────────────────────────────────────────────

def solve_nash_lp(A: np.ndarray) -> tuple[np.ndarray, float]:
    """Solve for row-player maximin strategy. Returns (mix, value).

    maximize v  s.t.  A^T x >= v·1,  sum(x) = 1,  x >= 0
    """
    n = A.shape[0]
    # Decision variables: x_0..x_{n-1}, v
    c = np.zeros(n + 1)
    c[-1] = -1.0  # maximize v

    # A^T x - v >= 0  =>  -A^T x + v <= 0
    A_ub = np.zeros((n, n + 1))
    for j in range(n):
        A_ub[j, :n] = -A[:, j]
        A_ub[j, -1] = 1.0
    b_ub = np.zeros(n)

    A_eq = np.zeros((1, n + 1))
    A_eq[0, :n] = 1.0
    b_eq = np.array([1.0])

    bounds = [(0.0, None)] * n + [(None, None)]

    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if res.status != 0:
        raise RuntimeError(f"LP failed: {res.message}")
    return res.x[:n], res.x[-1]


# ── Bootstrap ────────────────────────────────────────────────────────────────

def run_bootstrap(
    W: np.ndarray, L: np.ndarray, T: np.ndarray,
    n_iter: int = 10_000, seed: int = 42,
) -> dict:
    rng = np.random.default_rng(seed)
    n = 14

    # Precompute Wilson CIs and point estimates
    ci_lo = np.zeros((n, n))
    ci_hi = np.zeros((n, n))
    point_wr = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            lo, hi = wilson_ci(W[i, j], L[i, j], T[i, j])
            ci_lo[i, j] = lo
            ci_hi[i, j] = hi
            total = W[i, j] + L[i, j] + T[i, j]
            point_wr[i, j] = (W[i, j] + T[i, j] / 3.0) / total if total > 0 else 0.5

    # Compute point-estimate Nash
    # Scale to percentage like the original data
    A_point = point_wr * 100.0
    point_mix, point_val = solve_nash_lp(A_point)
    point_support = frozenset(i for i in range(n) if point_mix[i] > 1e-9)

    # Bootstrap
    all_weights = np.zeros((n_iter, n))
    support_counts = np.zeros(n, dtype=int)
    same_support_count = 0
    dragapult_idx = DECK_NAMES.index("Dragapult Dusknoir")
    dragapult_zero = 0

    for it in range(n_iter):
        # Sample win rates uniformly from Wilson CIs
        sampled = rng.uniform(ci_lo, ci_hi) * 100.0
        try:
            mix, val = solve_nash_lp(sampled)
        except RuntimeError:
            continue

        all_weights[it] = mix
        supp = frozenset(i for i in range(n) if mix[i] > 1e-9)
        for i in supp:
            support_counts[i] += 1
        if supp == point_support:
            same_support_count += 1
        if mix[dragapult_idx] < 1e-9:
            dragapult_zero += 1

        if (it + 1) % 2000 == 0:
            print(f"  ... {it+1}/{n_iter} iterations done", file=sys.stderr)

    return {
        "n_iter": n_iter,
        "point_mix": point_mix,
        "point_val": point_val,
        "point_support": point_support,
        "all_weights": all_weights,
        "support_counts": support_counts,
        "same_support_count": same_support_count,
        "dragapult_zero": dragapult_zero,
        "ci_lo": ci_lo,
        "ci_hi": ci_hi,
        "point_wr": point_wr,
    }


# ── Output ───────────────────────────────────────────────────────────────────

def format_results(res: dict) -> str:
    lines: list[str] = []
    n = 14
    n_iter = res["n_iter"]

    lines.append("=" * 72)
    lines.append("  BOOTSTRAP NASH EQUILIBRIUM STABILITY ANALYSIS")
    lines.append(f"  {n_iter:,} iterations, Wilson 95% CI sampling")
    lines.append("=" * 72)
    lines.append("")

    # ── Point estimate ──
    lines.append("── Point-estimate Nash equilibrium ──")
    lines.append(f"Game value: {res['point_val']:.4f}%")
    lines.append("")
    lines.append(f"{'Deck':<24} {'Weight':>8}")
    lines.append("-" * 34)
    for i in range(n):
        w = res["point_mix"][i]
        if w > 1e-9:
            lines.append(f"{DECK_NAMES[i]:<24} {w*100:>7.2f}%")
    lines.append("")

    # ── Support stability ──
    lines.append("── Support stability ──")
    frac = res["same_support_count"] / n_iter
    lines.append(f"Same {len(res['point_support'])}-deck support in {res['same_support_count']:,}/{n_iter:,} = {frac*100:.1f}% of bootstraps")
    lines.append("")
    lines.append(f"{'Deck':<24} {'In support':>12} {'Fraction':>10}")
    lines.append("-" * 48)
    for i in range(n):
        cnt = res["support_counts"][i]
        if cnt > 0:
            lines.append(f"{DECK_NAMES[i]:<24} {cnt:>10,}   {cnt/n_iter*100:>7.1f}%")
    lines.append("")

    # ── Weight confidence intervals ──
    lines.append("── Weight 95% confidence intervals ──")
    lines.append(f"{'Deck':<24} {'Mean':>7} {'2.5%':>7} {'97.5%':>7} {'Median':>7}")
    lines.append("-" * 56)
    weights = res["all_weights"]
    for i in range(n):
        col = weights[:, i]
        mean = np.mean(col)
        if mean < 1e-6 and res["support_counts"][i] < n_iter * 0.01:
            continue
        lo = np.percentile(col, 2.5)
        hi = np.percentile(col, 97.5)
        med = np.median(col)
        lines.append(f"{DECK_NAMES[i]:<24} {mean*100:>6.2f}% {lo*100:>6.2f}% {hi*100:>6.2f}% {med*100:>6.2f}%")
    lines.append("")

    # ── Dragapult exclusion ──
    dragapult_idx = DECK_NAMES.index("Dragapult Dusknoir")
    dz = res["dragapult_zero"]
    lines.append("── Dragapult Dusknoir exclusion rate ──")
    lines.append(f"Zero weight in {dz:,}/{n_iter:,} = {dz/n_iter*100:.1f}% of bootstraps")
    lines.append("")

    # ── Wilson CI widths for key matchups ──
    lines.append("── Wilson 95% CI widths for key matchups ──")
    ci_lo = res["ci_lo"]
    ci_hi = res["ci_hi"]
    point_wr = res["point_wr"]
    key_pairs = [
        (5, 6, "Drag.Dusk vs Gardevoir"),
        (5, 9, "Drag.Dusk vs Grimm.Fros"),
        (5, 11, "Drag.Dusk vs M.Absol"),
        (5, 8, "Drag.Dusk vs Ghol.Luna"),
        (9, 11, "Grimm.Fros vs M.Absol"),
        (11, 13, "M.Absol vs R.Bolt.Og"),
    ]
    lines.append(f"{'Matchup':<28} {'Point':>7} {'CI low':>7} {'CI high':>7} {'Width':>7} {'N':>6}")
    lines.append("-" * 66)
    W_mat = np.zeros((14, 14), dtype=int)  # reconstruct from point data
    for i, j, label in key_pairs:
        wr = point_wr[i, j]
        lo = ci_lo[i, j]
        hi = ci_hi[i, j]
        width = hi - lo
        lines.append(f"{label:<28} {wr*100:>6.1f}% {lo*100:>6.1f}% {hi*100:>6.1f}% {width*100:>6.1f}pp")
    lines.append("")

    # ── LaTeX table ──
    lines.append("── LaTeX table: Bootstrap Nash weight CIs ──")
    lines.append(r"\begin{tabular}{l r r r r}")
    lines.append(r"\toprule")
    lines.append(r"Deck & Mean & 2.5\% & 97.5\% & Support\% \\")
    lines.append(r"\midrule")
    for i in range(n):
        col = weights[:, i]
        mean = np.mean(col)
        lo = np.percentile(col, 2.5)
        hi = np.percentile(col, 97.5)
        supp_pct = res["support_counts"][i] / n_iter * 100
        if mean > 0.001 or supp_pct > 1.0:
            lines.append(
                f"{DECK_NAMES[i]} & {mean*100:.1f}\\% & {lo*100:.1f}\\% & {hi*100:.1f}\\% & {supp_pct:.0f}\\% \\\\"
            )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append("")

    return "\n".join(lines)


# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    data_path = Path(__file__).parent.parent / "data" / "trainerhill_matchups_2026-02-19.md"
    if not data_path.exists():
        print(f"ERROR: Data file not found: {data_path}", file=sys.stderr)
        sys.exit(1)

    print("Parsing matchup data...", file=sys.stderr)
    W, L, T = parse_matchup_data(data_path)

    # Sanity check
    total_games = W + L + T
    print(f"Total games in matrix: {total_games.sum():,}", file=sys.stderr)
    print(f"Max games in a cell: {total_games.max():,} (mirror matchup)", file=sys.stderr)
    print(f"Min games in a cell: {total_games[total_games > 0].min()}", file=sys.stderr)

    print("Running 10,000 bootstrap iterations...", file=sys.stderr)
    results = run_bootstrap(W, L, T, n_iter=10_000, seed=42)

    output = format_results(results)
    print(output)


if __name__ == "__main__":
    main()
