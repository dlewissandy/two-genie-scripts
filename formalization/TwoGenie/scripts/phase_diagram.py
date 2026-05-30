#!/usr/bin/env python3
"""Phase-4 computational artifact: the cooperative-basin phase diagram.

This reproduces the (K_G2, K_G1) phase diagram of §5 using the *exact* basin-
certificate formulas that are kernel-verified in `TwoGenie/Priors/Hill.lean`.
Each quantity below corresponds 1:1 to a Lean definition:

    h(K,n,X)            <->  TwoGenie.hillTail            (K^n/(K^n+X^n))
    pi_low              <->  TwoGenie.piLow               (w - b - 1)
    pi_high             <->  TwoGenie.piHigh
    pi_bind             <->  TwoGenie.piBind              (2(w-b-1)+2(b̂+â)-W_max)
    W_max               <->  max over X in [0,1/2] of  b̂ g_G2(X) + â g_G1(X)

The Lean side proves the *structure* (monotone tail, the (T1)/(T2)/(T3) frontier
algebra, region nesting); this script does the floating-point evaluation that
mathlib's noncomputable `Real.rpow` cannot `#eval`, exactly the prose/computation
split described in the plan's Phase 4. Run inside the project uv venv:

    source ../.venv/bin/activate && python scripts/phase_diagram.py
"""
from __future__ import annotations
import csv
import pathlib
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# Working point of manuscript Figure 1 (favorable u_d>0); no-erosion (â=a, b̂=b).
N, A, B, D, UD = 2.0, 0.8, 0.3, 1.0, 0.1
W = D + UD                      # w = d + u_d   (TwoGenie: w)
AHAT, BHAT = A, B               # no-erosion reductions used in (T1)/(T2)/(T3)

X_HALF = np.linspace(0.0, 0.5, 257)   # grid on [0,1/2] for the W_max maximization


def hill_tail(K: float, n: float, X: np.ndarray) -> np.ndarray:
    """h(X) = K^n/(K^n + X^n)  ==  TwoGenie.hillTail."""
    Kn = K ** n
    return Kn / (Kn + X ** n)


def pair_sum(K: float, n: float, X: np.ndarray) -> np.ndarray:
    """g_i(X) = h(X) + h(1-X)  ==  the centro-symmetric pair-sum of §5."""
    return hill_tail(K, n, X) + hill_tail(K, n, 1.0 - X)


def pi_high(K2: float, K1: float) -> float:
    s2 = hill_tail(K2, N, np.array([1.0]))[0]
    s1 = hill_tail(K1, N, np.array([1.0]))[0]
    return W - B - 1.0 + BHAT * (1.0 - s2) + AHAT * (1.0 - s1)   # TwoGenie.piHigh


def pi_bind(K2: float, K1: float) -> float:
    Wmax = float(np.max(BHAT * pair_sum(K2, N, X_HALF) + AHAT * pair_sum(K1, N, X_HALF)))
    return 2.0 * (W - B - 1.0) + 2.0 * (BHAT + AHAT) - Wmax       # TwoGenie.piBind


def main() -> None:
    outdir = pathlib.Path(__file__).resolve().parent.parent / "figures"
    outdir.mkdir(exist_ok=True)
    grid = np.linspace(0.05, 1.5, 120)
    region = np.zeros((grid.size, grid.size))   # 0 red, 1 amber, 2 green
    rows = []
    for i, K1 in enumerate(grid):
        for j, K2 in enumerate(grid):
            ph, pb = pi_high(K2, K1), pi_bind(K2, K1)
            region[i, j] = 0 if ph < 0 else (2 if pb > 0 else 1)
            rows.append((K2, K1, ph, pb, int(region[i, j])))

    with open(outdir / "phase_diagram.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["K_G2", "K_G1", "pi_high", "pi_bind", "region"])
        w.writerows(rows)

    plt.figure(figsize=(6, 5))
    plt.pcolormesh(grid, grid, region, cmap=matplotlib.colors.ListedColormap(
        ["#d62728", "#ff7f0e", "#2ca02c"]), shading="auto")
    plt.xlabel(r"$K_{G_2}$ (median threshold, audit binding)")
    plt.ylabel(r"$K_{G_1}$ (median threshold, approval binding)")
    plt.title(f"Cooperative-basin phase diagram  (n={N}, a={A}, b={B}, d={D}, $u_d$={UD})")
    plt.text(0.05, 0.95, "green: $G_2$-favored (C)\namber: $G_1$-favored\nred: no $G_2$ corner",
             transform=plt.gca().transAxes, va="top", fontsize=8,
             bbox=dict(boxstyle="round", fc="white", alpha=0.8))
    plt.tight_layout()
    plt.savefig(outdir / "phase_diagram.png", dpi=140)
    pos = int((region == 2).sum())
    print(f"wrote {outdir/'phase_diagram.png'} and phase_diagram.csv "
          f"({pos}/{region.size} grid cells G2-favored)")


if __name__ == "__main__":
    main()
