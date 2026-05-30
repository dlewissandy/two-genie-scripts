"""
Pareto-prior basin phase diagrams, formatted to match the Hill-prior figures
(see the figures/ directory at the repo root): region shading +
labeled pi_high / pi_bind contour families, bold =0 boundaries, reference points,
matched diagonal, legend, multi-line title.

Companion to the Hill diagrams. The basin-certificate pi-functions are
prior-agnostic (they depend on the prior only through its survival tail F̄_g), so
this swaps the Hill tail for the **Pareto Type I** tail and sweeps the Pareto
**scale** sigma_g — the location parameter, playing the role K_g played for Hill;
the shape alpha (tail index) is fixed, as n was. Plane: (sigma_G2, sigma_G1).

Correspondence to the kernel-verified Lean (TwoGenie/Priors/Pareto.lean):
    tail(chi, sigma)  ==  TwoGenie.paretoTail  with xm := sigma
        F̄(X) = 1 for X <= sigma,  (sigma/X)^alpha for X >= sigma  ==  min(1,(sigma/X)^alpha)
    pi_high / pi_bind  ==  TwoGenie.piHigh / piBind  (same form as Hill)
paretoTail_antitoneOn (Q2a) and paretoTail_lipschitz (Q2b) are both proved, so
this is a fully-certified ThresholdPrior; the plots are reproducible numerics on
top of that certified structure.

Run inside the project uv venv:
    source ../.venv/bin/activate && python scripts/phase_diagram_pareto.py
"""
import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D

# Evaluation mesh, shared by π_high, π_bind and χ*. The π_bind=0 contour has near-vertical
# segments that marching-squares renders as a staircase on a coarse mesh, so the mesh is fine
# (900²). That is affordable because W_max is computed as a vectorized field over the whole
# mesh (see make_panel), not per grid point.
SIG = np.linspace(0.05, 0.95, 900)        # Pareto scale sigma in (0,1); sigma>=1 => F̄≡1 (degenerate)
CHI = np.linspace(0.0, 0.5, 2001)         # dense grid for W_max interior maxima (exact kinks added separately)


def make_panel(alpha, a, b, d, u_d, fname, subtitle):
    pi_low = d + u_d - b - 1              # (B-low) test value; X-independent, must be < 0

    def tail(chi, sig):                   # == TwoGenie.paretoTail (xm := sig)
        with np.errstate(divide="ignore", invalid="ignore"):
            return np.minimum(1.0, (sig / chi) ** alpha)

    def sat(sig):                         # F̄(1) = sigma^alpha
        return sig ** alpha

    def g(chi, sig):                      # centro-symmetric pair-sum g_g(chi)
        return tail(chi, sig) + tail(1.0 - chi, sig)

    def pi_high(s2, s1):                  # == TwoGenie.piHigh  (B-high)
        return d + a * (1 - sat(s1)) + u_d - 1 - b * sat(s2)

    def W_max(s2, s1):
        # max over [0,1/2] of W(chi) = b g_2 + a g_1. Pareto's max sits at a kink
        # (chi = sigma_g or 1 - sigma_g), so add those to the dense grid explicitly;
        # this is exact at the kinks (verified equivalent to a Brent W'-root search).
        chi = np.concatenate([CHI] + [np.array([k]) for k in (s2, 1 - s2, s1, 1 - s1)
                                      if 0.0 <= k <= 0.5])
        return float(np.max(b * g(chi, s2) + a * g(chi, s1)))

    def pi_bind(s2, s1):                  # == TwoGenie.piBind  (C)
        return 2.0 * (u_d + d - 1.0 + a) - W_max(s2, s1)

    # phi_b grid via a *vectorized* W_max field — identical to the scalar W_max/pi_bind above
    # (verified, max diff 0.0) but cheap enough for the fine mesh, so the steep π_bind=0 contour
    # renders smoothly instead of as a marching-squares staircase. W is maximized at a Pareto
    # kink χ = min(σ_g, 1−σ_g) (added exactly) or an interior point of the dense CHI grid.
    S2, S1 = np.meshgrid(SIG, SIG)
    phi_h = pi_high(S2, S1)
    W_max_grid = np.full(S2.shape, -np.inf)
    for X in CHI:
        W_max_grid = np.maximum(W_max_grid, b * g(X, S2) + a * g(X, S1))
    for Xk in (np.minimum(S2, 1.0 - S2), np.minimum(S1, 1.0 - S1)):
        W_max_grid = np.maximum(W_max_grid, b * g(Xk, S2) + a * g(Xk, S1))
    phi_b = 2.0 * (u_d + d - 1.0 + a) - W_max_grid

    fig, ax = plt.subplots(figsize=(10, 9))

    region = np.zeros_like(phi_h)
    region[(phi_h >= 0) & (phi_b < 0)] = 1
    region[(phi_b >= 0)] = 2
    ax.imshow(region, origin="lower",
              extent=[SIG.min(), SIG.max(), SIG.min(), SIG.max()],
              cmap=ListedColormap(["#fad9d9", "#fdf0c9", "#dbecda"]),
              vmin=-0.5, vmax=2.5, aspect="equal", alpha=0.55)

    def fam_levels(Z, k=6):
        lo, hi = float(np.nanmin(Z)), float(np.nanmax(Z))
        if hi - lo < 1e-6:
            return []
        return [x for x in np.linspace(lo, hi, k + 2)[1:-1] if abs(x) > 1e-3]

    lv_h = fam_levels(phi_h)
    if lv_h:
        cs_h = ax.contour(S2, S1, phi_h, levels=lv_h, colors="#b21e3a",
                          linewidths=1.1, alpha=0.9)
        ax.clabel(cs_h, inline=True, fontsize=8, fmt="%.2f")
    if phi_h.min() < 0 < phi_h.max():
        cs_h0 = ax.contour(S2, S1, phi_h, levels=[0], colors="#b21e3a", linewidths=3.0)
        ax.clabel(cs_h0, inline=True, fontsize=10, fmt={0: "π_high = 0"})

    lv_b = fam_levels(phi_b)
    if lv_b:
        cs_b = ax.contour(S2, S1, phi_b, levels=lv_b, colors="#1f4e9b",
                          linewidths=1.1, alpha=0.9, linestyles="--")
        ax.clabel(cs_b, inline=True, fontsize=8, fmt="%.2f")
    if phi_b.min() < 0 < phi_b.max():
        cs_b0 = ax.contour(S2, S1, phi_b, levels=[0], colors="#1f4e9b",
                           linewidths=3.0, linestyles="--")
        ax.clabel(cs_b0, inline=True, fontsize=10, fmt={0: "π_bind = 0"})

    # χ* (basin tipping point) contours — purple dotted. χ*(σ_G2, σ_G1) = inf{χ : F_Δ ≥ 0},
    # the first zero of the non-decreasing F_Δ (NaN where no all-G2 corner exists, since
    # F_Δ(1) = π_high). The floor N_c > 1/(1/2 − χ*) is prior-agnostic, so each level fixes
    # the minimum favored community size — the lower bound of the operational window — just
    # as in the Hill panels. The bold χ* = 1/2 curve marks where that floor diverges and the
    # window closes; for χ* > 1/2 (amber side) F_Δ(1/2) < 0, (C) fails at the midpoint, and
    # G1 is favored on the integrated payoff — larger N_c does not rescue it.
    #
    # The Pareto tail has a kink at χ = σ, so χ* is piecewise: where the root sits above both
    # thresholds it is the smooth √((a·σ_G1² + b·σ_G2²)/(a + u_d+d−1)) (α=2); where it drops
    # below the larger threshold, that genie's tail is saturated at 1 and stops locating the
    # root, so the contour turns axis-aligned. Each χ* curve thus has two genuine corners. χ*
    # is found by a vectorized monotone scan over χ (the inf-definition above) on the shared
    # fine mesh, so those corners stay crisp without marching-squares faceting.
    chi_grid = np.full(S2.shape, np.nan)
    found = np.zeros(S2.shape, dtype=bool)
    for c in np.linspace(1e-6, 1.0, 2000):
        Fc = (u_d + d - 1.0 + a * (1.0 - np.minimum(1.0, (S1 / c) ** alpha))
              - b * np.minimum(1.0, (S2 / c) ** alpha))
        newly = (Fc >= 0.0) & (~found)
        chi_grid[newly] = c
        found |= newly
    cs_chi = ax.contour(S2, S1, chi_grid, levels=[0.15, 0.2, 0.3, 0.4, 0.45],
                        colors="#6a3d9a", linewidths=1.0, linestyles=":", alpha=0.95)
    ax.clabel(cs_chi, inline=True, fontsize=8, fmt=r"$\chi^*=%.2f$")
    cs_chi12 = ax.contour(S2, S1, chi_grid, levels=[0.5],
                          colors="#6a3d9a", linewidths=3.0, linestyles=":")
    ax.clabel(cs_chi12, inline=True, fontsize=9, fmt={0.5: r"$\chi^*=1/2$"})

    ax.plot(SIG, SIG, color="gray", linestyle="-", linewidth=1.0, alpha=0.4)
    ax.text(0.80, 0.83, r"$\sigma_{G_2} = \sigma_{G_1}$", color="gray",
            fontsize=9, rotation=45)

    for s2, s1, name in [(0.2, 0.2, "A"), (0.7, 0.7, "B"), (0.2, 0.7, "C"), (0.7, 0.2, "D")]:
        ax.plot(s2, s1, "o", markersize=9, markerfacecolor="white",
                markeredgecolor="black", markeredgewidth=1.5, zorder=5)
        ax.annotate(f"{name}: π_h={pi_high(s2, s1):+.2f}, π_b={pi_bind(s2, s1):+.2f}",
                    (s2, s1), xytext=(11, 9), textcoords="offset points",
                    fontsize=7, weight="bold",
                    bbox=dict(facecolor="white", alpha=0.92, edgecolor="black", pad=2),
                    zorder=6)

    ax.legend(handles=[
        Line2D([0], [0], color="#b21e3a", linewidth=3.0,
               label="π_high = 0  —  (B-high) corner-existence"),
        Line2D([0], [0], color="#b21e3a", linewidth=1.1, label="π_high level curves"),
        Line2D([0], [0], color="#1f4e9b", linewidth=3.0, linestyle="--",
               label="π_bind = 0  —  (C) ratio-favored boundary"),
        Line2D([0], [0], color="#1f4e9b", linewidth=1.1, linestyle="--",
               label="π_bind level curves"),
        Line2D([0], [0], color="#6a3d9a", linewidth=1.4, linestyle=":",
               label=r"$\chi^*$ contours (tipping pt; bold $=1/2$)"),
    ], loc="upper right", fontsize=9, framealpha=0.95)

    ax.set_xlabel(r"$\sigma_{G_2}$ (Pareto scale / min. threshold for $G_2$)", fontsize=12)
    ax.set_ylabel(r"$\sigma_{G_1}$ (Pareto scale / min. threshold for $G_1$)", fontsize=12)
    ax.set_title(
        r"$\pi_{\mathrm{high}}$ and $\pi_{\mathrm{bind}}$ contours over $(\sigma_{G_2}, \sigma_{G_1})$ — Pareto Type I" + "\n"
        + subtitle + f"   |   π_low = {pi_low:+.2f} < 0 throughout (B-low holds)" + "\n"
        + r"red = (B-high) fails (no corner)   ·   amber = (C) fails ($G_1$-favored)   ·   green = (C) holds ($G_2$-favored)",
        fontsize=10,
    )
    ax.set_xlim(SIG.min(), SIG.max())
    ax.set_ylim(SIG.min(), SIG.max())
    plt.tight_layout()

    here = os.path.dirname(os.path.abspath(__file__))
    out = os.path.join(here, "..", "figures", fname)
    os.makedirs(os.path.dirname(out), exist_ok=True)
    plt.savefig(out, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"saved: {os.path.normpath(out)}")


if __name__ == "__main__":
    make_panel(2.0, 0.8, 0.3, 1.0, +0.1, "phase_diagram_pareto_favorable.png",
               r"alpha=2, a=0.8, b=0.3, d=1.0, $u_d$=+0.1 (favorable)")
    make_panel(2.0, 0.8, 0.3, 1.0, -0.1, "phase_diagram_pareto_worst_case.png",
               r"alpha=2, a=0.8, b=0.3, d=1.0, $u_d$=-0.1 (worst-case, best $\neq$ harmless)")
    make_panel(2.0, 0.8, 0.8, 1.0, +0.1, "phase_diagram_pareto_symmetric.png",
               r"alpha=2, a=0.8, b=0.8, d=1.0, $u_d$=+0.1 (symmetric levers)")
