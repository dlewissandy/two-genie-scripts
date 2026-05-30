"""
Cross-prior robustness, Lomax (Pareto Type II) family: the Hill basin geometry
recomputed with the Lomax survival function. The x and y axes are the Lomax SCALE
parameters lambda of G2 and G1, the analog of the Hill (K_G2, K_G1) plane.

Shape parameter (justification). Lomax's extra parameter is the tail index alpha. We
fix alpha = 2 to match the Hill working point n = 2: Lomax's tail F_bar(X) =
(1 + X/lambda)^{-alpha} ~ (X/lambda)^{-alpha} decays as X^{-alpha}, so alpha = n = 2
gives the same polynomial tail-heaviness (~ X^{-2}) as Hill. With tail-heaviness held
fixed across families, the diagram isolates the effect of the body's functional form,
with the scale on the axes.

Unlike Hill (and Fréchet), the Lomax density is monotone decreasing for every alpha:
there is no interior mode. The single-family Q5 result (Lean lemma
lomaxPairSum_antitoneOn) shows the centro-symmetric pair-sum g(X) = F_bar(X) +
F_bar(1-X) is antitone on [0, 1/2], so its maximum, and that of any nonnegative-weighted
sum b g_G2 + a g_G1, is attained at X = 0. The Brent-on-W' maximizer recovers this
(W' < 0 throughout, so the maximum falls on the X = 0 endpoint).

Audit parameters (a, b, d, u_d) describe the mechanism, not the prior; held at the same
three Hill working points:
  favorable   : a=0.8, b=0.3, d=1.0, u_d=+0.1
  worst-case  : a=0.8, b=0.3, d=1.0, u_d=-0.1   ("best != harmless", principal panel)
  symmetric   : a=0.8, b=0.8, d=1.0, u_d=+0.1   (a/b = 1)

Region <-> named-inequality map (as in the Hill panels):
  red   (pi_high < 0)              : (B-high) fails -- no stable all-G2 corner
  amber (pi_high>=0, pi_bind<0)    : (B-high) holds, (C) fails -- bistable, G1-favored
  green (pi_bind >= 0)             : (C) holds -- ratio-favored for G2
  (B-low): pi_low = d+u_d-b-1 < 0, X-independent, holds throughout each window.

Plotting window (matched-median criterion). The scale parameters of different families
are not numerically comparable, so the axis range is fixed by a uniform rule: span the
scale so the family's MEDIAN threshold sweeps the same [0.05, 3] salience window as the
Hill (K) panels, where median = K exactly. The Lomax median is (2^{1/alpha} - 1) lambda,
so lambda ranges over [0.05, 3] / (2^{1/alpha} - 1) ~ [0.12, 7.25] for alpha = 2. This
fixes body LOCATION the same way alpha = 2 fixes tail HEAVINESS; the axes then carry the
per-genie scale. (Lomax's endpoint F_bar(1) saturates slowly, so its no-corner regime
sits at larger scale than Hill's; the matched-median window is what brings the full
red/amber/green structure into view.) Reference points A-D and the working points are
illustrative, not calibrated.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from scipy.optimize import brentq
import os

alpha = 2.0     # tail index; fixed at the Hill working point n = 2 (matched far tail)
d     = 1.0
SAL_LO, SAL_HI = 0.05, 3.0          # Hill median window (median = K) the others are matched to
MED   = 2.0 ** (1.0 / alpha) - 1.0  # Lomax median = MED * lambda
SCALE_LO, SCALE_HI = SAL_LO / MED, SAL_HI / MED   # ~ [0.12, 7.25] for alpha=2

# --- Lomax (Pareto II) survival (tail), endpoint, pair-sum, and derivative ---------
def h(chi, lam):
    """Lomax survival F_bar(chi) = (1 + chi/lambda)^{-alpha}."""
    return (1.0 + chi / lam) ** (-alpha)

def g(chi, lam):
    return h(chi, lam) + h(1.0 - chi, lam)

def sigma(lam):
    """Endpoint F_bar(1) = (1 + 1/lambda)^{-alpha}."""
    return (1.0 + 1.0 / lam) ** (-alpha)

def _h_prime(x, lam):
    """d/dx F_bar(x) = -(alpha/lambda)(1 + x/lambda)^{-alpha-1}."""
    return -(alpha / lam) * (1.0 + x / lam) ** (-alpha - 1.0)

# --- Panel builder -----------------------------------------------------------------
def build_panel(a, b, u_d, tag, title_line, out_names):
    pi_low = d + u_d - b - 1.0

    def pi_high(l_G2, l_G1):
        return d + a * (1.0 - sigma(l_G1)) + u_d - 1.0 - b * sigma(l_G2)

    def F_delta(chi, l_G2, l_G1):
        return u_d + d - 1.0 + a * (1.0 - h(chi, l_G1)) - b * h(chi, l_G2)

    def chi_star(l_G2, l_G1):
        f_lo, f_hi = F_delta(1e-6, l_G2, l_G1), F_delta(1.0, l_G2, l_G1)
        if f_lo >= 0:
            return 0.0
        if f_hi <= 0:
            return np.nan
        return brentq(lambda c: F_delta(c, l_G2, l_G1), 1e-6, 1.0)

    def _W_prime(chi, l_G2, l_G1):
        g2p = _h_prime(chi, l_G2) - _h_prime(1.0 - chi, l_G2)
        g3p = _h_prime(chi, l_G1) - _h_prime(1.0 - chi, l_G1)
        return b * g2p + a * g3p

    def _W_at(chi, l_G2, l_G1):
        return b * g(chi, l_G2) + a * g(chi, l_G1)

    def _maximize_W(l_G2, l_G1):
        """Max of W(chi)=b g_G2 + a g_G1 on [0,1/2]. The pair-sum is antitone (Q5),
        so the maximum sits at X=0; the scan/refine still runs as a numerical check."""
        candidates = [0.0, 0.5]
        scan = np.linspace(1e-6, 0.5 - 1e-6, 64)
        wp = np.array([_W_prime(c, l_G2, l_G1) for c in scan])
        for i in np.where(np.diff(np.sign(wp)) != 0)[0]:
            try:
                candidates.append(brentq(_W_prime, scan[i], scan[i + 1],
                                         args=(l_G2, l_G1), xtol=1e-12))
            except ValueError:
                pass
        W_values = [_W_at(c, l_G2, l_G1) for c in candidates]
        idx = int(np.argmax(W_values))
        return candidates[idx], W_values[idx]

    def pi_bind(l_G2, l_G1):
        _, W_max = _maximize_W(l_G2, l_G1)
        return 2.0 * (u_d + d - 1.0 + a) - W_max

    rng = np.linspace(SCALE_LO, SCALE_HI, 220)
    XG2, XG1 = np.meshgrid(rng, rng)
    phi_h = np.vectorize(pi_high)(XG2, XG1)
    phi_b = np.vectorize(pi_bind)(XG2, XG1)
    chi_grid = np.vectorize(chi_star)(XG2, XG1)

    fig, ax = plt.subplots(figsize=(10, 9))
    region = np.zeros_like(phi_h)
    region[(phi_h < 0)] = 0
    region[(phi_h >= 0) & (phi_b < 0)] = 1
    region[(phi_b >= 0)] = 2
    ax.imshow(region, origin='lower',
              extent=[rng.min(), rng.max(), rng.min(), rng.max()],
              cmap=ListedColormap(['#fad9d9', '#fdf0c9', '#dbecda']),
              vmin=-0.5, vmax=2.5, aspect='equal', alpha=0.55)

    cs_h = ax.contour(XG2, XG1, phi_h, levels=7, colors='#b21e3a',
                      linewidths=1.1, alpha=0.9)
    ax.clabel(cs_h, inline=True, fontsize=8, fmt='%.2f')
    cs_h0 = ax.contour(XG2, XG1, phi_h, levels=[0], colors='#b21e3a', linewidths=3.0)
    ax.clabel(cs_h0, inline=True, fontsize=10, fmt={0: 'pi_high = 0'})

    cs_b = ax.contour(XG2, XG1, phi_b, levels=7, colors='#1f4e9b',
                      linewidths=1.1, alpha=0.9, linestyles='--')
    ax.clabel(cs_b, inline=True, fontsize=8, fmt='%.2f')
    cs_b0 = ax.contour(XG2, XG1, phi_b, levels=[0], colors='#1f4e9b',
                       linewidths=3.0, linestyles='--')
    ax.clabel(cs_b0, inline=True, fontsize=10, fmt={0: 'pi_bind = 0'})

    if np.any(np.isfinite(chi_grid)):
        cs_chi = ax.contour(XG2, XG1, chi_grid, levels=[0.15, 0.2, 0.3, 0.4, 0.45],
                            colors='#6a3d9a', linewidths=1.0, linestyles=':', alpha=0.95)
        ax.clabel(cs_chi, inline=True, fontsize=8, fmt=r'$\chi^*=%.2f$')
        cs_chi12 = ax.contour(XG2, XG1, chi_grid, levels=[0.5],
                              colors='#6a3d9a', linewidths=3.0, linestyles=':')
        ax.clabel(cs_chi12, inline=True, fontsize=9, fmt={0.5: r'$\chi^*=1/2$'})

    ax.plot(rng, rng, color='gray', linestyle='-', linewidth=1.0, alpha=0.4)
    ax.text(5.0, 5.2, r"$\lambda_{G_2} = \lambda_{G_1}$", color='gray',
            fontsize=9, rotation=45)

    points = [(1.0, 1.0, 'A'), (4.0, 4.0, 'B'), (1.0, 4.0, 'C'), (4.0, 1.0, 'D')]
    for l_G2, l_G1, name in points:
        ph, pb = pi_high(l_G2, l_G1), pi_bind(l_G2, l_G1)
        ax.plot(l_G2, l_G1, 'o', markersize=9, markerfacecolor='white',
                markeredgecolor='black', markeredgewidth=1.5, zorder=5)
        ax.annotate(f"{name}: pi_h={ph:+.2f}, pi_b={pb:+.2f}",
                    (l_G2, l_G1), xytext=(11, 9), textcoords='offset points',
                    fontsize=7, weight='bold',
                    bbox=dict(facecolor='white', alpha=0.92, edgecolor='black', pad=2),
                    zorder=6)

    legend_elems = [
        Line2D([0], [0], color='#b21e3a', linewidth=3.0,
               label='pi_high = 0  —  (B-high) corner-existence'),
        Line2D([0], [0], color='#b21e3a', linewidth=1.1, label='pi_high level curves'),
        Line2D([0], [0], color='#1f4e9b', linewidth=3.0, linestyle='--',
               label='pi_bind = 0  —  (C) ratio-favored boundary'),
        Line2D([0], [0], color='#1f4e9b', linewidth=1.1, linestyle='--',
               label='pi_bind level curves'),
        Line2D([0], [0], color='#6a3d9a', linewidth=1.4, linestyle=':',
               label=r'$\chi^*$ contours (tipping pt; bold $=1/2$)'),
    ]
    ax.legend(handles=legend_elems, loc='upper right', fontsize=9, framealpha=0.95)
    ax.set_xlabel(r"$\lambda_{G_2}$ (Lomax scale, $G_2$)", fontsize=12)
    ax.set_ylabel(r"$\lambda_{G_1}$ (Lomax scale, $G_1$)", fontsize=12)
    ax.set_title(
        "Lomax (Pareto II) prior  ·  " + title_line + "\n"
        rf"$\alpha$ = {alpha:g} (far-tail index, matched to Hill $n=2$),  "
        f"a = {a}, b = {b}, d = {d}, u_d = {u_d:+.1f}   |   "
        f"pi_low = {pi_low:+.2f} < 0 (B-low holds)\n"
        r"red = (B-high) fails (no corner)   ·   amber = (C) fails ($G_1$-favored)   ·   green = (C) holds ($G_2$-favored)",
        fontsize=10,
    )
    ax.set_xlim(rng.min(), rng.max())
    ax.set_ylim(rng.min(), rng.max())
    plt.tight_layout()
    for name in out_names:
        plt.savefig(name, dpi=150, bbox_inches='tight')
        print(f"saved: {os.path.normpath(name)}")
    plt.close(fig)


_here = os.path.dirname(os.path.abspath(__file__))
PANELS = [
    dict(a=0.8, b=0.3, u_d=+0.1, tag="favorable",
         title_line="favorable ($u_d > 0$)",
         out=["phase_diagram_lomax_favorable.png", "figure_lomax_favorable.png"]),
    dict(a=0.8, b=0.3, u_d=-0.1, tag="worst_case",
         title_line=r"worst-case 'best $\neq$ harmless' ($u_d < 0$, principal panel)",
         out=["phase_diagram_lomax_worst_case.png", "figure_lomax_worst_case.png"]),
    dict(a=0.8, b=0.8, u_d=+0.1, tag="symmetric",
         title_line="symmetric lever weights ($a/b = 1$)",
         out=["phase_diagram_lomax_symmetric.png", "figure_lomax_symmetric.png"]),
]
for p in PANELS:
    build_panel(p["a"], p["b"], p["u_d"], p["tag"], p["title_line"],
                [os.path.join(_here, p["out"][0])])   # per-prior panel; the cross-prior grid is the headline figure
