"""
Cross-prior robustness, Fréchet (extreme-value type II) family: the Hill basin geometry
recomputed with the Fréchet survival function. The x and y axes are the Fréchet SCALE
parameters s of G2 and G1, the analog of the Hill (K_G2, K_G1) plane.

Shape parameter (justification). Fréchet's extra parameter is the tail index alpha. We
fix alpha = 2 to match the Hill working point n = 2: the Fréchet tail F_bar(X) =
1 - exp(-(s/X)^alpha) ~ (s/X)^alpha for large X (since 1 - e^{-u} ~ u), so it decays as
X^{-alpha}, and alpha = n = 2 gives the same polynomial tail-heaviness (~ X^{-2}) as
Hill. With tail-heaviness held fixed, the diagram isolates the effect of the body's
functional form, with the scale on the axes.

Fréchet is the natural unimodal analog of Hill: its density has an interior mode at
s (alpha/(alpha+1))^{1/alpha}, and the single-family Q5 results (Lean lemmas
frechetPairSum_monotoneOn for Regime II and regimeIII_interior_critical_frechet for
Regime III) place the centro-symmetric pair-sum maximum either at X = 1/2 (large scale,
Regime II) or at an interior critical point (small scale, Regime III) -- the same two
regimes as Hill. The Brent-on-W' maximizer locates whichever applies.

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
Hill (K) panels, where median = K exactly. The Fréchet median is s / (ln 2)^{1/alpha},
so s ranges over [0.05, 3] * (ln 2)^{1/alpha} ~ [0.042, 2.50] for alpha = 2. This fixes
body LOCATION the same way alpha = 2 fixes tail HEAVINESS; the axes then carry the
per-genie scale. Reference points A-D and the working points are illustrative, not
calibrated.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from scipy.optimize import brentq
import os

alpha = 2.0     # tail index; fixed at the Hill working point n = 2 (matched far tail)
d     = 1.0
SAL_LO, SAL_HI = 0.05, 3.0                # Hill median window (median = K) the others match
MED   = (np.log(2.0)) ** (-1.0 / alpha)   # Fréchet median = MED * s
SCALE_LO, SCALE_HI = SAL_LO / MED, SAL_HI / MED   # ~ [0.042, 2.50] for alpha=2

# --- Fréchet (EV type II) survival (tail), endpoint, pair-sum, and derivative ------
def h(chi, s):
    """Fréchet survival F_bar(chi) = 1 - exp(-(s/chi)^alpha); F_bar(0+) = 1."""
    if chi <= 0.0:
        return 1.0
    return 1.0 - np.exp(-((s / chi) ** alpha))

def g(chi, s):
    return h(chi, s) + h(1.0 - chi, s)

def sigma(s):
    """Endpoint F_bar(1) = 1 - exp(-s^alpha)."""
    return 1.0 - np.exp(-(s ** alpha))

def _h_prime(x, s):
    """d/dx F_bar(x) = -alpha s^alpha x^{-alpha-1} exp(-(s/x)^alpha); 0 at x<=0."""
    if x <= 0.0:
        return 0.0
    return -alpha * s ** alpha * x ** (-alpha - 1.0) * np.exp(-((s / x) ** alpha))

# --- Panel builder -----------------------------------------------------------------
def build_panel(a, b, u_d, tag, title_line, out_names):
    pi_low = d + u_d - b - 1.0

    def pi_high(s_G2, s_G1):
        return d + a * (1.0 - sigma(s_G1)) + u_d - 1.0 - b * sigma(s_G2)

    def F_delta(chi, s_G2, s_G1):
        return u_d + d - 1.0 + a * (1.0 - h(chi, s_G1)) - b * h(chi, s_G2)

    def chi_star(s_G2, s_G1):
        f_lo, f_hi = F_delta(1e-6, s_G2, s_G1), F_delta(1.0, s_G2, s_G1)
        if f_lo >= 0:
            return 0.0
        if f_hi <= 0:
            return np.nan
        return brentq(lambda c: F_delta(c, s_G2, s_G1), 1e-6, 1.0)

    def _W_prime(chi, s_G2, s_G1):
        g2p = _h_prime(chi, s_G2) - _h_prime(1.0 - chi, s_G2)
        g3p = _h_prime(chi, s_G1) - _h_prime(1.0 - chi, s_G1)
        return b * g2p + a * g3p

    def _W_at(chi, s_G2, s_G1):
        return b * g(chi, s_G2) + a * g(chi, s_G1)

    def _maximize_W(s_G2, s_G1):
        """Max of W(chi)=b g_G2 + a g_G1 on [0,1/2]: endpoints plus interior W'-roots.
        Regime II maximum is at 1/2; Regime III at an interior critical point that can
        sit close to 0 at small scale, so the scan is dense near the origin."""
        candidates = [0.0, 0.5]
        scan = np.concatenate([
            np.linspace(1e-6, 0.05, 48, endpoint=False),
            np.linspace(0.05, 0.5 - 1e-6, 80),
        ])
        wp = np.array([_W_prime(c, s_G2, s_G1) for c in scan])
        for i in np.where(np.diff(np.sign(wp)) != 0)[0]:
            try:
                candidates.append(brentq(_W_prime, scan[i], scan[i + 1],
                                         args=(s_G2, s_G1), xtol=1e-12))
            except ValueError:
                pass
        W_values = [_W_at(c, s_G2, s_G1) for c in candidates]
        idx = int(np.argmax(W_values))
        return candidates[idx], W_values[idx]

    def pi_bind(s_G2, s_G1):
        _, W_max = _maximize_W(s_G2, s_G1)
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
    ax.text(1.7, 1.75, r"$s_{G_2} = s_{G_1}$", color='gray', fontsize=9, rotation=45)

    points = [(0.5, 0.5, 'A'), (1.5, 1.5, 'B'), (0.5, 1.5, 'C'), (1.5, 0.5, 'D')]
    for s_G2, s_G1, name in points:
        ph, pb = pi_high(s_G2, s_G1), pi_bind(s_G2, s_G1)
        ax.plot(s_G2, s_G1, 'o', markersize=9, markerfacecolor='white',
                markeredgecolor='black', markeredgewidth=1.5, zorder=5)
        ax.annotate(f"{name}: pi_h={ph:+.2f}, pi_b={pb:+.2f}",
                    (s_G2, s_G1), xytext=(11, 9), textcoords='offset points',
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
    ax.set_xlabel(r"$s_{G_2}$ (Fréchet scale, $G_2$)", fontsize=12)
    ax.set_ylabel(r"$s_{G_1}$ (Fréchet scale, $G_1$)", fontsize=12)
    ax.set_title(
        "Fréchet (EV type II) prior  ·  " + title_line + "\n"
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
         out=["phase_diagram_frechet_favorable.png", "figure_frechet_favorable.png"]),
    dict(a=0.8, b=0.3, u_d=-0.1, tag="worst_case",
         title_line=r"worst-case 'best $\neq$ harmless' ($u_d < 0$, principal panel)",
         out=["phase_diagram_frechet_worst_case.png", "figure_frechet_worst_case.png"]),
    dict(a=0.8, b=0.8, u_d=+0.1, tag="symmetric",
         title_line="symmetric lever weights ($a/b = 1$)",
         out=["phase_diagram_frechet_symmetric.png", "figure_frechet_symmetric.png"]),
]
for p in PANELS:
    build_panel(p["a"], p["b"], p["u_d"], p["tag"], p["title_line"],
                [os.path.join(_here, p["out"][0])])   # per-prior panel; the cross-prior grid is the headline figure
