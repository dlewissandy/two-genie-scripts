"""
Cross-prior phase-diagram GRID: a single 4 x 3 matrix of phase diagrams.

  rows  (y / prior)      : Hill (log-logistic), Pareto Type I, Lomax (Pareto II), Fréchet
  cols  (x / parameters) : favorable (u_d=+0.1), worst-case (u_d=-0.1), symmetric (a/b=1)

Each cell is the phase diagram of the corresponding family at the corresponding audit
working point, stripped to its essentials for legibility in the grid: region shading
(red / amber / green), the bold zero-contours pi_high = 0 and pi_bind = 0, the chi*
tipping-point contours (bold at chi* = 1/2), and the equal-scale diagonal. Reference
points, per-panel titles, legends, and inline contour labels are removed; the shared
legend and the row/column labels carry that information once for the whole figure.

Within every panel the horizontal axis is the G2 scale and the vertical axis is the G1
scale; the per-row scale symbol (K, x_m, lambda, s) is given in the row label.

Comparability (identical to the standalone per-family scripts):
  - shape: each non-Hill family's tail index is fixed at alpha = 2 so the far tail
    matches the Hill working point n = 2 (all families decay ~ X^{-2}); Hill uses n = 2.
  - scale range: matched-median -- each scale axis spans the range over which the
    family's median threshold sweeps the same [0.05, 3] salience window as the Hill
    K-panels (median = K for Hill), so x_m, lambda, s ranges differ but mean the same.

The binding maximum W_max = max_{X in [0,1/2]}[b g_G2 + a g_G1] is located by a Brent
maximizer (dense scan near 0 for the unimodal interior-peak regimes; explicit kink
candidates x_m for Pareto), matching the per-family (Q5) maximum-location lemmas. A
self-check block at the bottom asserts F_bar(0)=1, monotone tails, and agreement of the
maximizer with a brute-force grid maximum before any figure is drawn.

Writes phase_diagram_grid.png next to this script. If the environment variable
MANUSCRIPT_FIG_DIR is set, also writes a copy named figure_prior_grid.png into
that directory (used to refresh a manuscript's embedded figure).
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from scipy.optimize import brentq
import os

ALPHA = 2.0   # tail index for the non-Hill families; matched to Hill n = 2
N_HILL = 2    # Hill exponent
D = 1.0       # audit substrate level, common to all panels
SAL_LO, SAL_HI = 0.05, 3.0   # Hill median window (median = K) the others are matched to

# --- Family definitions: tail F_bar(chi; scale), endpoint F_bar(1), derivative -----
# Each family is a dict carrying the survival function, its endpoint and derivative,
# the matched-median scale range, the kink locations to add as maximizer candidates,
# and labels. Functions are copied verbatim from the standalone per-family scripts.

def _hill_h(chi, K):    return K ** N_HILL / (K ** N_HILL + chi ** N_HILL)
def _hill_sigma(K):     return K ** N_HILL / (K ** N_HILL + 1.0)
def _hill_hp(x, K):     return -N_HILL * K ** N_HILL * x ** (N_HILL - 1) / (K ** N_HILL + x ** N_HILL) ** 2

def _pareto_h(chi, xm): return 1.0 if chi <= xm else (xm / chi) ** ALPHA
def _pareto_sigma(xm):  return 1.0 if xm >= 1.0 else xm ** ALPHA
def _pareto_hp(x, xm):  return 0.0 if x <= xm else -ALPHA * xm ** ALPHA * x ** (-ALPHA - 1.0)

def _lomax_h(chi, lam): return (1.0 + chi / lam) ** (-ALPHA)
def _lomax_sigma(lam):  return (1.0 + 1.0 / lam) ** (-ALPHA)
def _lomax_hp(x, lam):  return -(ALPHA / lam) * (1.0 + x / lam) ** (-ALPHA - 1.0)

def _frechet_h(chi, s): return 1.0 if chi <= 0.0 else 1.0 - np.exp(-((s / chi) ** ALPHA))
def _frechet_sigma(s):  return 1.0 - np.exp(-(s ** ALPHA))
def _frechet_hp(x, s):  return 0.0 if x <= 0.0 else -ALPHA * s ** ALPHA * x ** (-ALPHA - 1.0) * np.exp(-((s / x) ** ALPHA))

def _range(med_per_scale):
    """Matched-median scale range: scale = salience / (median-per-unit-scale)."""
    return SAL_LO / med_per_scale, SAL_HI / med_per_scale

FAMILIES = [
    dict(name="Hill", scale=r"K", g2=r"K_{G_2}", h=_hill_h, sigma=_hill_sigma, hp=_hill_hp,
         rng=(SAL_LO, SAL_HI), kinks=False),                      # median = K
    dict(name="Pareto", scale=r"x_m", g2=r"x_{m,G_2}", h=_pareto_h, sigma=_pareto_sigma, hp=_pareto_hp,
         rng=_range(2.0 ** (1.0 / ALPHA)), kinks=True),           # median = 2^(1/a) x_m
    dict(name="Lomax", scale=r"\lambda", g2=r"\lambda_{G_2}", h=_lomax_h, sigma=_lomax_sigma, hp=_lomax_hp,
         rng=_range(2.0 ** (1.0 / ALPHA) - 1.0), kinks=False),    # median = (2^(1/a)-1) lambda
    dict(name="Fréchet", scale=r"s", g2=r"s_{G_2}", h=_frechet_h, sigma=_frechet_sigma, hp=_frechet_hp,
         rng=_range((np.log(2.0)) ** (-1.0 / ALPHA)), kinks=False),   # median = s/(ln2)^(1/a)
]

PARAMS = [
    dict(tag="favorable", a=0.8, b=0.3, u_d=+0.1, title=r"$G_2$ more useful: $u_d=+0.1$"),
    dict(tag="g2_less_useful", a=0.8, b=0.3, u_d=-0.1, title=r"$G_2$ less useful: $u_d=-0.1$"),
    dict(tag="symmetric", a=0.8, b=0.8, u_d=+0.1, title=r"Symmetric levers: $a/b=1$"),
]

# --- Generic basin functions -------------------------------------------------------
def pi_high(fam, p, s_G2, s_G1):
    return D + p["a"] * (1.0 - fam["sigma"](s_G1)) + p["u_d"] - 1.0 - p["b"] * fam["sigma"](s_G2)

def F_delta(fam, p, chi, s_G2, s_G1):
    return p["u_d"] + D - 1.0 + p["a"] * (1.0 - fam["h"](chi, s_G1)) - p["b"] * fam["h"](chi, s_G2)

def chi_star(fam, p, s_G2, s_G1):
    f_lo = F_delta(fam, p, 1e-6, s_G2, s_G1)
    f_hi = F_delta(fam, p, 1.0, s_G2, s_G1)
    if f_lo >= 0:
        return 0.0
    if f_hi <= 0:
        return np.nan
    return brentq(lambda c: F_delta(fam, p, c, s_G2, s_G1), 1e-6, 1.0)

def _W_prime(fam, p, chi, s_G2, s_G1):
    hp = fam["hp"]
    g2p = hp(chi, s_G2) - hp(1.0 - chi, s_G2)
    g3p = hp(chi, s_G1) - hp(1.0 - chi, s_G1)
    return p["b"] * g2p + p["a"] * g3p

def _W_at(fam, p, chi, s_G2, s_G1):
    h = fam["h"]
    g2 = h(chi, s_G2) + h(1.0 - chi, s_G2)
    g3 = h(chi, s_G1) + h(1.0 - chi, s_G1)
    return p["b"] * g2 + p["a"] * g3

def maximize_W(fam, p, s_G2, s_G1):
    """Max of W on [0,1/2]: endpoints, family kink points (Pareto x_m), and refined
    interior W'-roots. Dense scan near 0 catches Regime III interior peaks at small scale."""
    candidates = [0.0, 0.5]
    if fam["kinks"]:
        for sc in (s_G2, s_G1):
            if 0.0 < sc < 0.5:
                candidates.append(sc)
    scan = np.concatenate([np.linspace(1e-6, 0.05, 48, endpoint=False),
                           np.linspace(0.05, 0.5 - 1e-6, 80)])
    wp = np.array([_W_prime(fam, p, c, s_G2, s_G1) for c in scan])
    for i in np.where(np.diff(np.sign(wp)) != 0)[0]:
        try:
            candidates.append(brentq(lambda c: _W_prime(fam, p, c, s_G2, s_G1),
                                     scan[i], scan[i + 1], xtol=1e-12))
        except ValueError:
            pass
    vals = [_W_at(fam, p, c, s_G2, s_G1) for c in candidates]
    idx = int(np.argmax(vals))
    return candidates[idx], vals[idx]

def pi_bind(fam, p, s_G2, s_G1):
    _, W_max = maximize_W(fam, p, s_G2, s_G1)
    return 2.0 * (p["u_d"] + D - 1.0 + p["a"]) - W_max

# --- Self-check: tails and maximizer agree with first principles -------------------
def _self_check():
    for fam in FAMILIES:
        lo, hi = fam["rng"]
        for sc in (lo, 0.5 * (lo + hi), hi):
            assert abs(fam["h"](0.0, sc) - 1.0) < 1e-9, f"{fam['name']}: F_bar(0)!=1"
            xs = np.linspace(1e-4, 1.0, 400)
            hv = np.array([fam["h"](x, sc) for x in xs])
            assert np.all(np.diff(hv) <= 1e-9), f"{fam['name']}: tail not antitone at scale {sc}"
        # maximizer vs brute force at a couple of (s_G2, s_G1) points
        for p in (PARAMS[0], PARAMS[1]):
            for (a2, a1) in [(lo, lo), (0.5 * (lo + hi), hi), (hi, lo)]:
                arg, Wm = maximize_W(fam, p, a2, a1)
                grid = np.linspace(0.0, 0.5, 6001)
                Wb = max(_W_at(fam, p, c, a2, a1) for c in grid)
                assert Wm >= Wb - 5e-4, f"{fam['name']} {p['tag']}: maximizer {Wm} < brute {Wb}"
    print("self-check OK: tails normalized & antitone; W maximizer matches brute force.")


def build_grid():
  # --- Build the 4 x 3 grid --------------------------------------------------------
  REGION_CMAP = ListedColormap(['#fad9d9', '#fdf0c9', '#dbecda'])  # red, amber, green
  NGRID = 200

  fig, axes = plt.subplots(len(FAMILIES), len(PARAMS), figsize=(9.5, 12.6))

  for r, fam in enumerate(FAMILIES):
    lo, hi = fam["rng"]
    rng = np.linspace(lo, hi, NGRID)
    XG2, XG1 = np.meshgrid(rng, rng)
    for c, p in enumerate(PARAMS):
        ax = axes[r, c]
        phi_h = np.vectorize(lambda x2, x1: pi_high(fam, p, x2, x1))(XG2, XG1)
        phi_b = np.vectorize(lambda x2, x1: pi_bind(fam, p, x2, x1))(XG2, XG1)
        chi_g = np.vectorize(lambda x2, x1: chi_star(fam, p, x2, x1))(XG2, XG1)

        region = np.zeros_like(phi_h)
        region[(phi_h >= 0) & (phi_b < 0)] = 1
        region[(phi_b >= 0)] = 2
        ax.imshow(region, origin='lower', extent=[lo, hi, lo, hi],
                  cmap=REGION_CMAP, vmin=-0.5, vmax=2.5, aspect='auto', alpha=0.6)

        ax.contour(XG2, XG1, phi_h, levels=[0], colors='#b21e3a', linewidths=2.2)
        ax.contour(XG2, XG1, phi_b, levels=[0], colors='#1f4e9b',
                   linewidths=2.2, linestyles='--')
        if np.any(np.isfinite(chi_g)):
            cs_chi = ax.contour(XG2, XG1, chi_g, levels=[0.15, 0.2, 0.3, 0.4],
                                colors='#6a3d9a', linewidths=0.8, linestyles=':', alpha=0.95)
            ax.clabel(cs_chi, inline=True, fontsize=6, fmt=r'$\chi^*\!=\!%.2f$')
            cs_chi12 = ax.contour(XG2, XG1, chi_g, levels=[0.5], colors='#6a3d9a',
                                  linewidths=2.2, linestyles=':')
            ax.clabel(cs_chi12, inline=True, fontsize=7, fmt={0.5: r'$\chi^*\!=\!1/2$'})
        ax.plot(rng, rng, color='gray', linewidth=0.8, alpha=0.45)

        ax.set_xlim(lo, hi)
        ax.set_ylim(lo, hi)
        ax.tick_params(labelsize=7)
        ax.set_xticks(np.round(np.linspace(lo, hi, 4), 2))
        ax.set_yticks(np.round(np.linspace(lo, hi, 4), 2))

        if r == 0:
            ax.set_title(p["title"], fontsize=12, fontweight='bold', pad=8)
        if c == 0:
            ax.set_ylabel(f"{fam['name']}\n(scale ${fam['scale']}$)",
                          fontsize=11, fontweight='bold', labelpad=6)

  # --- Shared legend + figure title ------------------------------------------------
  legend_elems = [
      Patch(facecolor='#dbecda', edgecolor='gray', label=r'cooperative basin ($G_2$ wins)'),
      Patch(facecolor='#fdf0c9', edgecolor='gray', label=r'$G_1$ wins (bistable)'),
      Patch(facecolor='#fad9d9', edgecolor='gray', label=r'no stable $G_2$ corner'),
      Line2D([0], [0], color='#b21e3a', linewidth=2.2, label=r'$\pi_{\mathrm{high}}=0$: corner edge'),
      Line2D([0], [0], color='#1f4e9b', linewidth=2.2, linestyle='--', label=r'$\pi_{\mathrm{bind}}=0$: basin frontier'),
      Line2D([0], [0], color='#6a3d9a', linewidth=2.2, linestyle=':', label=r'$\chi^*=1/2$ limit'),
      Line2D([0], [0], color='#6a3d9a', linewidth=0.8, linestyle=':', label=r'$\chi^*$ isoclines'),
      Line2D([0], [0], color='gray', linewidth=0.8, label=r'equal scales $G_2=G_1$'),
  ]
  fig.legend(handles=legend_elems, loc='lower center', ncol=4, fontsize=9,
             framealpha=0.95, bbox_to_anchor=(0.5, 0.005))

  fig.subplots_adjust(left=0.09, right=0.985, top=0.945, bottom=0.085,
                      wspace=0.22, hspace=0.20)

  _here = os.path.dirname(os.path.abspath(__file__))
  _outs = [os.path.join(_here, "phase_diagram_grid.png")]
  _mdir = os.environ.get("MANUSCRIPT_FIG_DIR")
  if _mdir:
      _outs.append(os.path.join(_mdir, "figure_prior_grid.png"))
  for _out in _outs:
      fig.savefig(_out, dpi=160, bbox_inches='tight')
      print(f"saved: {os.path.normpath(_out)}")


if __name__ == "__main__":
    _self_check()
    build_grid()
