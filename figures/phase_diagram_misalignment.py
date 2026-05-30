"""
Figure 1 of the darker-side extension: the (u_d, theta_lambda) plane and the
regime INVERSION.

Holds a representative community fixed (per family, median threshold m) and sweeps the
private-usefulness differential u_d (x) against the audit-misalignment angle theta_lambda
(y). Misalignment enters only through the audit substrate d, via the sec 3.1a
parametrization

    d(theta) = d0 * (cos theta - kappa * sin theta),      kappa = leak ratio,

so W_agg = M*d, and W_agg = 0 exactly on the horizontal line theta = theta_crit =
arctan(1/kappa) (independent of u_d). Everything downstream (u_w = u_d + d, pi_high,
pi_bind) is the existing eq. (3) machinery, reused from phase_diagram_grid.

Shading:
  gray   : no cooperative basin (pi_bind < 0)
  green  : basin exists AND d >= 0 (theta <= theta_crit): selection tracks real welfare
  red    : basin exists AND d < 0  (theta >  theta_crit): LAUNDERING -- G2 adopted and
           favored while W_agg < 0 (community-harm-increasing)

The point of the figure: the red laundering wedge sits only at u_d > u_d_min > 0. A
misaligned audit fails LOUD at u_d < 0 (no basin, not adopted) and fails QUIET at u_d > 0
(adopted while harmful). u_d_min at the W_agg=0 line is 1 - a + W_max/2 >= 0.2 > 0.

Writes phase_diagram_misalignment.png next to this script. If MANUSCRIPT_FIG_DIR
is set, also writes a copy named figure_misalignment.png into that directory.
"""

import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

import phase_diagram_grid as pg   # FAMILIES, maximize_W, SAL_LO

# --- misalignment parametrization (sec 3.1a) -----------------------------------
D0 = 1.0          # aligned community-metric welfare d_0 (the old hardcoded D)
KAPPA = 1.0       # leak ratio; theta_crit = arctan(1/kappa) = 45 deg here
THETA_CRIT = np.arctan(1.0 / KAPPA)

A, B = 0.8, 0.3   # perception levers, the favorable working point of the grid
MEDIAN = 0.3      # representative community: median acceptance threshold

U_LO, U_HI = -0.6, 1.6
NGRID = 240


def d_of_theta(theta):
    return D0 * (np.cos(theta) - KAPPA * np.sin(theta))


def fam_scale(fam):
    """Scale giving median threshold = MEDIAN. med_per_scale = SAL_LO / range_lo."""
    lo = fam["rng"][0]
    med_per_scale = pg.SAL_LO / lo
    return MEDIAN / med_per_scale


def panel(ax, fam, show_x, show_y):
    sc = fam_scale(fam)
    sig1, sig2 = fam["sigma"](sc), fam["sigma"](sc)          # s_G1 = s_G2 = sc
    _, W_max = pg.maximize_W(fam, {"a": A, "b": B, "u_d": 0.0}, sc, sc)  # indep of u_d, d
    u_d_min = 1.0 - A + 0.5 * W_max                          # CSP frontier at d = 0

    us = np.linspace(U_LO, U_HI, NGRID)
    ths = np.linspace(0.0, np.pi / 2, NGRID)
    U, TH = np.meshgrid(us, ths)
    dvals = d_of_theta(TH)

    # eq. (3) basin conditions with d = d(theta), at the fixed community (sc, sc)
    pi_high = dvals + A * (1.0 - sig1) + U - 1.0 - B * sig2
    pi_bind = 2.0 * (U + dvals - 1.0 + A) - W_max
    basin = pi_bind >= 0.0
    laundering = basin & (dvals < 0.0)                       # theta > theta_crit

    region = np.zeros_like(U)            # 0 gray (no basin)
    region[basin] = 1                    # 1 green (basin, real welfare)
    region[laundering] = 2               # 2 red  (basin, laundering)
    cmap = ListedColormap(['#ededed', '#dbecda', '#f4b8b0'])
    ax.imshow(region, origin='lower', extent=[U_LO, U_HI, 0.0, np.pi / 2],
              cmap=cmap, vmin=-0.5, vmax=2.5, aspect='auto')

    # W_agg = 0 line (theta_crit) and the basin frontier
    ax.axhline(THETA_CRIT, color='#1f4e9b', lw=2.0, ls='--')
    ax.contour(U, TH, pi_bind, levels=[0], colors='#b21e3a', linewidths=2.0)
    ax.axvline(0.0, color='gray', lw=0.8, alpha=0.6)
    ax.axvline(1.0, color='#222', lw=1.1, ls=':', alpha=0.8)          # u_d = 1 reference
    # u_d_min: laundering threshold, where the frontier meets the W_agg=0 line
    if U_LO < u_d_min < U_HI:
        ax.axvline(u_d_min, color='#b21e3a', lw=1.0, ls='-', alpha=0.45)
        ax.plot([u_d_min], [THETA_CRIT], 'o', color='#b21e3a', ms=5, zorder=5)
        ax.text(u_d_min, 0.04, rf"$u_d^{{\min}}\!=\!{u_d_min:.2f}$", fontsize=7,
                color='#b21e3a', ha='center', va='bottom')

    ax.set_xlim(U_LO, U_HI)
    ax.set_ylim(0.0, np.pi / 2)
    ax.set_yticks([0, np.pi / 8, np.pi / 4, 3 * np.pi / 8, np.pi / 2])
    ax.set_yticklabels(['0', r'$\pi/8$', r'$\pi/4$', r'$3\pi/8$', r'$\pi/2$'], fontsize=8)
    ax.tick_params(labelsize=8)
    ax.set_title(rf"{fam['name']}  ($\tilde\theta$ median $={MEDIAN}$)", fontsize=11)
    if show_x:
        ax.set_xlabel(r"private usefulness $u_d$", fontsize=10)
    if show_y:
        ax.set_ylabel(r"misalignment $\theta_\lambda$", fontsize=10)
    return u_d_min


def main():
    # u_d_min is ~prior-independent (1 - a + W_max/2, endpoint-dominated), so one
    # representative family suffices; the per-family basin SHAPE lives in the basin grid.
    fig, ax = plt.subplots(1, 1, figsize=(7.0, 5.6))
    u_mins = [panel(ax, pg.FAMILIES[0], show_x=True, show_y=True)]
    ax.set_title("")   # single panel: the suptitle carries the labelling

    legend = [
        Patch(facecolor='#dbecda', edgecolor='gray', label='basin exists, tracks welfare ($d\\geq0$)'),
        Patch(facecolor='#f4b8b0', edgecolor='gray', label='LAUNDERING: basin exists, $W_{agg}<0$'),
        Patch(facecolor='#ededed', edgecolor='gray', label='no basin (not adopted)'),
        Line2D([0], [0], color='#1f4e9b', lw=2.0, ls='--',
               label=r'$W_{agg}=0$  ($\theta_\lambda=\theta_\lambda^{\mathrm{crit}}$)'),
        Line2D([0], [0], color='#b21e3a', lw=2.0, label=r'basin frontier ($\pi_{\mathrm{bind}}=0$)'),
        Line2D([0], [0], color='#b21e3a', lw=1.0, label=r'$u_d^{\min}$ (laundering threshold)'),
        Line2D([0], [0], color='#222', lw=1.1, ls=':', label=r'$u_d=1$ reference'),
    ]
    fig.legend(handles=legend, loc='lower center', ncol=3, fontsize=9,
               framealpha=0.95, bbox_to_anchor=(0.5, 0.0))
    fig.suptitle(
        "The regime inversion (Hill, representative; $u_d^{\\min}$ nearly prior-independent)\n"
        rf"laundering ($W_{{agg}}<0$ yet basin-favored) only at $u_d>u_d^{{\min}}$; "
        rf"fail-loud at $u_d<u_d^{{\min}}$",
        fontsize=11, y=1.0)
    fig.subplots_adjust(left=0.10, right=0.985, top=0.84, bottom=0.20)

    here = os.path.dirname(os.path.abspath(__file__))
    outs = [os.path.join(here, "phase_diagram_misalignment.png")]
    mdir = os.environ.get("MANUSCRIPT_FIG_DIR")
    if mdir:
        outs.append(os.path.join(mdir, "figure_misalignment.png"))
    for out in outs:
        fig.savefig(out, dpi=160, bbox_inches='tight')
        print(f"saved: {os.path.normpath(out)}")
    print(f"u_d_min (Hill, representative) = {u_mins[0]:.3f}  (~prior-independent; > 0 == inversion holds)")


if __name__ == "__main__":
    main()
