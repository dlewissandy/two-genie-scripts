"""
Misalignment basin grid: the cooperative basin in adoption coordinates (K_G2, K_G1),
across the four threshold priors (rows) as misalignment grows (columns), at a fixed
private usefulness u_d above the laundering threshold u_d_min so that laundering basins
appear rather than the basin merely collapsing.

Misalignment enters only through d = d0(cos theta - kappa sin theta) (sec 3.1a), the module
global pg.D set per column. A basin cell is recolored from green to red where d < 0: there
the basin still exists and G2 is adopted, but W_agg < 0 (laundering). The point of the grid:
past theta_crit the basin does not vanish, it turns into a laundering basin, and the basin
SHAPE (chi*) varies by prior while the laundering threshold u_d_min does not.

Writes phase_diagram_misalignment_grid.png next to this script. If
MANUSCRIPT_FIG_DIR is set, also writes a copy named figure_misalignment_grid.png
into that directory.
"""

import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

import phase_diagram_grid as pg

D0, KAPPA = 1.0, 1.0
THETA_CRIT = np.arctan(1.0 / KAPPA)
THETAS = [0.0, np.pi / 4, 3 * np.pi / 8, 7 * np.pi / 16]
TH_LABELS = ['0', r'\pi/4', r'3\pi/8', r'7\pi/16']
U_D = 1.6                      # above u_d_min ~ 0.8, so laundering basins appear
A, B = 0.8, 0.3
NGRID = 200


def d_of_theta(theta):
    return D0 * (np.cos(theta) - KAPPA * np.sin(theta))


def main():
    # 0 no corner (gray), 1 G1-favored (amber), 2 G2 basin d>=0 (green),
    # 3 G2 basin d<0 = LAUNDERING (red)
    cmap = ListedColormap(['#ededed', '#fdf0c9', '#dbecda', '#e06666'])
    P = dict(a=A, b=B, u_d=U_D)

    fig, axes = plt.subplots(len(pg.FAMILIES), len(THETAS), figsize=(13.0, 12.6))
    for r, fam in enumerate(pg.FAMILIES):
        lo, hi = fam["rng"]
        rng = np.linspace(lo, hi, NGRID)
        XG2, XG1 = np.meshgrid(rng, rng)
        for c, theta in enumerate(THETAS):
            pg.D = d_of_theta(theta)
            ax = axes[r, c]
            phi_h = np.vectorize(lambda x2, x1: pg.pi_high(fam, P, x2, x1))(XG2, XG1)
            phi_b = np.vectorize(lambda x2, x1: pg.pi_bind(fam, P, x2, x1))(XG2, XG1)
            chi_g = np.vectorize(lambda x2, x1: pg.chi_star(fam, P, x2, x1))(XG2, XG1)

            region = np.zeros_like(phi_h)
            region[(phi_h >= 0) & (phi_b < 0)] = 1
            region[phi_b >= 0] = 2
            if pg.D < 0:
                region[phi_b >= 0] = 3
            ax.imshow(region, origin='lower', extent=[lo, hi, lo, hi], cmap=cmap,
                      vmin=-0.5, vmax=3.5, aspect='auto', alpha=0.7)
            ax.contour(XG2, XG1, phi_b, levels=[0], colors='#1f4e9b', linewidths=1.6, linestyles='--')
            if np.any(np.isfinite(chi_g)):
                ax.contour(XG2, XG1, chi_g, levels=[0.2, 0.3, 0.4], colors='#6a3d9a',
                           linewidths=0.7, linestyles=':', alpha=0.9)
            ax.plot(rng, rng, color='gray', linewidth=0.7, alpha=0.4)
            ax.set_xlim(lo, hi)
            ax.set_ylim(lo, hi)
            ax.tick_params(labelsize=7)
            ax.set_xticks(np.round(np.linspace(lo, hi, 4), 2))
            ax.set_yticks(np.round(np.linspace(lo, hi, 4), 2))
            if r == len(pg.FAMILIES) - 1:
                ax.set_xlabel(rf"${fam['g2']}$", fontsize=9)
            if c == 0:
                ax.set_ylabel(f"{fam['name']}\n(scale ${fam['scale']}$)", fontsize=10, fontweight='bold')
            if r == 0:
                tag = r"\;>\theta^{crit}" if theta > THETA_CRIT + 1e-9 else \
                      (r"\;=\theta^{crit}" if abs(theta - THETA_CRIT) < 1e-9 else "")
                ax.set_title(rf"$\theta_\lambda={TH_LABELS[c]}{tag}$, $d={pg.D:+.2f}$", fontsize=10)

    legend = [
        Patch(facecolor='#dbecda', edgecolor='gray', label=r'$G_2$ basin, tracks welfare ($d\geq0$)'),
        Patch(facecolor='#e06666', edgecolor='gray', label=r'$G_2$ basin, LAUNDERING ($d<0$, $W_{agg}<0$)'),
        Patch(facecolor='#fdf0c9', edgecolor='gray', label=r'$G_1$-favored'),
        Patch(facecolor='#ededed', edgecolor='gray', label=r'no $G_2$ basin'),
        Line2D([0], [0], color='#1f4e9b', lw=1.6, ls='--', label=r'$\pi_{\mathrm{bind}}=0$'),
        Line2D([0], [0], color='#6a3d9a', lw=0.7, ls=':', label=r'$\chi^*$ level sets'),
    ]
    fig.legend(handles=legend, loc='lower center', ncol=6, fontsize=9,
               framealpha=0.95, bbox_to_anchor=(0.5, 0.002))
    fig.suptitle(
        rf"Misalignment basin grid ($u_d={U_D}>u_d^{{\min}}$, $a={A}$, $b={B}$, $\kappa=1$): "
        r"past $\theta_\lambda^{\mathrm{crit}}=\pi/4$ the basin persists as a LAUNDERING basin (red),"
        "\n"
        r"across all four priors. The basin shape $\chi^*$ is prior-dependent; the laundering "
        r"threshold $u_d^{\min}$ is not.",
        fontsize=12, y=0.995)
    fig.subplots_adjust(left=0.07, right=0.99, top=0.92, bottom=0.07, wspace=0.22, hspace=0.22)

    here = os.path.dirname(os.path.abspath(__file__))
    outs = [os.path.join(here, "phase_diagram_misalignment_grid.png")]
    mdir = os.environ.get("MANUSCRIPT_FIG_DIR")
    if mdir:
        outs.append(os.path.join(mdir, "figure_misalignment_grid.png"))
    for out in outs:
        fig.savefig(out, dpi=150, bbox_inches='tight')
        print(f"saved: {os.path.normpath(out)}")


if __name__ == "__main__":
    main()
