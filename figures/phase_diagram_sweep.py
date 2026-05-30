"""
Misalignment sweep: u_d (columns) x theta_lambda (rows), Hill family, in the (K_G2, K_G1)
adoption plane.

Uses the EXACT colour scheme and contours of the cross-prior phase grid
(phase_diagram_grid.py): green = G2-favored basin, amber = G1-favored, red = no stable
corner; bold red pi_high=0, dashed blue pi_bind=0, dotted purple chi* level sets, gray
equal-scale diagonal. No special laundering colour.

The point of keeping the scheme identical: a green basin in the bottom two rows is
indistinguishable from a healthy basin, because to the adoption dynamics it IS one. The
row labels carry what the colour cannot:

  rows are theta_lambda = 0, pi/8, pi/4, 3pi/8, i.e. d = +1.00, +0.54, 0.00, -0.54.
  row theta = pi/4  (d = 0,  W_agg = 0)  : WELFARE ILLEGIBLE -- the audit's welfare signal
                                            has vanished; a basin here tracks nothing.
  row theta = 3pi/8 (d < 0,  W_agg < 0)  : LAUNDERING -- the basin is adopted and harmful.

Writes phase_diagram_sweep.png next to this script. If MANUSCRIPT_FIG_DIR is set,
also writes a copy named figure_misalignment_sweep.png into that directory.
"""

import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

import phase_diagram_grid as pg

D0, KAPPA = 1.0, 1.0
THETAS = [0.0, np.pi / 8, np.pi / 4, 3 * np.pi / 8]
TH_LABELS = ['0', r'\pi/8', r'\pi/4', r'3\pi/8']
ROW_TAG = ['Aligned', 'Partially Aligned', 'WELFARE ILLEGIBLE', 'LAUNDERING']  # bottom two are the point
ROW_TAGCOLOR = ['#444', '#444', '#1f4e9b', '#b21e3a']
U_DS = [0.5, 1.0, 1.5]
FAM = pg.FAMILIES[0]                       # Hill
A, B = 0.8, 0.3
NGRID = 200

# exact scheme of phase_diagram_grid
REGION_CMAP = ListedColormap(['#fad9d9', '#fdf0c9', '#dbecda'])  # red, amber, green


def d_of_theta(theta):
    return D0 * (np.cos(theta) - KAPPA * np.sin(theta))


def main():
    lo, hi = FAM["rng"]
    rng = np.linspace(lo, hi, NGRID)
    XG2, XG1 = np.meshgrid(rng, rng)

    fig, axes = plt.subplots(len(THETAS), len(U_DS), figsize=(10.5, 13.0))
    for r, theta in enumerate(THETAS):
        pg.D = d_of_theta(theta)
        for c, u_d in enumerate(U_DS):
            P = dict(a=A, b=B, u_d=u_d)
            ax = axes[r, c]
            phi_h = np.vectorize(lambda x2, x1: pg.pi_high(FAM, P, x2, x1))(XG2, XG1)
            phi_b = np.vectorize(lambda x2, x1: pg.pi_bind(FAM, P, x2, x1))(XG2, XG1)
            chi_g = np.vectorize(lambda x2, x1: pg.chi_star(FAM, P, x2, x1))(XG2, XG1)

            region = np.zeros_like(phi_h)
            region[(phi_h >= 0) & (phi_b < 0)] = 1
            region[(phi_b >= 0)] = 2
            ax.imshow(region, origin='lower', extent=[lo, hi, lo, hi], cmap=REGION_CMAP,
                      vmin=-0.5, vmax=2.5, aspect='auto', alpha=0.6)

            ax.contour(XG2, XG1, phi_h, levels=[0], colors='#b21e3a', linewidths=2.2)
            ax.contour(XG2, XG1, phi_b, levels=[0], colors='#1f4e9b', linewidths=2.2, linestyles='--')
            if np.any(np.isfinite(chi_g)):
                ax.contour(XG2, XG1, chi_g, levels=[0.15, 0.2, 0.3, 0.4], colors='#6a3d9a',
                           linewidths=0.8, linestyles=':', alpha=0.95)
                ax.contour(XG2, XG1, chi_g, levels=[0.5], colors='#6a3d9a',
                           linewidths=2.2, linestyles=':')
            ax.plot(rng, rng, color='gray', linewidth=0.8, alpha=0.45)

            ax.set_xlim(lo, hi)
            ax.set_ylim(lo, hi)
            ax.tick_params(labelsize=7)
            ax.set_xticks(np.round(np.linspace(lo, hi, 4), 2))
            ax.set_yticks(np.round(np.linspace(lo, hi, 4), 2))
            if r == len(THETAS) - 1:
                ax.set_xlabel(r"$K_{G_2}$", fontsize=9)
            if r == 0:
                ax.set_title(rf"$u_d={u_d}$", fontsize=12, fontweight='bold')
            if c == 0:
                lbl = rf"$\theta_\lambda={TH_LABELS[r]}$" + "\n" + rf"$d={pg.D:+.2f}$"
                ax.set_ylabel(lbl + "\n" + r"$K_{G_1}$", fontsize=9)
                if ROW_TAG[r]:
                    ax.text(-0.42, 0.5, ROW_TAG[r], transform=ax.transAxes, rotation=90,
                            va='center', ha='center', fontsize=10, fontweight='bold',
                            color=ROW_TAGCOLOR[r])

    legend = [
        Patch(facecolor='#dbecda', edgecolor='gray', label=r'$G_2$-favored basin'),
        Patch(facecolor='#fdf0c9', edgecolor='gray', label=r'$G_1$-favored'),
        Patch(facecolor='#fad9d9', edgecolor='gray', label=r'no stable $G_2$ corner'),
        Line2D([0], [0], color='#b21e3a', lw=2.2, label=r'$\pi_{\mathrm{high}}=0$'),
        Line2D([0], [0], color='#1f4e9b', lw=2.2, ls='--', label=r'$\pi_{\mathrm{bind}}=0$'),
        Line2D([0], [0], color='#6a3d9a', lw=0.8, ls=':', label=r'$\chi^*$ level sets'),
    ]
    fig.legend(handles=legend, loc='lower center', ncol=6, fontsize=9,
               framealpha=0.95, bbox_to_anchor=(0.5, 0.005))
    fig.subplots_adjust(left=0.13, right=0.98, top=0.955, bottom=0.07, wspace=0.20, hspace=0.22)

    here = os.path.dirname(os.path.abspath(__file__))
    outs = [os.path.join(here, "phase_diagram_sweep.png")]
    mdir = os.environ.get("MANUSCRIPT_FIG_DIR")
    if mdir:
        outs.append(os.path.join(mdir, "figure_misalignment_sweep.png"))
    for out in outs:
        fig.savefig(out, dpi=150, bbox_inches='tight')
        print(f"saved: {os.path.normpath(out)}")


if __name__ == "__main__":
    main()
