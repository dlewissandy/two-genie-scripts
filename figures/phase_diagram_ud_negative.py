"""
Legacy single-panel Hill plot (worst-case u_d<0, "best != harmless"): π_high/π_bind
contours over (K_G2, K_G1). Same model as phase_diagram_combined_contours.py with u_d
flipped negative. Writes only phase_diagram_ud_negative.png next to this script.
This single-panel legacy plot is superseded by the cross-prior grid produced by
phase_diagram_grid.py.

Region <-> named-inequality map (§6 Q3/Q4/Q5 = B-low/B-high/C):
  red (π_high<0): (B-high) fails; amber (π_high>=0,π_bind<0): (C) fails, G1-favored;
  green (π_bind>=0): (C) holds, G2-favored. (B-low): π_low=d+u_d-b-1<0 throughout.
Reference points A-D and parameters are illustrative, not calibrated.

Parameters: n=2, a=0.8, b=0.3, d=1.0, u_d=-0.1.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.lines import Line2D
from scipy.optimize import brentq
import os

n   = 2
a   = 0.8    # base parameters: favorable working point with u_d sign flipped
b   = 0.3
d   = 1.0
u_d = -0.1   # worst-case under "best != harmless" (vs +0.1 in Figure 1)
pi_low = d + u_d - b - 1   # (B-low) test value; X-independent, must be < 0

def h(chi, K):    return K**n / (K**n + chi**n)
def g(chi, K):    return h(chi, K) + h(1 - chi, K)
def sigma(K):     return K**n / (K**n + 1)
def pi_high(K_G2, K_G1):
    return d + a * (1 - sigma(K_G1)) + u_d - 1 - b * sigma(K_G2)

def F_delta(chi, K_G2, K_G1):
    h2 = K_G2**n / (K_G2**n + chi**n)
    h3 = K_G1**n / (K_G1**n + chi**n)
    return u_d + d - 1 + a * (1 - h3) - b * h2

def chi_star(K_G2, K_G1):
    """Solve F_Delta(chi; K_G2, K_G1) = 0 for chi in (0, 1); NaN where no corner."""
    f_lo, f_hi = F_delta(1e-6, K_G2, K_G1), F_delta(1.0, K_G2, K_G1)
    if f_lo >= 0: return 0.0
    if f_hi <= 0: return np.nan
    return brentq(lambda c: F_delta(c, K_G2, K_G1), 1e-6, 1.0)

def _h_prime(x, K, n_):
    """∂/∂x [K^n / (K^n + x^n)]."""
    if n_ == 1:
        return -K / (K + x)**2
    return -n_ * K**n_ * x**(n_-1) / (K**n_ + x**n_)**2

def _W_prime(chi, K_G2, K_G1):
    g2p = _h_prime(chi, K_G2, n) - _h_prime(1.0 - chi, K_G2, n)
    g3p = _h_prime(chi, K_G1, n) - _h_prime(1.0 - chi, K_G1, n)
    return b * g2p + a * g3p

def _W_at(chi, K_G2, K_G1):
    return b * g(chi, K_G2) + a * g(chi, K_G1)

def _maximize_W(K_G2, K_G1):
    """Brent's-method maximizer of W(χ) = b·g₂ + a·g₃ on [0, 1/2]; replaces
    1001-point chi_grid (which missed χ†<5×10⁻⁴ in Regime III at low K — audit M6)."""
    candidates = [0.0, 0.5]
    scan = np.linspace(1e-6, 0.5 - 1e-6, 64)
    wp = np.array([_W_prime(c, K_G2, K_G1) for c in scan])
    sign_changes = np.where(np.diff(np.sign(wp)) != 0)[0]
    for i in sign_changes:
        try:
            root = brentq(_W_prime, scan[i], scan[i+1], args=(K_G2, K_G1), xtol=1e-12)
            candidates.append(root)
        except ValueError:
            pass
    W_values = [_W_at(c, K_G2, K_G1) for c in candidates]
    idx = int(np.argmax(W_values))
    return candidates[idx], W_values[idx]

def pi_bind(K_G2, K_G1):
    _, W_max = _maximize_W(K_G2, K_G1)
    return 2.0 * (u_d + d - 1.0 + a) - W_max

K_range = np.linspace(0.05, 3.0, 220)
K_G2_grid, K_G1_grid = np.meshgrid(K_range, K_range)
phi_h = np.vectorize(pi_high)(K_G2_grid, K_G1_grid)
phi_b = np.vectorize(pi_bind)(K_G2_grid, K_G1_grid)
K_star = 0.5 * ((n + 1) / (n - 1)) ** (1 / n)

fig, ax = plt.subplots(figsize=(10, 9))
region = np.zeros_like(phi_h)
region[(phi_h < 0)] = 0
region[(phi_h >= 0) & (phi_b < 0)] = 1
region[(phi_b >= 0)] = 2
ax.imshow(region, origin='lower',
          extent=[K_range.min(), K_range.max(), K_range.min(), K_range.max()],
          cmap=ListedColormap(['#fad9d9', '#fdf0c9', '#dbecda']),
          vmin=-0.5, vmax=2.5, aspect='equal', alpha=0.55)

levels_h = [-0.5, -0.3, -0.15, 0.15, 0.3, 0.5, 0.8]
cs_h = ax.contour(K_G2_grid, K_G1_grid, phi_h, levels=levels_h,
                  colors='#b21e3a', linewidths=1.1, alpha=0.9)
ax.clabel(cs_h, inline=True, fontsize=8, fmt='%.2f')
cs_h0 = ax.contour(K_G2_grid, K_G1_grid, phi_h, levels=[0],
                   colors='#b21e3a', linewidths=3.0)
ax.clabel(cs_h0, inline=True, fontsize=10, fmt={0: 'π_high = 0'})

levels_b = [-1.4, -1.2, -1.0, -0.8, -0.5, -0.25, 0.1]
cs_b = ax.contour(K_G2_grid, K_G1_grid, phi_b, levels=levels_b,
                  colors='#1f4e9b', linewidths=1.1, alpha=0.9, linestyles='--')
ax.clabel(cs_b, inline=True, fontsize=8, fmt='%.2f')
cs_b0 = ax.contour(K_G2_grid, K_G1_grid, phi_b, levels=[0],
                   colors='#1f4e9b', linewidths=3.0, linestyles='--')
ax.clabel(cs_b0, inline=True, fontsize=10, fmt={0: 'π_bind = 0'})

# χ* (basin tipping point) contours — purple dotted. χ*(K_G2, K_G1) is the first
# zero of F_Δ (NaN where no all-G2 corner exists, since F_Δ(1) = π_high). The
# favoredness floor is N_c > 1/(1/2 − χ*) (eq:nc-floor), so each χ* level fixes the
# minimum favored community size — the lower bound of the operational window
# (eq:achievability-window). The bold χ* = 1/2 curve (below) marks where that floor
# diverges and the operational window closes.
chi_grid = np.vectorize(chi_star)(K_G2_grid, K_G1_grid)
cs_chi = ax.contour(K_G2_grid, K_G1_grid, chi_grid,
                    levels=[0.15, 0.2, 0.3, 0.4, 0.45], colors='#6a3d9a',
                    linewidths=1.0, linestyles=':', alpha=0.95)
ax.clabel(cs_chi, inline=True, fontsize=8, fmt=r'$\chi^*=%.2f$')
# χ* = 1/2: the favoredness boundary. The floor 1/(1/2−χ*) diverges here, so the
# operational window closes; for χ* > 1/2 (amber side) F_Δ(1/2) < 0, (C) fails at the
# midpoint, and G1 is favored on the integrated payoff — larger N_c does not rescue it.
cs_chi12 = ax.contour(K_G2_grid, K_G1_grid, chi_grid, levels=[0.5],
                      colors='#6a3d9a', linewidths=3.0, linestyles=':')
ax.clabel(cs_chi12, inline=True, fontsize=9, fmt={0.5: r'$\chi^*=1/2$'})

ax.plot(K_range, K_range, color='gray', linestyle='-', linewidth=1.0, alpha=0.4)
ax.text(2.05, 2.10, r"$K_{G_2} = K_{G_1}$", color='gray', fontsize=9, rotation=45)

points = [(0.5, 0.5, 'A'), (1.5, 1.5, 'B'), (0.5, 1.5, 'C'), (1.5, 0.5, 'D')]
for K_G2, K_G1, name in points:
    ph = pi_high(K_G2, K_G1); pb = pi_bind(K_G2, K_G1)
    ax.plot(K_G2, K_G1, 'o', markersize=9, markerfacecolor='white',
            markeredgecolor='black', markeredgewidth=1.5, zorder=5)
    ax.annotate(f"{name}: π_h={ph:+.2f}, π_b={pb:+.2f}",
                (K_G2, K_G1), xytext=(11, 9), textcoords='offset points',
                fontsize=7, weight='bold',
                bbox=dict(facecolor='white', alpha=0.92, edgecolor='black', pad=2),
                zorder=6)

legend_elems = [
    Line2D([0], [0], color='#b21e3a', linewidth=3.0,
           label='π_high = 0  —  (B-high) corner-existence'),
    Line2D([0], [0], color='#b21e3a', linewidth=1.1, label='π_high level curves'),
    Line2D([0], [0], color='#1f4e9b', linewidth=3.0, linestyle='--',
           label='π_bind = 0  —  (C) ratio-favored boundary'),
    Line2D([0], [0], color='#1f4e9b', linewidth=1.1, linestyle='--',
           label='π_bind level curves'),
    Line2D([0], [0], color='#6a3d9a', linewidth=1.4, linestyle=':',
           label=r'$\chi^*$ contours (tipping pt; bold $=1/2$)'),
]
ax.legend(handles=legend_elems, loc='upper right', fontsize=9, framealpha=0.95)
ax.set_xlabel(r"$K_{G_2}$ (median wisher threshold for $G_2$)", fontsize=12)
ax.set_ylabel(r"$K_{G_1}$ (median wisher threshold for $G_1$)", fontsize=12)
ax.set_title(
    f"u_d = {u_d:+.1f} (worst-case 'best ≠ harmless')\n"
    f"n = {n}, a = {a}, b = {b}, d = {d}   |   "
    f"π_low = {pi_low:+.2f} < 0 throughout (B-low holds)\n"
    r"red = (B-high) fails (no corner)   ·   amber = (C) fails ($G_1$-favored)   ·   green = (C) holds ($G_2$-favored)",
    fontsize=10,
)
ax.set_xlim(K_range.min(), K_range.max())
ax.set_ylim(K_range.min(), K_range.max())
plt.tight_layout()
_here = os.path.dirname(os.path.abspath(__file__))
for _out in [os.path.join(_here, "phase_diagram_ud_negative.png")]:
    plt.savefig(_out, dpi=150, bbox_inches='tight')
    print(f"saved: {os.path.normpath(_out)}")
