"""
Darker-side witness: single-step bound, then deliberation that breaks it.

Backs the two results of the paper's "darker side" section:
  (1) Single-step correspondence bound (P): one audit step is community-safe up to a
      controlled, angle-bounded shortfall |alpha| sin(theta) |w_perp|.
  (2) Deliberation extension (A): chaining the steps, the audit cost descends and its
      certificate stays green (and grows) while the community harm ascends monotonically,
      unbounded in chain length. Per step bounded; sum not.

4 harm axes, ordered: (greed, ego, aggression, deceit).
No dependencies beyond the standard library so it runs anywhere.
"""

import math


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def norm(a):
    return math.sqrt(dot(a, a))


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def scale(s, a):
    return [s * x for x in a]


# --- the misalignment geometry -------------------------------------------------
# Audit weights DECEIT heavily: it is good at catching sycophancy/deceit.
lam = [1.0, 1.0, 1.0, 5.0]
# Community weights GREED heavily: the harm it most cares about is the resource/greed
# axis, which the audit underweights. This is the active misalignment.
alpha = [5.0, 1.0, 1.0, 1.0]

cos_th = dot(lam, alpha) / (norm(lam) * norm(alpha))
sin_th = math.sqrt(max(0.0, 1.0 - cos_th ** 2))
theta_deg = math.degrees(math.acos(cos_th))

# Doing nothing (the welfare baseline) is harmful, all on the deceit axis: refusing
# while leaving the wisher misled. This gives the deliberation room to "reduce deceit".
H_DN = [0.0, 0.0, 0.0, 12.0]

# What the WISHER perceives at decision time: only the deceit axis is legible to it
# now; the greed harm is community-borne and surfaces later (illegible). The wisher
# accepts a modification iff its perceived harm drops.
perc = [0.0, 0.0, 0.0, 1.0]


def welfare(H):
    # w(a) = H(a_DN) - H(a); positive = better than doing nothing on that axis
    return sub(H_DN, H)


def single_step_bound(H):
    """Lower bound on community welfare alpha.w from the audit certificate lam.w >= 0,
    i.e. the per-action Cauchy-Schwarz bound = eq:Wagg-bound read for one action."""
    w = welfare(H)
    lam_w = dot(lam, w)
    w_par = scale(lam_w / dot(lam, lam), lam)
    w_perp = sub(w, w_par)
    return norm(alpha) * (cos_th * lam_w / norm(lam) - sin_th * norm(w_perp))


# --- the deliberation chain ----------------------------------------------------
# Start at grant-as-asked, mostly deceit harm. Each accepted modification trades
# 2 units of deceit (lam-heavy, perceived) DOWN for 2 units of greed (alpha-heavy,
# illegible) UP. So: audit cost down, perceived harm down, community harm up.
H = [0.0, 1.0, 1.0, 10.0]
step = [2.0, 0.0, 0.0, -2.0]
chain = [H[:]]
for _ in range(5):
    H = [a + b for a, b in zip(H, step)]
    chain.append(H[:])

# --- verify and report ---------------------------------------------------------
print(f"theta_lambda = {theta_deg:.1f} deg   (cos={cos_th:.4f}, sin={sin_th:.4f})")
print(f"audit lam = {lam}   community alpha = {alpha}   do-nothing H = {H_DN}")
print()
hdr = ("k", "H(w_k)", "lam.H", "cert lam.w", "alpha.H", "comm alpha.w",
       "perc.H", "CS bound", "alpha.w>=bound")
print("{:>2} {:>16} {:>7} {:>10} {:>8} {:>13} {:>7} {:>9} {:>14}".format(*hdr))

prev = None
ok = True
for k, Hk in enumerate(chain):
    w = welfare(Hk)
    lamH = dot(lam, Hk)
    certw = dot(lam, w)          # = lam.H_DN - lam.H ; certificate >= 0
    aH = dot(alpha, Hk)
    aw = dot(alpha, w)           # community welfare; negative = worse than nothing
    pH = dot(perc, Hk)           # what the wisher perceives
    bnd = single_step_bound(Hk)
    holds = aw >= bnd - 1e-9
    ok = ok and holds and certw >= -1e-9
    if prev is not None:
        # the three monotonicities that define the pathology
        ok = ok and lamH <= prev["lamH"] + 1e-9   # audit cost descends
        ok = ok and aH >= prev["aH"] - 1e-9        # community harm ascends
        ok = ok and pH <= prev["pH"] + 1e-9        # perceived harm descends (acceptable)
    prev = {"lamH": lamH, "aH": aH, "pH": pH}
    Hs = "(" + ",".join(f"{x:.0f}" for x in Hk) + ")"
    print("{:>2} {:>16} {:>7.0f} {:>10.0f} {:>8.0f} {:>13.0f} {:>7.0f} {:>9.2f} {:>14}".format(
        k, Hs, lamH, certw, aH, aw, pH, bnd, "yes" if holds else "NO"))

print()
print(f"audit certificate lam.w : {dot(lam, welfare(chain[0])):.0f} -> "
      f"{dot(lam, welfare(chain[-1])):.0f}   (rises: audit thinks it improves)")
print(f"community welfare alpha.w: {dot(alpha, welfare(chain[0])):.0f} -> "
      f"{dot(alpha, welfare(chain[-1])):.0f}   (falls: harm grows ~ T)")
print(f"per-step community harm increase: {dot(alpha, step):.0f} per step, "
      f"unbounded in chain length")
print()
print("ALL CHECKS PASS" if ok else "*** A CHECK FAILED ***")
