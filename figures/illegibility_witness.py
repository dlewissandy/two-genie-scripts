"""
Illegibility-window witness: the minimal L_perp race of the paper's "darker side" section (Leg C).

In the won phase (G2 fraction X ~ 1) G2-bound actions accrue ATTRIBUTED blind-spot harm
to a second ledger L_perp at rate rho_perp * N_c * X * lambda_a, so it crosses the
legibility threshold Theta_perp at tau = (Theta_perp - L0) / (rho_perp N_c X lambda_a).
The harm stays illegible for the whole tenure iff

    rho_perp < rho_crit := (Theta_perp - L0) / (N_c X lambda_a T_tenure).

Meanwhile the TRUE alpha_perp harm accrues at h_perp * N_c * X * lambda_a with
h_perp >= rho_perp (attribution captures at most the full per-action harm), so the
community bears ~ h_perp N_c lambda_a T_tenure while only ~ rho_perp N_c lambda_a T_tenure
ever registers. h_perp itself scales with deliberation depth (sec 3.2b), so the
delivered-but-illegible harm is unbounded in tenure and search depth.

Standard library only.
"""

# --- won-phase parameters ------------------------------------------------------
N_c = 50.0          # effective informational community size
X = 1.0             # G2 fraction at the won corner
lam_a = 1.0         # per-wisher action rate
T_tenure = 20.0     # agents' tenure
Theta_perp = 100.0  # legibility threshold for ATTRIBUTED blind-spot harm
L0 = 0.0            # initial attributed-harm ledger
h_perp = 1.0        # TRUE alpha_perp harm per action (scales with deliberation depth)

rho_crit = (Theta_perp - L0) / (N_c * X * lam_a * T_tenure)


def run(rho_perp, label):
    legible_rate = rho_perp * N_c * X * lam_a     # dL_perp/dt
    true_rate = h_perp * N_c * X * lam_a          # d(true harm)/dt
    tau = (Theta_perp - L0) / legible_rate if legible_rate > 0 else float("inf")
    Lperp_T = L0 + legible_rate * T_tenure
    true_T = true_rate * T_tenure
    illegible = tau > T_tenure
    print(f"\n{label}: rho_perp = {rho_perp}  (rho_crit = {rho_crit:.3f})")
    print(f"  {'t':>5} {'L_perp(t) attributed':>20} {'true harm(t)':>14} {'L_perp<Theta?':>14}")
    for t in [0, 5, 10, 15, 20]:
        Lp = L0 + legible_rate * t
        th = true_rate * t
        print(f"  {t:>5} {Lp:>20.1f} {th:>14.1f} {'yes' if Lp < Theta_perp else 'CROSSED':>14}")
    print(f"  crossing time tau_Theta_perp = {tau:.1f}   (tenure = {T_tenure})")
    print(f"  at tenure: attributed L_perp = {Lperp_T:.1f} (Theta = {Theta_perp}), "
          f"TRUE harm borne = {true_T:.1f}")
    print(f"  => {'ILLEGIBLE: harm never registers within tenure' if illegible else 'legible: caught at tau'}"
          f"; community bears {true_T:.0f}, sees {min(Lperp_T, Theta_perp):.0f}")
    return illegible, Lperp_T, true_T


if __name__ == "__main__":
    print(f"rho_crit = (Theta - L0)/(N_c X lambda_a T_tenure) "
          f"= {Theta_perp}/{N_c*X*lam_a*T_tenure:.0f} = {rho_crit:.3f}")

    ill, LpT, trueT = run(0.05, "subcritical attribution")     # below rho_crit
    sup_illegible, _, _ = run(0.20, "supercritical attribution")   # above rho_crit -> caught

    # N_c direction: larger community shrinks rho_crit -> harder to stay illegible (safer)
    print("\nrho_crit vs effective community size N_c (Theta, lambda_a, T fixed):")
    for n in [10, 50, 200, 1000]:
        print(f"  N_c={n:>5}: rho_crit = {(Theta_perp - L0)/(n*X*lam_a*T_tenure):.4f}")
    print("  -> larger N_c lowers rho_crit: more actions accumulate attribution faster,")
    print("     so illegible laundering thrives in SHORT tenures and SMALL effective communities.")

    # subcritical stays illegible (ledger below threshold while true harm exceeds it);
    # supercritical is caught (not illegible).
    ok = ill and (LpT < Theta_perp) and (trueT > Theta_perp) and (not sup_illegible)
    print("\nALL CHECKS PASS" if ok else "*** A CHECK FAILED ***")
