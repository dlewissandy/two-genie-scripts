import TwoGenie.Primitives

/-!
# Per-wisher dynamics: the affine fast chain and its Banach fixed point

Formalizes §3 ("Prior-agnostic wisher dynamics"). Each wisher carries a
calibration state `b` evolving under the noise-averaged update (eq. 1, eq. 2a):

  `T_X(b) = b + η_b · A_g · σ · (1 - b) - μ · ε · b`

with attunement `R = A_g σ (1-b)` (eq. RD-R) and dissonance `D = ε b` (eq. RD-D).
Writing the linear relaxation rate `L_b := η_b A_g σ + μ ε`, the map is affine:
`T_X(b) = (1 - L_b) b + η_b A_g σ`.

Results:
* `Tmap_affine`        — the update is affine in `b` with slope `1 - L_b`.
* `Tmap_fixed`         — `b*(X;θ) = η_b A_g σ / L_b` is a fixed point (eq. bstar).
* `Tmap_contract`      — `|T b - T b'| = |1 - L_b| · |b - b'|`; a strict contraction
                          when `L_b ∈ (0,2)`, the step-size condition.
* `fixed_unique`       — the fixed point is unique (the Banach conclusion, proved
                          here directly from the contraction equality).
* `bstar_eq_cg`        — under the sharp threshold `σ = 1`, `b* = c_g = 1/(1+ρ_g)`
                          with `ρ_g = μ ε / (η_b A_g)` (eq. hat-sigma).
* perceived utilities `uPercG1/G2` are affine in `b` (`uPercG2_affine`, …); this
  affineness is exactly what the Lifting Theorem (`Lifting.lean`) integrates against.
-/

namespace TwoGenie

/-- The noise-averaged calibration update `T_X` (eq. 2a with the linear forms
eq. RD-R, eq. RD-D). `et = η_b`, `mu = μ`, `eps = ε`, `Ag = A_g`, `sig = σ(X)`. -/
def Tmap (et mu eps Ag sig b : ℝ) : ℝ := b + et * Ag * sig * (1 - b) - mu * eps * b

/-- The linear relaxation rate `L_b := η_b A_g σ + μ ε`. -/
def relax (et mu eps Ag sig : ℝ) : ℝ := et * Ag * sig + mu * eps

/-- The deterministic fixed point `b*(X;θ) = η_b A_g σ / L_b` (eq. bstar). -/
noncomputable def bstar (et mu eps Ag sig : ℝ) : ℝ :=
  et * Ag * sig / relax et mu eps Ag sig

/-- The update is affine in `b`: `T_X(b) = (1 - L_b) b + η_b A_g σ`. -/
theorem Tmap_affine (et mu eps Ag sig b : ℝ) :
    Tmap et mu eps Ag sig b = (1 - relax et mu eps Ag sig) * b + et * Ag * sig := by
  unfold Tmap relax; ring

/-- **Banach fixed point** (closed form), eq. bstar: `T_X(b*) = b*`, provided the
relaxation rate is nonzero (guaranteed by the step-size condition `L_b > 0`). -/
theorem Tmap_fixed (et mu eps Ag sig : ℝ) (hL : relax et mu eps Ag sig ≠ 0) :
    Tmap et mu eps Ag sig (bstar et mu eps Ag sig) = bstar et mu eps Ag sig := by
  rw [Tmap_affine]
  unfold bstar
  field_simp
  ring

/-- The update is a Lipschitz map with exact factor `|1 - L_b|`:
`|T b - T b'| = |1 - L_b| · |b - b'|`. Under the step-size condition
`0 < L_b < 2` this factor is `< 1`, so `T_X` is a strict contraction and the
Banach fixed-point theorem applies. -/
theorem Tmap_contract (et mu eps Ag sig b b' : ℝ) :
    |Tmap et mu eps Ag sig b - Tmap et mu eps Ag sig b'|
      = |1 - relax et mu eps Ag sig| * |b - b'| := by
  rw [Tmap_affine, Tmap_affine]
  rw [show (1 - relax et mu eps Ag sig) * b + et * Ag * sig
        - ((1 - relax et mu eps Ag sig) * b' + et * Ag * sig)
        = (1 - relax et mu eps Ag sig) * (b - b') by ring]
  rw [abs_mul]

/-- The contraction factor is `< 1` exactly under the step-size condition
`0 < L_b < 2` (the condition `0 < η_b A_g σ + μ ε < 2` in §3). -/
theorem contract_lt_one (et mu eps Ag sig : ℝ)
    (h0 : 0 < relax et mu eps Ag sig) (h2 : relax et mu eps Ag sig < 2) :
    |1 - relax et mu eps Ag sig| < 1 := by
  rw [abs_lt]; constructor <;> linarith

/-- **Uniqueness of the fixed point** (the Banach conclusion). Any two fixed points
of a strict contraction coincide; proved here directly from the contraction
equality, so no fixed-point library is needed. -/
theorem fixed_unique (et mu eps Ag sig x y : ℝ)
    (hc : |1 - relax et mu eps Ag sig| < 1)
    (hx : Tmap et mu eps Ag sig x = x) (hy : Tmap et mu eps Ag sig y = y) :
    x = y := by
  have hkey : |x - y| = |1 - relax et mu eps Ag sig| * |x - y| := by
    calc |x - y| = |Tmap et mu eps Ag sig x - Tmap et mu eps Ag sig y| := by rw [hx, hy]
    _ = |1 - relax et mu eps Ag sig| * |x - y| := Tmap_contract _ _ _ _ _ _ _
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  nlinarith [hkey, hpos, hc]

/-! ## Operational awareness and the sharp-threshold reduction -/

/-- The dimensionless calibration-update scale `ρ_g := μ ε / (η_b A_g)` (eq. hat-sigma). -/
noncomputable def rhoScale (et mu eps Ag : ℝ) : ℝ := mu * eps / (et * Ag)

/-- The amplitude-rescaling factor `c_g := 1 / (1 + ρ_g)` (eq. hat-sigma). -/
noncomputable def cAmp (et mu eps Ag : ℝ) : ℝ := 1 / (1 + rhoScale et mu eps Ag)

/-- Below threshold (`σ = 0`) the fixed point is `0`: no community signal, no
calibration. -/
theorem bstar_below (et mu eps Ag : ℝ) :
    bstar et mu eps Ag 0 = 0 := by
  unfold bstar relax; simp

/-- **Sharp-threshold reduction** (eq. bstar-step): above threshold (`σ = 1`) the
fixed point equals the operational-awareness rescale, `b* = c_g = 1/(1+ρ_g)`. -/
theorem bstar_eq_cg (et mu eps Ag : ℝ) (het : 0 < et) (hAg : 0 < Ag) :
    bstar et mu eps Ag 1 = cAmp et mu eps Ag := by
  unfold bstar cAmp rhoScale relax
  have hetAg : et * Ag ≠ 0 := by positivity
  field_simp

/-! ## Perceived utilities are affine in the calibration state

(eq. uperc-G2, eq. uperc-G1). The affineness in `b` is the single fact the
Lifting Theorem relies on. Here `ua = u_actual`, `ualt = u_alt`, `Bcap = B`,
`Mcap = M`, `Aa = A_{G1}`. -/

/-- Perceived utility under `G2` (eq. uperc-G2): `u_actual^G2 + u_alt^G2 - B(1-b)`. -/
def uPercG2 (uaG2 ualtG2 Bcap b : ℝ) : ℝ := uaG2 + ualtG2 - Bcap * (1 - b)

/-- Perceived utility under `G1` (eq. uperc-G1): `u_actual^G1 + u_alt^G1 + M - A·b`. -/
def uPercG1 (uaG1 ualtG1 Mcap Aa b : ℝ) : ℝ := uaG1 + ualtG1 + Mcap - Aa * b

/-- `uPercG2` is affine in `b` with intercept `u_actual^G2+u_alt^G2-B` and slope `B`. -/
theorem uPercG2_affine (uaG2 ualtG2 Bcap b : ℝ) :
    uPercG2 uaG2 ualtG2 Bcap b = (uaG2 + ualtG2 - Bcap) + Bcap * b := by
  unfold uPercG2; ring

/-- `uPercG1` is affine in `b` with intercept `u_actual^G1+u_alt^G1+M` and slope `-A`. -/
theorem uPercG1_affine (uaG1 ualtG1 Mcap Aa b : ℝ) :
    uPercG1 uaG1 ualtG1 Mcap Aa b = (uaG1 + ualtG1 + Mcap) + (-Aa) * b := by
  unfold uPercG1; ring

end TwoGenie
