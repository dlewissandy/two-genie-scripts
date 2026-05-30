import TwoGenie.Priors
import TwoGenie.Priors.Hill

/-!
# Fréchet (inverse-Weibull / extreme-value Type II) threshold prior

A third heavy-tailed `ThresholdPrior`, genuinely distinct from the Hill
(log-logistic) and Pareto families: the Type-II extreme-value distribution, with a
*unimodal* density and a polynomial tail of a different functional pedigree. Survival
tail (scale `s > 0`, shape `α > 0`):

  `F̄(X) = 1 − exp(−(s/X)^α)`  for `X > 0`,   `F̄(0) = 1`.

The work mirrors the Hill discharge. The one genuinely harder step is the (Q2b)
Lipschitz bound: the density `φ(X) = (α/s)·t^{1+1/α}·e^{-t}` (with `t = (s/X)^α`) is
bounded by its mode value, which we obtain from `t^c e^{-t} ≤ c^c e^{-c}`
(`rpow_mul_exp_neg_le`), itself a one-line consequence of `log u ≤ u − 1` (no
calculus). The essential flat point at `X = 0` is handled by extending the interior
Lipschitz bound to the boundary through continuity.
-/

set_option linter.unusedVariables false

namespace TwoGenie

open Set

/-- **`t^c e^{-t} ≤ c^c e^{-c}`** for `c, t > 0`: the maximum of `t ↦ t^c e^{-t}`,
from `log(t/c) ≤ t/c − 1`. The single inequality behind the Fréchet density bound. -/
theorem rpow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    t ^ c * Real.exp (-t) ≤ c ^ c * Real.exp (-c) := by
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hc, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (t / c) ≤ t / c - 1 := Real.log_le_sub_one_of_pos (div_pos ht hc)
  have hmul : c * Real.log (t / c) ≤ c * (t / c - 1) := mul_le_mul_of_nonneg_left hlog hc.le
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hc)] at hmul
  have hsimp : c * (t / c - 1) = t - c := by field_simp
  rw [hsimp] at hmul
  rw [mul_comm (Real.log t) c, mul_comm (Real.log c) c]
  linarith [hmul]

/-- The Fréchet survival tail: `1 − exp(−(s/X)^α)` for `X > 0`, and `1` at `X ≤ 0`
(the `X = 0` value is the right-limit, restored explicitly because `s/0` is junk). -/
noncomputable def frechetTail (s alpha X : ℝ) : ℝ :=
  if 0 < X then 1 - Real.exp (-((s / X) ^ alpha)) else 1

/-- The Fréchet core on `X > 0` (the tail without the boundary patch). -/
noncomputable def frechetCore (s alpha X : ℝ) : ℝ := 1 - Real.exp (-((s / X) ^ alpha))

theorem frechetTail_eq_core {s alpha X : ℝ} (hX : 0 < X) :
    frechetTail s alpha X = frechetCore s alpha X := by
  unfold frechetTail frechetCore; rw [if_pos hX]

/-- `F̄(0) = 1`. -/
theorem frechetTail_zero (s alpha : ℝ) : frechetTail s alpha 0 = 1 := by
  unfold frechetTail; rw [if_neg (lt_irrefl 0)]

/-- `F̄(1) = 1 − exp(−s^α)`. -/
theorem frechetTail_one (s alpha : ℝ) :
    frechetTail s alpha 1 = 1 - Real.exp (-(s ^ alpha)) := by
  unfold frechetTail; rw [if_pos one_pos, div_one]

/-- **(Q2a)** The Fréchet tail is monotone non-increasing on `[0,1]` (source of
condition (A)): larger `X` shrinks `(s/X)^α`, hence grows `exp(−(s/X)^α)`. -/
theorem frechetTail_antitoneOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    AntitoneOn (frechetTail s alpha) (Icc 0 1) := by
  intro X hX Y hY hXY
  unfold frechetTail
  by_cases hX0 : 0 < X
  · have hY0 : 0 < Y := lt_of_lt_of_le hX0 hXY
    rw [if_pos hX0, if_pos hY0]
    have hsY : (0 : ℝ) < s / Y := div_pos hs hY0
    have hle : s / Y ≤ s / X := by gcongr
    have hpow : (s / Y) ^ alpha ≤ (s / X) ^ alpha := Real.rpow_le_rpow hsY.le hle ha.le
    have : Real.exp (-((s / X) ^ alpha)) ≤ Real.exp (-((s / Y) ^ alpha)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  · rw [if_neg hX0]
    by_cases hY0 : 0 < Y
    · rw [if_pos hY0]; linarith [Real.exp_pos (-((s / Y) ^ alpha))]
    · rw [if_neg hY0]

/-- **Derivative of the core** on `X > 0`. -/
theorem frechetCore_hasDerivAt {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (frechetCore s alpha)
      (-(Real.exp (-((s / X) ^ alpha))
        * -(s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))))) X := by
  have hsX : (0 : ℝ) < s / X := div_pos hs hX
  have h1 : HasDerivAt (fun X : ℝ => s / X) (s * -(X ^ 2)⁻¹) X := by
    have := (hasDerivAt_inv (ne_of_gt hX)).const_mul s
    simpa [div_eq_mul_inv] using this
  have hg : HasDerivAt (fun X : ℝ => (s / X) ^ alpha)
      (s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))) X := by
    have := h1.rpow_const (p := alpha) (Or.inl (ne_of_gt hsX))
    convert this using 1; ring
  exact (hg.neg.exp).const_sub (1 : ℝ)

/-- **(Q2b) density bound.** The magnitude of the core derivative is bounded by the
density mode value `M := (α/s)(1+1/α)^{1+1/α} e^{-(1+1/α)}` on `X > 0`. -/
theorem frechetCore_deriv_abs_le {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    |(-(Real.exp (-((s / X) ^ alpha)) * -(s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)))))|
      ≤ (alpha / s) * (1 + 1 / alpha) ^ (1 + 1 / alpha) * Real.exp (-(1 + 1 / alpha)) := by
  have hsX : (0 : ℝ) < s / X := div_pos hs hX
  have hR : (0 : ℝ) < (s / X) ^ (alpha - 1) := Real.rpow_pos_of_pos hsX _
  have hX2 : (0 : ℝ) < (X ^ 2)⁻¹ := by positivity
  set u := (s / X) ^ alpha with hu
  set beta := 1 + 1 / alpha with hbeta
  have hu_pos : 0 < u := Real.rpow_pos_of_pos hsX alpha
  have hbeta_pos : 0 < beta := by rw [hbeta]; positivity
  have hscalar : s * (X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)) = (alpha / s) * u ^ beta := by
    have e1 : u ^ beta = (s / X) ^ (alpha + 1) := by
      rw [hu, ← Real.rpow_mul hsX.le]; congr 1; rw [hbeta]; field_simp
    have e2 : (s / X) ^ (alpha + 1) = (s / X) ^ (alpha - 1) * (s / X) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hsX]; congr 1; ring
    have e3 : (s / X) ^ (2 : ℝ) = (s / X) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2, e3, div_pow]; field_simp
  have hpos : 0 ≤ Real.exp (-u) * (s * (X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))) := by positivity
  have hid : |(-(Real.exp (-u) * -(s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)))))|
      = (alpha / s) * u ^ beta * Real.exp (-u) := by
    rw [show (-(Real.exp (-u) * -(s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)))))
          = -(Real.exp (-u) * (s * (X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)))) from by ring,
        abs_neg, abs_of_nonneg hpos, hscalar]
    ring
  rw [hid]
  have hb := rpow_mul_exp_neg_le hbeta_pos hu_pos
  calc (alpha / s) * u ^ beta * Real.exp (-u)
      = (alpha / s) * (u ^ beta * Real.exp (-u)) := by ring
    _ ≤ (alpha / s) * (beta ^ beta * Real.exp (-beta)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (alpha / s) * (1 + 1 / alpha) ^ (1 + 1 / alpha) * Real.exp (-(1 + 1 / alpha)) := by
        rw [hbeta]; ring

/-- The exp factor `exp(−(s/X)^α) → 0` as `X → 0⁺`. -/
theorem frechet_exp_tendsto {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    Filter.Tendsto (fun X : ℝ => Real.exp (-((s / X) ^ alpha)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hinv : Filter.Tendsto (fun X : ℝ => s / X) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
    have h0 : Filter.Tendsto (fun X : ℝ => X⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) Filter.atTop :=
      tendsto_inv_nhdsGT_zero
    simpa [div_eq_mul_inv, mul_comm] using h0.const_mul_atTop hs
  have hpow : Filter.Tendsto (fun X : ℝ => (s / X) ^ alpha) (nhdsWithin 0 (Ioi 0)) Filter.atTop :=
    (tendsto_rpow_atTop ha).comp hinv
  exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atBot_iff.mpr hpow)

/-- **Right-continuity of the tail at `0`**: along `Ioi 0` the tail equals the core
`1 − exp(−(s/X)^α)`, which tends to `1 = F̄(0)` as `X → 0⁺`. -/
theorem frechetTail_continuousWithinAt_zero {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    ContinuousWithinAt (frechetTail s alpha) (Ioi 0) 0 := by
  rw [ContinuousWithinAt, frechetTail_zero]
  have heq : (frechetTail s alpha) =ᶠ[nhdsWithin 0 (Ioi 0)] (frechetCore s alpha) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact frechetTail_eq_core hx
  rw [Filter.tendsto_congr' heq]
  simpa [frechetCore] using (frechet_exp_tendsto hs ha).const_sub 1

/-- **(Q2b) Lipschitz** of the Fréchet tail on `[0,1]`, constant
`M := (α/s)(1+1/α)^{1+1/α} e^{-(1+1/α)}`: the interior bound from the density mode,
extended to the boundary by continuity at `0`. -/
theorem frechetTail_lipschitz {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |frechetTail s alpha x - frechetTail s alpha y|
        ≤ ((alpha / s) * (1 + 1 / alpha) ^ (1 + 1 / alpha) * Real.exp (-(1 + 1 / alpha))) * |x - y| := by
  set M := (alpha / s) * (1 + 1 / alpha) ^ (1 + 1 / alpha) * Real.exp (-(1 + 1 / alpha)) with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  -- interior bound for strictly positive arguments
  have hpos_case : ∀ x, 0 < x → x ≤ 1 → ∀ y, 0 < y → y ≤ 1 →
      |frechetTail s alpha x - frechetTail s alpha y| ≤ M * |x - y| := by
    intro x hx0 hx1 y hy0 hy1
    have hsub : uIcc x y ⊆ Ioi (0 : ℝ) := by
      intro z hz
      rw [mem_uIcc] at hz
      rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [exact lt_of_lt_of_le hx0 h1; exact lt_of_lt_of_le hy0 h1]
    have hderiv : ∀ z ∈ uIcc x y,
        HasDerivWithinAt (frechetTail s alpha)
          (-(Real.exp (-((s / z) ^ alpha)) * -(s * -(z ^ 2)⁻¹ * (alpha * (s / z) ^ (alpha - 1)))))
          (uIcc x y) z := by
      intro z hz
      have hz0 : 0 < z := hsub hz
      refine (frechetCore_hasDerivAt hs ha hz0).hasDerivWithinAt.congr
        (fun w hw => frechetTail_eq_core (hsub hw)) (frechetTail_eq_core hz0)
    have hbound : ∀ z ∈ uIcc x y,
        ‖-(Real.exp (-((s / z) ^ alpha)) * -(s * -(z ^ 2)⁻¹ * (alpha * (s / z) ^ (alpha - 1))))‖ ≤ M := by
      intro z hz
      rw [Real.norm_eq_abs]
      exact frechetCore_deriv_abs_le hs ha (hsub hz)
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_uIcc x y)
      (right_mem_uIcc) (left_mem_uIcc)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at key
  -- extend to the boundary x = 0 (and symmetrically y = 0) by continuity at 0
  have hzero_case : ∀ y, 0 ≤ y → y ≤ 1 →
      |frechetTail s alpha 0 - frechetTail s alpha y| ≤ M * |0 - y| := by
    intro y hy0 hy1
    rcases eq_or_lt_of_le hy0 with hy | hy
    · simp [← hy]
    · -- y > 0; take x' → 0⁺ along Ioi 0 in the interior bound
      have hcont : Filter.Tendsto (fun x' => |frechetTail s alpha x' - frechetTail s alpha y|)
          (nhdsWithin 0 (Ioi 0)) (nhds (|frechetTail s alpha 0 - frechetTail s alpha y|)) :=
        ((frechetTail_continuousWithinAt_zero hs ha).sub continuousWithinAt_const).abs
      have hcont2 : Filter.Tendsto (fun x' : ℝ => M * |x' - y|)
          (nhdsWithin 0 (Ioi 0)) (nhds (M * |0 - y|)) :=
        ((continuous_const.mul ((continuous_id.sub continuous_const).abs)).continuousWithinAt)
      have hev : (fun x' => |frechetTail s alpha x' - frechetTail s alpha y|)
          ≤ᶠ[nhdsWithin 0 (Ioi 0)] (fun x' => M * |x' - y|) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
          with x' hx'pos hx'lt
        exact hpos_case x' hx'pos hx'lt.le y hy hy1
      exact le_of_tendsto_of_tendsto hcont hcont2 hev
  -- assemble: reduce all cases to hpos_case / hzero_case
  intro x hx y hy
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · rw [← hx0]; exact hzero_case y hy.1 hy.2
  · rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · rw [← hy0, abs_sub_comm, abs_sub_comm x]
      exact hzero_case x hx.1 hx.2
    · exact hpos_case x hx0 hx.2 y hy0 hy.2

/-- The Fréchet family as a fully-certified `ThresholdPrior` (Q2a + Q2b proved). -/
noncomputable def frechetPrior {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) : ThresholdPrior where
  tail := frechetTail s alpha
  antitone := frechetTail_antitoneOn hs ha
  lipConst := (alpha / s) * (1 + 1 / alpha) ^ (1 + 1 / alpha) * Real.exp (-(1 + 1 / alpha))
  lipschitz := frechetTail_lipschitz hs ha

/-! ## (Q5) Fréchet density unimodality

The (Q5) centro-symmetric max-location turns, as for Hill, on the density's
unimodality: `φ(X) = α s^α X^{-(α+1)} e^{-(s/X)^α}` rises on `(0, χ*_F]` and falls on
`[χ*_F, ∞)`, with peak `χ*_F = s(α/(α+1))^{1/α}`. We obtain it from the sign of
`(log φ)'(X) = (α(s/X)^α − (α+1))/X`, which flips exactly at `χ*_F`. -/

/-- The Fréchet density `φ(X) = α s^α X^{-(α+1)} e^{-(s/X)^α}` (here `-F̄'`). -/
noncomputable def frechetDensity (s alpha X : ℝ) : ℝ :=
  alpha * s ^ alpha * X ^ (-(alpha + 1)) * Real.exp (-((s / X) ^ alpha))

/-- The Fréchet density peak location `χ*_F = s(α/(α+1))^{1/α}`. -/
noncomputable def frechetPeak (s alpha : ℝ) : ℝ := s * (alpha / (alpha + 1)) ^ (1 / alpha)

/-- `log φ(X) = log(α s^α) − (α+1) log X − (s/X)^α`. -/
noncomputable def frechetLogDensity (s alpha X : ℝ) : ℝ :=
  Real.log (alpha * s ^ alpha) - (alpha + 1) * Real.log X - (s / X) ^ alpha

theorem frechetPeak_pos {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) : 0 < frechetPeak s alpha :=
  mul_pos hs (Real.rpow_pos_of_pos (div_pos ha (by linarith)) _)

/-- `(s/χ*_F)^α = (α+1)/α`: the defining property of the Fréchet density peak. -/
theorem frechet_peak_pow {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    (s / frechetPeak s alpha) ^ alpha = (alpha + 1) / alpha := by
  have hb : (0 : ℝ) ≤ alpha / (alpha + 1) := (div_pos ha (by linarith)).le
  have hr : (0 : ℝ) < (alpha / (alpha + 1)) ^ (1 / alpha) := Real.rpow_pos_of_pos (by positivity) _
  have hsa : (0 : ℝ) < s ^ alpha := Real.rpow_pos_of_pos hs alpha
  unfold frechetPeak
  rw [Real.div_rpow hs.le (by positivity), Real.mul_rpow hs.le hr.le,
      ← Real.rpow_mul hb, one_div_mul_cancel (ne_of_gt ha), Real.rpow_one]
  rw [← div_div, div_self (ne_of_gt hsa), one_div_div]

/-- `φ(X) = exp(logφ(X))` for `X > 0`. -/
theorem frechetDensity_eq_exp {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    frechetDensity s alpha X = Real.exp (frechetLogDensity s alpha X) := by
  unfold frechetDensity frechetLogDensity
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log (show (0 : ℝ) < alpha * s ^ alpha by positivity),
      show Real.exp ((alpha + 1) * Real.log X) = X ^ (alpha + 1) from by
        rw [mul_comm, ← Real.rpow_def_of_pos hX],
      Real.exp_neg,
      show X ^ (-(alpha + 1)) = (X ^ (alpha + 1))⁻¹ from by rw [← Real.rpow_neg hX.le]]
  ring

/-- Derivative of `logφ`. -/
theorem frechetLogDensity_hasDerivAt {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (frechetLogDensity s alpha)
      (-((alpha + 1) * X⁻¹) - s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))) X := by
  have hsX : (0 : ℝ) < s / X := div_pos hs hX
  have hlog : HasDerivAt (fun X : ℝ => (alpha + 1) * Real.log X) ((alpha + 1) * X⁻¹) X :=
    (Real.hasDerivAt_log (ne_of_gt hX)).const_mul (alpha + 1)
  have hg : HasDerivAt (fun X : ℝ => (s / X) ^ alpha)
      (s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))) X := by
    have h1 : HasDerivAt (fun X : ℝ => s / X) (s * -(X ^ 2)⁻¹) X := by
      have := (hasDerivAt_inv (ne_of_gt hX)).const_mul s
      simpa [div_eq_mul_inv] using this
    have := h1.rpow_const (p := alpha) (Or.inl (ne_of_gt hsX))
    convert this using 1; ring
  have hd := ((hasDerivAt_const X (Real.log (alpha * s ^ alpha))).sub hlog).sub hg
  convert hd using 1; ring

/-- The `logφ` derivative has the sign of `α(s/X)^α − (α+1)`. -/
theorem frechetLogDensity_deriv_eq {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    -((alpha + 1) * X⁻¹) - s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))
      = (alpha * (s / X) ^ alpha - (alpha + 1)) / X := by
  have hsX : (0 : ℝ) < s / X := div_pos hs hX
  have e1 : (s / X) ^ alpha = (s / X) ^ (alpha - 1) * (s / X) := by
    rw [← Real.rpow_add_one (ne_of_gt hsX), sub_add_cancel]
  rw [e1]; field_simp; ring

theorem frechetLogDensity_strictMonoOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    StrictMonoOn (frechetLogDensity s alpha) (Ioc 0 (frechetPeak s alpha)) := by
  have hχ : 0 < frechetPeak s alpha := frechetPeak_pos hs ha
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (frechetPeak s alpha))
    (fun x hx => (frechetLogDensity_hasDerivAt hs ha hx.1).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ioc, mem_Ioo] at hx
  rw [(frechetLogDensity_hasDerivAt hs ha hx.1).deriv, frechetLogDensity_deriv_eq hs ha hx.1]
  apply div_pos _ hx.1
  have hgt : (s / frechetPeak s alpha) ^ alpha < (s / x) ^ alpha :=
    Real.rpow_lt_rpow (div_pos hs hχ).le (div_lt_div_of_pos_left hs hx.1 hx.2) ha
  rw [frechet_peak_pow hs ha] at hgt
  have := (div_lt_iff₀ ha).mp hgt
  nlinarith [this]

theorem frechetLogDensity_strictAntiOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    StrictAntiOn (frechetLogDensity s alpha) (Ici (frechetPeak s alpha)) := by
  have hχ : 0 < frechetPeak s alpha := frechetPeak_pos hs ha
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    (fun x hx => (frechetLogDensity_hasDerivAt hs ha (lt_of_lt_of_le hχ hx)).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hx0 : 0 < x := lt_trans hχ hx
  rw [(frechetLogDensity_hasDerivAt hs ha hx0).deriv, frechetLogDensity_deriv_eq hs ha hx0]
  apply div_neg_of_neg_of_pos _ hx0
  have hlt : (s / x) ^ alpha < (s / frechetPeak s alpha) ^ alpha :=
    Real.rpow_lt_rpow (div_pos hs hx0).le (div_lt_div_of_pos_left hs hχ hx) ha
  rw [frechet_peak_pow hs ha] at hlt
  have := (lt_div_iff₀ ha).mp hlt
  nlinarith [this]

/-- **Rising tail of the Fréchet density**: strictly increasing on `(0, χ*_F]`. -/
theorem frechetDensity_strictMonoOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    StrictMonoOn (frechetDensity s alpha) (Ioc 0 (frechetPeak s alpha)) := by
  have heq : EqOn (frechetDensity s alpha) (Real.exp ∘ frechetLogDensity s alpha)
      (Ioc 0 (frechetPeak s alpha)) := fun x hx => frechetDensity_eq_exp hs ha hx.1
  exact (Real.exp_strictMono.comp_strictMonoOn (frechetLogDensity_strictMonoOn hs ha)).congr heq.symm

/-- **Falling tail of the Fréchet density**: strictly decreasing on `[χ*_F, ∞)`. -/
theorem frechetDensity_strictAntiOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    StrictAntiOn (frechetDensity s alpha) (Ici (frechetPeak s alpha)) := by
  have heq : EqOn (frechetDensity s alpha) (Real.exp ∘ frechetLogDensity s alpha)
      (Ici (frechetPeak s alpha)) :=
    fun x hx => frechetDensity_eq_exp hs ha (lt_of_lt_of_le (frechetPeak_pos hs ha) hx)
  exact (Real.exp_strictMono.comp_strictAntiOn (frechetLogDensity_strictAntiOn hs ha)).congr heq.symm

/-- **The convexity core of the Fréchet right-skew.** For `t ∈ (0,1)`, `α > 0`:
`1/(1+t) + 1/(1-t) < (1-t)^{-(α+1)} + (1+t)^{-(α+1)}`. Equivalent (clearing the
positive factor `(1-t²)^{α+1}`) to `2(1-t²)^α < (1-t)^{α+1}+(1+t)^{α+1}`, which holds
because `x^{α+1}` is convex (midpoint at `1` gives `≥ 2`) while `(1-t²)^α < 1`. -/
theorem frechet_skewH_pos {alpha t : ℝ} (ha : 0 < alpha) (ht0 : 0 < t) (ht1 : t < 1) :
    1 / (1 + t) + 1 / (1 - t) < (1 - t) ^ (-(alpha + 1)) + (1 + t) ^ (-(alpha + 1)) := by
  have ha1 : (0 : ℝ) < 1 - t := by linarith
  have hb1 : (0 : ℝ) < 1 + t := by linarith
  have hab : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hP : (0 : ℝ) < (1 - t ^ 2) ^ (alpha + 1) := Real.rpow_pos_of_pos hab _
  -- convexity: 2 ≤ (1-t)^{α+1} + (1+t)^{α+1}
  have hconv : (2 : ℝ) ≤ (1 - t) ^ (alpha + 1) + (1 + t) ^ (alpha + 1) := by
    have hc := (convexOn_rpow (by linarith : (1 : ℝ) ≤ alpha + 1)).2
      (mem_Ici.mpr ha1.le) (mem_Ici.mpr hb1.le)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
    simp only [smul_eq_mul] at hc
    rw [show (1 : ℝ) / 2 * (1 - t) + 1 / 2 * (1 + t) = 1 by ring, Real.one_rpow] at hc
    linarith
  have hlt1 : (1 - t ^ 2) ^ alpha < 1 := Real.rpow_lt_one hab.le (by nlinarith) ha
  have hkey : 2 * (1 - t ^ 2) ^ alpha < (1 - t) ^ (alpha + 1) + (1 + t) ^ (alpha + 1) := by
    linarith
  -- clear (1-t²)^{α+1} from the target
  have hmul : (1 - t ^ 2) ^ (alpha + 1) = (1 - t) ^ (alpha + 1) * (1 + t) ^ (alpha + 1) := by
    rw [show (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) by ring, Real.mul_rpow ha1.le hb1.le]
  have hA : ((1 - t) ^ (alpha + 1)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha1 _)
  have hB : ((1 + t) ^ (alpha + 1)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb1 _)
  have eR : ((1 - t) ^ (-(alpha + 1)) + (1 + t) ^ (-(alpha + 1))) * (1 - t ^ 2) ^ (alpha + 1)
      = (1 - t) ^ (alpha + 1) + (1 + t) ^ (alpha + 1) := by
    rw [hmul, Real.rpow_neg ha1.le, Real.rpow_neg hb1.le]
    field_simp
    ring
  have eL : (1 / (1 + t) + 1 / (1 - t)) * (1 - t ^ 2) ^ (alpha + 1) = 2 * (1 - t ^ 2) ^ alpha := by
    have hsum : 1 / (1 + t) + 1 / (1 - t) = 2 / (1 - t ^ 2) := by
      rw [show (1 : ℝ) - t ^ 2 = (1 + t) * (1 - t) by ring]; field_simp; ring
    rw [hsum, Real.rpow_add_one (ne_of_gt hab)]
    field_simp
  have hLP : (1 / (1 + t) + 1 / (1 - t)) * (1 - t ^ 2) ^ (alpha + 1)
      < ((1 - t) ^ (-(alpha + 1)) + (1 + t) ^ (-(alpha + 1))) * (1 - t ^ 2) ^ (alpha + 1) := by
    rw [eL, eR]; exact hkey
  exact lt_of_mul_lt_mul_right hLP hP.le

/-- The right-skew comparison function `G(t)`, with `G(0)=0` and `G' = H > 0`. -/
noncomputable def frechetG (alpha t : ℝ) : ℝ :=
  (1 / alpha) * ((1 - t) ^ (-alpha) - (1 + t) ^ (-alpha)) - (Real.log (1 + t) - Real.log (1 - t))

theorem frechetG_zero (alpha : ℝ) : frechetG alpha 0 = 0 := by
  unfold frechetG; simp [Real.one_rpow]

theorem frechetG_hasDerivAt {alpha t : ℝ} (ha : 0 < alpha) (ha1 : 0 < 1 - t) (hb1 : 0 < 1 + t) :
    HasDerivAt (frechetG alpha)
      ((1 - t) ^ (-(alpha + 1)) + (1 + t) ^ (-(alpha + 1)) - (1 / (1 + t) + 1 / (1 - t))) t := by
  have d1mt : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by simpa using (hasDerivAt_id t).const_sub 1
  have d1pt : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by simpa using (hasDerivAt_id t).const_add 1
  have da : HasDerivAt (fun t : ℝ => (1 - t) ^ (-alpha)) (alpha * (1 - t) ^ (-(alpha + 1))) t := by
    have h := d1mt.rpow_const (p := -alpha) (Or.inl (ne_of_gt ha1))
    rw [show -alpha - 1 = -(alpha + 1) by ring] at h
    convert h using 1; ring
  have db : HasDerivAt (fun t : ℝ => (1 + t) ^ (-alpha)) (-(alpha * (1 + t) ^ (-(alpha + 1)))) t := by
    have h := d1pt.rpow_const (p := -alpha) (Or.inl (ne_of_gt hb1))
    rw [show -alpha - 1 = -(alpha + 1) by ring] at h
    convert h using 1; ring
  have dlogp : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
    have := d1pt.log (ne_of_gt hb1); simpa using this
  have dlogm : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - t)) t := by
    have := d1mt.log (ne_of_gt ha1); simpa using this
  have hd := (((da.sub db).const_mul (1 / alpha)).sub (dlogp.sub dlogm))
  convert hd using 1
  field_simp
  ring

theorem frechetG_pos {alpha t : ℝ} (ha : 0 < alpha) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < frechetG alpha t := by
  have hmono : StrictMonoOn (frechetG alpha) (Ico 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
      (fun x hx => (frechetG_hasDerivAt ha (by linarith [hx.2]) (by linarith [hx.1])).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ico, mem_Ioo] at hx
    rw [(frechetG_hasDerivAt ha (by linarith [hx.2]) (by linarith [hx.1])).deriv]
    have := frechet_skewH_pos ha hx.1 hx.2
    linarith [this]
  have := hmono (left_mem_Ico.mpr (by norm_num)) ⟨ht0.le, ht1⟩ ht0
  rwa [frechetG_zero] at this

theorem frechetDensity_zero {s alpha : ℝ} (ha : 0 < alpha) : frechetDensity s alpha 0 = 0 := by
  unfold frechetDensity
  rw [Real.zero_rpow (by linarith : -(alpha + 1) ≠ 0)]; ring

theorem frechetDensity_pos {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    0 < frechetDensity s alpha X := by
  unfold frechetDensity
  have : (0:ℝ) < X ^ (-(alpha+1)) := Real.rpow_pos_of_pos hX _
  have hsa : (0:ℝ) < s ^ alpha := Real.rpow_pos_of_pos hs alpha
  positivity

/-- The log-density difference across the peak equals `(α+1)·G(t)`. -/
theorem frechetLogDensity_diff {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {t : ℝ}
    (h1m : 0 < 1 - t) (h1p : 0 < 1 + t) :
    frechetLogDensity s alpha (frechetPeak s alpha * (1 + t))
        - frechetLogDensity s alpha (frechetPeak s alpha * (1 - t))
      = (alpha + 1) * frechetG alpha t := by
  have hχ : 0 < frechetPeak s alpha := frechetPeak_pos hs ha
  have es : ∀ u : ℝ, 0 < u → (s / (frechetPeak s alpha * u)) ^ alpha
      = (alpha + 1) / alpha * u ^ (-alpha) := by
    intro u hu
    rw [show s / (frechetPeak s alpha * u) = (s / frechetPeak s alpha) * u⁻¹ from by
          field_simp,
        Real.mul_rpow (div_pos hs hχ).le (inv_nonneg.mpr hu.le), frechet_peak_pow hs ha,
        Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
  unfold frechetLogDensity frechetG
  rw [Real.log_mul (ne_of_gt hχ) (ne_of_gt h1p), Real.log_mul (ne_of_gt hχ) (ne_of_gt h1m),
      es (1 + t) h1p, es (1 - t) h1m]
  ring

/-- **Lemma B.1(a) analog for Fréchet: right-skew at the peak.**
`φ(χ*_F - δ) < φ(χ*_F + δ)` for `δ ∈ (0, χ*_F]`. -/
theorem frechetDensity_right_skew {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ frechetPeak s alpha) :
    frechetDensity s alpha (frechetPeak s alpha - δ) < frechetDensity s alpha (frechetPeak s alpha + δ) := by
  have hχ : 0 < frechetPeak s alpha := frechetPeak_pos hs ha
  rcases lt_or_eq_of_le hδle with hlt | heq
  · set t := δ / frechetPeak s alpha with ht_def
    have ht0 : 0 < t := div_pos hδ hχ
    have ht1 : t < 1 := by rw [ht_def, div_lt_one hχ]; exact hlt
    have h1m : (0:ℝ) < 1 - t := by linarith
    have h1p : (0:ℝ) < 1 + t := by linarith
    have e_plus : frechetPeak s alpha + δ = frechetPeak s alpha * (1 + t) := by
      rw [ht_def]; field_simp
    have e_minus : frechetPeak s alpha - δ = frechetPeak s alpha * (1 - t) := by
      rw [ht_def]; field_simp
    rw [e_plus, e_minus,
        frechetDensity_eq_exp hs ha (by positivity), frechetDensity_eq_exp hs ha (by positivity),
        Real.exp_lt_exp]
    have hdiff := frechetLogDensity_diff hs ha h1m h1p
    have hGpos := frechetG_pos ha ht0 ht1
    nlinarith [hdiff, hGpos]
  · subst heq
    rw [sub_self, frechetDensity_zero ha]
    exact frechetDensity_pos hs ha (by linarith)

/-- The scalar identity `s·(X²)⁻¹·α·(s/X)^{α-1} = α s^α X^{-(α+1)}`. -/
theorem frechet_scalar_id {s alpha : ℝ} (hs : 0 < s) {X : ℝ} (hX : 0 < X) :
    s * (X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)) = alpha * s ^ alpha * X ^ (-(alpha + 1)) := by
  have hX2 : (X ^ 2)⁻¹ = X ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast X 2, ← Real.rpow_neg hX.le]; norm_num
  have hdiv : (s / X) ^ (alpha - 1) = s ^ (alpha - 1) * X ^ (-(alpha - 1)) := by
    rw [Real.div_rpow hs.le hX.le, div_eq_mul_inv, ← Real.rpow_neg hX.le]
  have hss : s * s ^ (alpha - 1) = s ^ alpha := by
    rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hs)]; congr 1; ring
  have hXX : X ^ (-(2 : ℝ)) * X ^ (-(alpha - 1)) = X ^ (-(alpha + 1)) := by
    rw [← Real.rpow_add hX]; congr 1; ring
  rw [hX2, hdiv]
  rw [show s * X ^ (-(2 : ℝ)) * (alpha * (s ^ (alpha - 1) * X ^ (-(alpha - 1))))
        = alpha * (s * s ^ (alpha - 1)) * (X ^ (-(2 : ℝ)) * X ^ (-(alpha - 1))) by ring]
  rw [hss, hXX]

theorem frechetTail_hasDerivAt {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (frechetTail s alpha) (-(frechetDensity s alpha X)) X := by
  have hcore := frechetCore_hasDerivAt hs ha hX
  have hval : -(Real.exp (-((s / X) ^ alpha)) * -(s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))))
      = -(frechetDensity s alpha X) := by
    unfold frechetDensity
    rw [show -(Real.exp (-((s / X) ^ alpha)) * -(s * -(X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1))))
          = -(Real.exp (-((s / X) ^ alpha)) * (s * (X ^ 2)⁻¹ * (alpha * (s / X) ^ (alpha - 1)))) by ring,
        frechet_scalar_id hs hX]
    ring
  rw [hval] at hcore
  have heq : frechetTail s alpha =ᶠ[nhds X] frechetCore s alpha := by
    filter_upwards [Ioi_mem_nhds hX] with y hy; exact frechetTail_eq_core hy
  exact hcore.congr_of_eventuallyEq heq

/-- **Lemma B.1(b) analog for Fréchet (Regime II pointwise).** Under `χ*_F ≥ 1/2`,
`φ(X) ≤ φ(1-X)` for `X ∈ [0,1/2]`. -/
theorem frechet_right_skew_centro {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha)
    (hχ : 1 / 2 ≤ frechetPeak s alpha) {X : ℝ} (hX0 : 0 ≤ X) (hXhalf : X ≤ 1 / 2) :
    frechetDensity s alpha X ≤ frechetDensity s alpha (1 - X) := by
  have hχpos : 0 < frechetPeak s alpha := frechetPeak_pos hs ha
  rcases eq_or_lt_of_le hX0 with hX0' | hX0'
  · rw [← hX0', frechetDensity_zero ha, sub_zero]
    exact (frechetDensity_pos hs ha one_pos).le
  · have hmono := (frechetDensity_strictMonoOn hs ha).monotoneOn
    have hXle : X ≤ frechetPeak s alpha := le_trans hXhalf hχ
    by_cases hc : 1 - X ≤ frechetPeak s alpha
    · exact hmono ⟨hX0', hXle⟩ ⟨by linarith, hc⟩ (by linarith)
    · rw [not_le] at hc
      set Δ2 := (1 - X) - frechetPeak s alpha with hΔ2
      have hΔ2pos : 0 < Δ2 := by rw [hΔ2]; linarith
      have hΔ2le : Δ2 ≤ frechetPeak s alpha := by rw [hΔ2]; nlinarith [hχ, hX0]
      have e1X : 1 - X = frechetPeak s alpha + Δ2 := by rw [hΔ2]; ring
      have hskew := frechetDensity_right_skew hs ha hΔ2pos hΔ2le
      have hXle2 : X ≤ frechetPeak s alpha - Δ2 := by rw [hΔ2]; nlinarith [hχ]
      have hge0 : 0 < frechetPeak s alpha - Δ2 := by rw [hΔ2]; nlinarith [hχ, hX0']
      have hlt : frechetDensity s alpha X < frechetDensity s alpha (1 - X) :=
        calc frechetDensity s alpha X
            ≤ frechetDensity s alpha (frechetPeak s alpha - Δ2) :=
              hmono ⟨hX0', hXle⟩ ⟨hge0, by linarith [hΔ2pos]⟩ hXle2
          _ < frechetDensity s alpha (frechetPeak s alpha + Δ2) := hskew
          _ = frechetDensity s alpha (1 - X) := by rw [← e1X]
      exact hlt.le

/-- Right-continuity of the Fréchet tail at `0` within `Ici 0`. -/
theorem frechetTail_continuousWithinAt_zero_Ici {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    ContinuousWithinAt (frechetTail s alpha) (Ici 0) 0 := by
  have h := frechetTail_continuousWithinAt_zero hs ha
  have hu := (continuousWithinAt_singleton).union h
  rwa [show ({0} : Set ℝ) ∪ Ioi 0 = Ici 0 from by
    rw [Set.union_comm]; exact Set.Ioi_union_left] at hu

/-- Continuity of the Fréchet tail on `[0,1]`. -/
theorem frechetTail_continuousOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    ContinuousOn (frechetTail s alpha) (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    exact (continuousWithinAt_Icc_iff_Ici (by norm_num : (0 : ℝ) < 1)).mpr
      (frechetTail_continuousWithinAt_zero_Ici hs ha)
  · have hsx : ContinuousAt (fun X : ℝ => s / X) x :=
      continuousAt_const.div continuousAt_id (ne_of_gt hx0)
    have hpow : ContinuousAt (fun X : ℝ => (s / X) ^ alpha) x :=
      hsx.rpow_const (Or.inl (ne_of_gt (div_pos hs hx0)))
    have hcore : ContinuousAt (frechetCore s alpha) x := by
      unfold frechetCore
      exact continuousAt_const.sub (Real.continuous_exp.continuousAt.comp hpow.neg)
    have heq : frechetTail s alpha =ᶠ[nhds x] frechetCore s alpha := by
      filter_upwards [Ioi_mem_nhds hx0] with y hy; exact frechetTail_eq_core hy
    exact (hcore.congr heq.symm).continuousWithinAt

/-- **Fréchet (Q5), Regime II** (`χ*_F ≥ 1/2`): the centro-symmetric pair-sum
`g(X) = h(X) + h(1-X)` is non-decreasing on `[0,1/2]`, so its max sits at `X = 1/2`. -/
theorem frechetPairSum_monotoneOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha)
    (hχ : 1 / 2 ≤ frechetPeak s alpha) :
    MonotoneOn (fun X => frechetTail s alpha X + frechetTail s alpha (1 - X)) (Icc 0 (1 / 2)) := by
  have hcont : ContinuousOn (fun X => frechetTail s alpha X + frechetTail s alpha (1 - X))
      (Icc 0 (1 / 2)) := by
    apply ContinuousOn.add
      ((frechetTail_continuousOn hs ha).mono (Icc_subset_Icc le_rfl (by norm_num)))
    apply (frechetTail_continuousOn hs ha).comp ((continuous_const.sub continuous_id).continuousOn)
    intro x hx; simp only [Set.mem_Icc, id_eq] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) (1 / 2)),
      HasDerivAt (fun X => frechetTail s alpha X + frechetTail s alpha (1 - X))
        (-(frechetDensity s alpha x) + frechetDensity s alpha (1 - x)) x := by
    intro x hx
    rw [interior_Icc, mem_Ioo] at hx
    have hx0 : 0 < x := hx.1
    have h1mx : 0 < 1 - x := by linarith [hx.2]
    have hinner : HasDerivAt (fun X : ℝ => 1 - X) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hcomp : HasDerivAt (fun X => frechetTail s alpha (1 - X)) (frechetDensity s alpha (1 - x)) x := by
      have := (frechetTail_hasDerivAt hs ha h1mx).comp x hinner; simpa using this
    exact (frechetTail_hasDerivAt hs ha hx0).add hcomp
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) hcont
  · exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hderiv x hx).deriv]
    rw [interior_Icc, mem_Ioo] at hx
    have := frechet_right_skew_centro hs ha hχ hx.1.le (le_of_lt hx.2)
    linarith

/-- The Fréchet density vanishes at the origin in the limit: `φ(X) → 0` as `X → 0⁺`
(the exp factor beats the `X^{-(α+1)}` blow-up). -/
theorem frechetDensity_tendsto_zero {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    Filter.Tendsto (frechetDensity s alpha) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hv : Filter.Tendsto (fun X : ℝ => (s / X) ^ alpha) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
    have hinv : Filter.Tendsto (fun X : ℝ => s / X) (nhdsWithin 0 (Ioi 0)) Filter.atTop := by
      simpa [div_eq_mul_inv, mul_comm] using tendsto_inv_nhdsGT_zero.const_mul_atTop hs
    exact (tendsto_rpow_atTop ha).comp hinv
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((alpha + 1) / alpha) 1 one_pos
  have hcomp := (hlim.comp hv).const_mul (alpha / s)
  rw [mul_zero] at hcomp
  refine (Filter.tendsto_congr' ?_).mpr hcomp
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hX0 : (0 : ℝ) < X := hX
  have hsX : (0 : ℝ) < s / X := div_pos hs hX0
  unfold frechetDensity
  simp only [Function.comp]
  rw [← Real.rpow_mul hsX.le, show alpha * ((alpha + 1) / alpha) = alpha + 1 by field_simp,
      show (-1 : ℝ) * (s / X) ^ alpha = -((s / X) ^ alpha) by ring,
      show (s / X) ^ (alpha + 1) = s ^ (alpha + 1) * (X ^ (alpha + 1))⁻¹ from by
        rw [Real.div_rpow hs.le hX0.le, div_eq_mul_inv],
      show X ^ (-(alpha + 1)) = (X ^ (alpha + 1))⁻¹ from by rw [← Real.rpow_neg hX0.le],
      Real.rpow_add_one (ne_of_gt hs)]
  field_simp

/-- Continuity of the Fréchet density on `[0,1]` (with `φ(0) = 0`). -/
theorem frechetDensity_continuousOn {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    ContinuousOn (frechetDensity s alpha) (Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    rw [continuousWithinAt_Icc_iff_Ici (by norm_num : (0 : ℝ) < 1)]
    have hIoi : ContinuousWithinAt (frechetDensity s alpha) (Ioi 0) 0 := by
      rw [ContinuousWithinAt, frechetDensity_zero ha]; exact frechetDensity_tendsto_zero hs ha
    have hIci := (continuousWithinAt_singleton).union hIoi
    rwa [show ({0} : Set ℝ) ∪ Ioi 0 = Ici 0 from by
      rw [Set.union_comm]; exact Set.Ioi_union_left] at hIci
  · have h1 : ContinuousAt (fun X : ℝ => X ^ (-(alpha + 1))) x :=
      continuousAt_id.rpow_const (Or.inl (ne_of_gt hx0))
    have hsx : ContinuousAt (fun X : ℝ => s / X) x :=
      continuousAt_const.div continuousAt_id (ne_of_gt hx0)
    have hexp : ContinuousAt (fun X : ℝ => Real.exp (-((s / X) ^ alpha))) x :=
      Real.continuous_exp.continuousAt.comp
        ((hsx.rpow_const (Or.inl (ne_of_gt (div_pos hs hx0)))).neg)
    have hcont : ContinuousAt (frechetDensity s alpha) x := by
      unfold frechetDensity; exact (continuousAt_const.mul h1).mul hexp
    exact hcont.continuousWithinAt

/-- **Fréchet (Q5), Regime III** (`χ*_F < 1/2`): the pair-sum has an interior
critical point in `(0, χ*_F)` where `φ(1-X₀) = φ(X₀)`, by the IVT on
`g'(X) = φ(1-X) - φ(X)` (positive at `0`, negative at `χ*_F`). -/
theorem regimeIII_interior_critical_frechet {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha)
    (hχ : frechetPeak s alpha < 1 / 2) :
    ∃ X0 ∈ Ioo (0 : ℝ) (frechetPeak s alpha),
      frechetDensity s alpha (1 - X0) = frechetDensity s alpha X0 := by
  have hχpos : 0 < frechetPeak s alpha := frechetPeak_pos hs ha
  set gp : ℝ → ℝ := fun X => frechetDensity s alpha (1 - X) - frechetDensity s alpha X with hgp
  have hcont : ContinuousOn gp (Icc 0 (frechetPeak s alpha)) := by
    apply ContinuousOn.sub
    · apply (frechetDensity_continuousOn hs ha).comp ((continuous_const.sub continuous_id).continuousOn)
      intro x hx; simp only [mem_Icc, id_eq] at hx ⊢; constructor <;> linarith [hx.1, hx.2, hχ]
    · exact (frechetDensity_continuousOn hs ha).mono (Icc_subset_Icc le_rfl (by linarith))
  have hpos0 : 0 < gp 0 := by
    rw [hgp]; simp only [sub_zero]; rw [frechetDensity_zero ha]
    simpa using frechetDensity_pos hs ha one_pos
  have hneg : gp (frechetPeak s alpha) < 0 := by
    rw [hgp]; simp only
    have hanti := frechetDensity_strictAntiOn hs ha
    have : frechetDensity s alpha (1 - frechetPeak s alpha) < frechetDensity s alpha (frechetPeak s alpha) :=
      hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
    linarith
  obtain ⟨X0, hX0mem, hX0val⟩ := regimeIII_interior_critical hχpos hcont hpos0 hneg
  exact ⟨X0, hX0mem, sub_eq_zero.mp hX0val⟩

end TwoGenie
