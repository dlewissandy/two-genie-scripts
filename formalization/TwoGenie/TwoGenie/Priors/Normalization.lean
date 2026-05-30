import TwoGenie.Priors.Hill
import TwoGenie.Priors.Pareto
import TwoGenie.Priors.Lomax
import TwoGenie.Priors.Frechet

/-!
# (Q1): every threshold prior is a genuine probability density

The (Q1) burden of \S5 -- that each prior density integrates to `1` over its
support -- discharged uniformly for all four families. The common engine is the
improper Fundamental Theorem of Calculus: if the survival tail `F̄` has derivative
`-density`, is continuous at the left endpoint, and tends to `0` at `+∞`, then
`∫ density = F̄(left endpoint) - 0 = 1`. The standard parametrizations are already
normalized, so no rescaling is needed; the integral closes to `F̄(a) = 1` exactly.
-/

set_option linter.unusedVariables false

namespace TwoGenie

open Set Filter MeasureTheory

/-- **Uniform (Q1).** A threshold density integrates to `1` over `(a,∞)` whenever its
tail `F̄` is continuous at `a`, has derivative `-density` on `(a,∞)`, the density is
nonnegative, and `F̄ → 0` at `∞`. By the improper FTC, `∫ = F̄(a) − 0 = F̄(a)`. -/
theorem prior_density_integral {a : ℝ} {tail dens : ℝ → ℝ}
    (hcont : ContinuousWithinAt tail (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt tail (-(dens x)) x)
    (hdens : ∀ x ∈ Ioi a, 0 ≤ dens x)
    (htend : Tendsto tail atTop (nhds 0)) :
    ∫ x in Ioi a, dens x = tail a := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg (g := fun x => -tail x) (g' := dens) (a := a)
    hcont.neg (fun x hx => by simpa using (hderiv x hx).neg) hdens (by simpa using htend.neg)
  simpa using h

theorem lomax_integral_eq_one {lam alpha : ℝ} (hlam : 0 < lam) (ha : 0 < alpha) :
    ∫ x in Ioi (0 : ℝ), lomaxDensity lam alpha x = 1 := by
  have hcont : ContinuousWithinAt (lomaxTail lam alpha) (Ici 0) 0 :=
    (lomaxTail_hasDeriv hlam (le_refl 0)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (lomaxTail lam alpha) (-(lomaxDensity lam alpha x)) x :=
    fun x hx => lomaxTail_hasDeriv hlam (le_of_lt hx)
  have hdens : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ lomaxDensity lam alpha x := by
    intro x hx
    have hbase : 0 < 1 + x / lam := lomax_base_pos hlam (le_of_lt hx)
    unfold lomaxDensity; positivity
  have htend : Tendsto (lomaxTail lam alpha) atTop (nhds 0) := by
    unfold lomaxTail
    have hb : Tendsto (fun X : ℝ => 1 + X / lam) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 (tendsto_id.atTop_div_const hlam)
    exact (tendsto_rpow_neg_atTop ha).comp hb
  have h := prior_density_integral hcont hderiv hdens htend
  rwa [lomaxTail_zero hlam] at h

theorem hill_integral_eq_one {K n : ℝ} (hK : 0 < K) (hn : 1 ≤ n) :
    ∫ x in Ioi (0 : ℝ), hillDensity K n x = 1 := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hcont : ContinuousWithinAt (hillTail K n) (Ici 0) 0 :=
    (hillTail_hasDeriv hK hn (le_refl 0)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (hillTail K n) (-(hillDensity K n x)) x :=
    fun x hx => hillTail_hasDeriv hK hn (le_of_lt hx)
  have hdens : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ hillDensity K n x := by
    intro x hx
    have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
    have hxn1 : 0 ≤ x ^ (n - 1) := Real.rpow_nonneg (le_of_lt hx) _
    have hxn : 0 ≤ x ^ n := Real.rpow_nonneg (le_of_lt hx) n
    unfold hillDensity; positivity
  have htend : Tendsto (hillTail K n) atTop (nhds 0) := by
    unfold hillTail
    have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
    have hb : Tendsto (fun X : ℝ => K ^ n + X ^ n) atTop atTop :=
      tendsto_atTop_add_const_left atTop (K ^ n) (tendsto_rpow_atTop hn0)
    exact hb.const_div_atTop (K ^ n)
  have h := prior_density_integral hcont hderiv hdens htend
  rwa [hillTail_zero hK hn] at h

theorem pareto_integral_eq_one {xm alpha : ℝ} (hxm : 0 < xm) (ha : 0 < alpha) :
    ∫ x in Ioi xm, paretoSmoothDensity xm alpha x = 1 := by
  have heqOn : EqOn (paretoTail xm alpha) (fun x => (xm / x) ^ alpha) (Ici xm) := by
    intro x hx; unfold paretoTail
    rcases eq_or_lt_of_le (mem_Ici.mp hx) with h | h
    · rw [← h]; simp [div_self (ne_of_gt hxm)]
    · rw [if_neg (not_le.mpr h)]
  have hcontAt : ContinuousAt (fun x => (xm / x) ^ alpha) xm :=
    (continuousAt_const.div continuousAt_id (ne_of_gt hxm)).rpow_const
      (Or.inl (ne_of_gt (div_pos hxm hxm)))
  have hcont : ContinuousWithinAt (paretoTail xm alpha) (Ici xm) xm :=
    (hcontAt.continuousWithinAt).congr heqOn (heqOn (Set.self_mem_Ici))
  have hderiv : ∀ x ∈ Ioi xm, HasDerivAt (paretoTail xm alpha) (-(paretoSmoothDensity xm alpha x)) x := by
    intro x hx
    have hd := paretoSmooth_hasDeriv (α := alpha) hxm (lt_trans hxm hx)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold paretoTail; rw [if_neg (not_le.mpr hy)]
  have hdens : ∀ x ∈ Ioi xm, 0 ≤ paretoSmoothDensity xm alpha x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hxm hx
    unfold paretoSmoothDensity
    have hxn : 0 ≤ x ^ (-alpha - 1) := Real.rpow_nonneg hx0.le _
    have hxm' : 0 ≤ xm ^ alpha := Real.rpow_nonneg hxm.le _
    positivity
  have htend : Tendsto (paretoTail xm alpha) atTop (nhds 0) := by
    have he : paretoTail xm alpha =ᶠ[atTop] (fun x => xm ^ alpha * x ^ (-alpha)) := by
      filter_upwards [eventually_gt_atTop xm, eventually_gt_atTop 0] with x hxm' hx0
      unfold paretoTail
      rw [if_neg (not_le.mpr hxm'), Real.div_rpow hxm.le hx0.le, div_eq_mul_inv, ← Real.rpow_neg hx0.le]
    rw [tendsto_congr' he]
    simpa using (tendsto_rpow_neg_atTop ha).const_mul (xm ^ alpha)
  have h := prior_density_integral hcont hderiv hdens htend
  rwa [show paretoTail xm alpha xm = 1 from by unfold paretoTail; rw [if_pos le_rfl]] at h

theorem frechet_integral_eq_one {s alpha : ℝ} (hs : 0 < s) (ha : 0 < alpha) :
    ∫ x in Ioi (0 : ℝ), frechetDensity s alpha x = 1 := by
  have hcont : ContinuousWithinAt (frechetTail s alpha) (Ici 0) 0 :=
    frechetTail_continuousWithinAt_zero_Ici hs ha
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (frechetTail s alpha) (-(frechetDensity s alpha x)) x :=
    fun x hx => frechetTail_hasDerivAt hs ha hx
  have hdens : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ frechetDensity s alpha x :=
    fun x hx => (frechetDensity_pos hs ha hx).le
  have htend : Tendsto (frechetTail s alpha) atTop (nhds 0) := by
    have he : frechetTail s alpha =ᶠ[atTop] (fun x => 1 - Real.exp (-((s / x) ^ alpha))) := by
      filter_upwards [eventually_gt_atTop 0] with x hx; exact frechetTail_eq_core hx
    rw [tendsto_congr' he]
    have h1 : Tendsto (fun x : ℝ => (s / x) ^ alpha) atTop (nhds 0) := by
      have he1 : (fun x : ℝ => (s / x) ^ alpha) =ᶠ[atTop] (fun x => s ^ alpha * x ^ (-alpha)) := by
        filter_upwards [eventually_gt_atTop 0] with x hx
        rw [Real.div_rpow hs.le hx.le, div_eq_mul_inv, ← Real.rpow_neg hx.le]
      rw [tendsto_congr' he1]
      simpa using (tendsto_rpow_neg_atTop ha).const_mul (s ^ alpha)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-((s / x) ^ alpha))) atTop (nhds 1) := by
      have := (Real.continuous_exp.tendsto 0).comp (by simpa using h1.neg)
      simpa using this
    simpa using h2.const_sub 1
  have h := prior_density_integral hcont hderiv hdens htend
  rwa [frechetTail_zero] at h

end TwoGenie
