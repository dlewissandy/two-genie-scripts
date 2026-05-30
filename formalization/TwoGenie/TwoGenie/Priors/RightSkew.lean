import TwoGenie.Priors.Hill

/-!
# Lemma B.1, general `n > 1`: right-skew of the Hill density

The full `H(t)/H'(t)` construction (manuscript §B). With `t = δ/χ*` and
`(χ*)^n = K^n(n-1)/(n+1)`, the density ratio `φ(χ*+δ)/φ(χ*-δ)` equals
`((1+t)/(1-t))^{n-1}(B/A)^2`, and its log `f` has `f' = 2(n²-1)H/[(1-t²)AB]`
with `H(0)=0`, `H'(t) > 0` on `(0,1)`. So `H>0 ⟹ f'>0 ⟹ f>0 ⟹` ratio `> 1`.
-/

namespace TwoGenie

open Set

set_option linter.unusedVariables false

/-- `A(t) = (n+1) + (n-1)(1+t)^n`. -/
noncomputable def Afn (n t : ℝ) : ℝ := (n + 1) + (n - 1) * (1 + t) ^ n

/-- `B(t) = (n+1) + (n-1)(1-t)^n`. -/
noncomputable def Bfn (n t : ℝ) : ℝ := (n + 1) + (n - 1) * (1 - t) ^ n

/-- `H(t)` of the manuscript. -/
noncomputable def Hfn (n t : ℝ) : ℝ :=
  (n + 1) + (n - 1) * ((1 + t) ^ n + (1 - t) ^ n)
    - n * ((1 - t ^ 2) * ((1 + t) ^ (n - 1) + (1 - t) ^ (n - 1)))
    - (n - 1) * (1 - t ^ 2) ^ n

/-- `H'(t) = n(n+1)t[(1+t)^{n-1}+(1-t)^{n-1}] + 2n(n-1)t(1-t²)^{n-1}`. -/
noncomputable def Hp (n t : ℝ) : ℝ :=
  n * (n + 1) * t * ((1 + t) ^ (n - 1) + (1 - t) ^ (n - 1))
    + 2 * n * (n - 1) * t * (1 - t ^ 2) ^ (n - 1)

theorem hasDerivAt_Hfn (n t : ℝ) (ht1 : (0 : ℝ) < 1 + t) (ht2 : (0 : ℝ) < 1 - t) :
    HasDerivAt (Hfn n) (Hp n t) t := by
  have hne1 : (1 : ℝ) + t ≠ 0 := ne_of_gt ht1
  have hne2 : (1 : ℝ) - t ≠ 0 := ne_of_gt ht2
  have ht12 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [mul_pos ht1 ht2]
  have hne12 : (1 : ℝ) - t ^ 2 ≠ 0 := ne_of_gt ht12
  have h1t : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have h1mt : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (1 : ℝ)
  have h1t2 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub (1 : ℝ)
  have dA := h1t.rpow_const (p := n) (Or.inl hne1)
  have dB := h1mt.rpow_const (p := n) (Or.inl hne2)
  have dAm := h1t.rpow_const (p := n - 1) (Or.inl hne1)
  have dBm := h1mt.rpow_const (p := n - 1) (Or.inl hne2)
  have dC := h1t2.rpow_const (p := n) (Or.inl hne12)
  have hstep :=
    ((((dA.add dB).const_mul (n - 1)).const_add (n + 1)).sub
      ((h1t2.mul (dAm.add dBm)).const_mul n)).sub (dC.const_mul (n - 1))
  convert hstep using 1
  simp only [Hp, Pi.add_apply]
  have ra : (1 + t) ^ (n - 2) = (1 + t) ^ (n - 1) / (1 + t) := by
    rw [eq_div_iff hne1, ← Real.rpow_add_one hne1, show n - 2 + 1 = n - 1 by ring]
  have rb : (1 - t) ^ (n - 2) = (1 - t) ^ (n - 1) / (1 - t) := by
    rw [eq_div_iff hne2, ← Real.rpow_add_one hne2, show n - 2 + 1 = n - 1 by ring]
  rw [show n - 1 - 1 = n - 2 by ring, ra, rb]
  field_simp
  ring

theorem Hfn_zero (n : ℝ) : Hfn n 0 = 0 := by
  simp only [Hfn]
  norm_num [Real.one_rpow]
  ring

theorem Hp_pos {n t : ℝ} (hn : 1 < n) (ht0 : 0 < t) (ht1 : t < 1) : 0 < Hp n t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have h2t : (0 : ℝ) < 1 - t := by linarith
  have h12 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [mul_pos h1t h2t]
  have hp : (0 : ℝ) < (1 + t) ^ (n - 1) := Real.rpow_pos_of_pos h1t _
  have hq : (0 : ℝ) < (1 - t) ^ (n - 1) := Real.rpow_pos_of_pos h2t _
  have hr : (0 : ℝ) < (1 - t ^ 2) ^ (n - 1) := Real.rpow_pos_of_pos h12 _
  have t1 : 0 < n * (n + 1) * t * ((1 + t) ^ (n - 1) + (1 - t) ^ (n - 1)) :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) ht0) (add_pos hp hq)
  have t2 : 0 < 2 * n * (n - 1) * t * (1 - t ^ 2) ^ (n - 1) :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) ht0) hr
  unfold Hp
  linarith

theorem Hfn_pos {n t : ℝ} (hn : 1 < n) (ht0 : 0 < t) (ht1 : t < 1) : 0 < Hfn n t := by
  have hmono : StrictMonoOn (Hfn n) (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
    · intro x hx
      have hx1 : (0 : ℝ) < 1 + x := by simp only [mem_Icc] at hx; linarith [hx.1]
      have hx2 : (0 : ℝ) < 1 - x := by simp only [mem_Icc] at hx; linarith [hx.2]
      exact (hasDerivAt_Hfn n x hx1 hx2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc, mem_Ioo] at hx
      have hx1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have hx2 : (0 : ℝ) < 1 - x := by linarith [hx.2]
      rw [(hasDerivAt_Hfn n x hx1 hx2).deriv]
      exact Hp_pos hn (by linarith [hx.1]) (by linarith [hx.2])
  have := hmono (left_mem_Icc.mpr ht0.le) (right_mem_Icc.mpr ht0.le) ht0
  rwa [Hfn_zero] at this

/-- `(χ*)^n = K^n (n-1)/(n+1)`: the defining property of the Hill density peak. -/
theorem chi_pow {K n : ℝ} (hK : 0 < K) (hn : 1 < n) :
    (chistar K n) ^ n = K ^ n * ((n - 1) / (n + 1)) := by
  have hbase : (0 : ℝ) ≤ (n - 1) / (n + 1) := le_of_lt (div_pos (by linarith) (by linarith))
  unfold chistar
  rw [Real.mul_rpow hK.le (Real.rpow_nonneg hbase _)]
  congr 1
  rw [← Real.rpow_mul hbase, one_div, inv_mul_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < n)),
      Real.rpow_one]

theorem Afn_pos {n t : ℝ} (hn : 1 < n) (ht : (0 : ℝ) ≤ 1 + t) : 0 < Afn n t := by
  have : 0 ≤ (n - 1) * (1 + t) ^ n := mul_nonneg (by linarith) (Real.rpow_nonneg ht _)
  unfold Afn; linarith

theorem Bfn_pos {n t : ℝ} (hn : 1 < n) (ht : (0 : ℝ) ≤ 1 - t) : 0 < Bfn n t := by
  have : 0 ≤ (n - 1) * (1 - t) ^ n := mul_nonneg (by linarith) (Real.rpow_nonneg ht _)
  unfold Bfn; linarith

theorem hasDerivAt_Afn (n t : ℝ) (ht : (1 : ℝ) + t ≠ 0) :
    HasDerivAt (Afn n) (n * (n - 1) * (1 + t) ^ (n - 1)) t := by
  have h1t : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
  have d := ((h1t.rpow_const (p := n) (Or.inl ht)).const_mul (n - 1)).const_add (n + 1)
  unfold Afn; convert d using 1; ring

theorem hasDerivAt_Bfn (n t : ℝ) (ht : (1 : ℝ) - t ≠ 0) :
    HasDerivAt (Bfn n) (-(n * (n - 1) * (1 - t) ^ (n - 1))) t := by
  have h1mt : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by simpa using (hasDerivAt_id t).const_sub 1
  have d := ((h1mt.rpow_const (p := n) (Or.inl ht)).const_mul (n - 1)).const_add (n + 1)
  unfold Bfn; convert d using 1; ring

/-- The log-ratio `f(t) = ln[φ(χ*+δ)/φ(χ*-δ)]` in `(1±t)` form. -/
noncomputable def Ffn (n t : ℝ) : ℝ :=
  (n - 1) * Real.log (1 + t) - (n - 1) * Real.log (1 - t)
    + 2 * Real.log (Bfn n t) - 2 * Real.log (Afn n t)

/-- `f'(t)`, the derivative of `Ffn`. -/
noncomputable def fp (n t : ℝ) : ℝ :=
  (n - 1) / (1 + t) + (n - 1) / (1 - t)
    - 2 * (n * (n - 1) * (1 - t) ^ (n - 1)) / Bfn n t
    - 2 * (n * (n - 1) * (1 + t) ^ (n - 1)) / Afn n t

theorem hasDerivAt_Ffn (n t : ℝ) (hn : 1 < n) (ht1 : (0 : ℝ) < 1 + t) (ht2 : (0 : ℝ) < 1 - t) :
    HasDerivAt (Ffn n) (fp n t) t := by
  have hA := Afn_pos hn ht1.le
  have hB := Bfn_pos hn ht2.le
  have h1t : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
  have h1mt : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by simpa using (hasDerivAt_id t).const_sub 1
  have dlog1 := (h1t.log (ne_of_gt ht1)).const_mul (n - 1)
  have dlog2 := (h1mt.log (ne_of_gt ht2)).const_mul (n - 1)
  have dlogB := (hasDerivAt_Bfn n t (ne_of_gt ht2)).log (ne_of_gt hB)
  have dlogA := (hasDerivAt_Afn n t (ne_of_gt ht1)).log (ne_of_gt hA)
  have d := ((dlog1.sub dlog2).add (dlogB.const_mul 2)).sub (dlogA.const_mul 2)
  unfold Ffn; convert d using 1; unfold fp; ring

/-- **The `f'` identity**: `f'(t) = 2(n²−1)H(t)/[(1−t²)A(t)B(t)]`. -/
theorem fp_eq {n t : ℝ} (hn : 1 < n) (ht1 : (0 : ℝ) < 1 + t) (ht2 : (0 : ℝ) < 1 - t) :
    fp n t = 2 * (n ^ 2 - 1) * Hfn n t / ((1 - t ^ 2) * Afn n t * Bfn n t) := by
  have hA := Afn_pos hn ht1.le
  have hB := Bfn_pos hn ht2.le
  have h12 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [mul_pos ht1 ht2]
  have e1 : (1 + t) ^ n = (1 + t) ^ (n - 1) * (1 + t) := by
    rw [← Real.rpow_add_one (ne_of_gt ht1) (n - 1), show n - 1 + 1 = n by ring]
  have e2 : (1 - t) ^ n = (1 - t) ^ (n - 1) * (1 - t) := by
    rw [← Real.rpow_add_one (ne_of_gt ht2) (n - 1), show n - 1 + 1 = n by ring]
  have e12 : (1 - t ^ 2) ^ (n - 1) = (1 + t) ^ (n - 1) * (1 - t) ^ (n - 1) := by
    rw [show (1 : ℝ) - t ^ 2 = (1 + t) * (1 - t) by ring, Real.mul_rpow ht1.le ht2.le]
  have e12n : (1 - t ^ 2) ^ n = (1 - t ^ 2) ^ (n - 1) * (1 - t ^ 2) := by
    rw [← Real.rpow_add_one (ne_of_gt h12) (n - 1), show n - 1 + 1 = n by ring]
  -- pure-ring relation between H and A, B (no division)
  have Hrel : 2 * (n ^ 2 - 1) * Hfn n t
      = 2 * (n - 1) * (Afn n t * Bfn n t
          - n * (1 - t ^ 2) * ((1 - t) ^ (n - 1) * Afn n t + (1 + t) ^ (n - 1) * Bfn n t)) := by
    unfold Hfn Afn Bfn
    rw [e1, e2, e12n, e12]
    ring
  rw [Hrel, eq_div_iff (ne_of_gt (mul_pos (mul_pos h12 hA) hB))]
  unfold fp
  field_simp
  ring

theorem fp_pos {n t : ℝ} (hn : 1 < n) (ht0 : 0 < t) (ht1 : t < 1) : 0 < fp n t := by
  have hp1 : (0 : ℝ) < 1 + t := by linarith
  have hp2 : (0 : ℝ) < 1 - t := by linarith
  have h12 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith [mul_pos hp1 hp2]
  rw [fp_eq hn hp1 hp2]
  have hH := Hfn_pos hn ht0 ht1
  have hden : 0 < (1 - t ^ 2) * Afn n t * Bfn n t :=
    mul_pos (mul_pos h12 (Afn_pos hn hp1.le)) (Bfn_pos hn hp2.le)
  apply div_pos _ hden
  have hc : 0 < 2 * (n ^ 2 - 1) := by nlinarith
  exact mul_pos hc hH

theorem Ffn_zero (n : ℝ) : Ffn n 0 = 0 := by
  simp [Ffn, Afn, Bfn, Real.one_rpow]

theorem Ffn_pos {n t : ℝ} (hn : 1 < n) (ht0 : 0 < t) (ht1 : t < 1) : 0 < Ffn n t := by
  have hmono : StrictMonoOn (Ffn n) (Icc 0 t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t)
    · intro x hx
      simp only [mem_Icc] at hx
      exact (hasDerivAt_Ffn n x hn (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc, mem_Ioo] at hx
      rw [(hasDerivAt_Ffn n x hn (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact fp_pos hn (by linarith [hx.1]) (by linarith [hx.2])
  have := hmono (left_mem_Icc.mpr ht0.le) (right_mem_Icc.mpr ht0.le) ht0
  rwa [Ffn_zero] at this

theorem chistar_pos {K n : ℝ} (hK : 0 < K) (hn : 1 < n) : 0 < chistar K n := by
  unfold chistar
  exact mul_pos hK (Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _)

/-- The Hill density at `χ*·u`, reduced via `(χ*)^n = K^n(n-1)/(n+1)` to a form
whose `u`-dependence is `u^{n-1}/((n+1)+(n-1)u^n)^2` (the `A`/`B` denominator). -/
theorem hd_chi {K n : ℝ} (hK : 0 < K) (hn : 1 < n) {u : ℝ} (hu : 0 < u) :
    hillDensity K n (chistar K n * u)
      = (n * (chistar K n) ^ (n - 1) * (n + 1) ^ 2 / K ^ n) * u ^ (n - 1)
        / ((n + 1) + (n - 1) * u ^ n) ^ 2 := by
  have hχ := chistar_pos hK hn
  have hKn : (0 : ℝ) < K ^ n := Real.rpow_pos_of_pos hK n
  have hun : (0 : ℝ) ≤ u ^ n := Real.rpow_nonneg hu.le n
  have hd : (0 : ℝ) < (n + 1) + (n - 1) * u ^ n := by nlinarith
  unfold hillDensity
  simp only [Real.mul_rpow hχ.le hu.le]
  rw [chi_pow hK hn]
  field_simp

/-- **Lemma B.1, general `n > 1`.** -/
theorem right_skew_general {K n : ℝ} (hK : 0 < K) (hn : 1 < n) {δ : ℝ}
    (hδ : 0 < δ) (hδle : δ ≤ chistar K n) :
    hillDensity K n (chistar K n - δ) < hillDensity K n (chistar K n + δ) := by
  have hχ : 0 < chistar K n := chistar_pos hK hn
  have hKn : (0 : ℝ) < K ^ n := Real.rpow_pos_of_pos hK n
  rcases lt_or_eq_of_le hδle with hlt | heq
  · -- δ < χ*: set t = δ/χ* ∈ (0,1)
    set t := δ / chistar K n with ht_def
    have ht0 : 0 < t := div_pos hδ hχ
    have ht1 : t < 1 := by rw [ht_def, div_lt_one hχ]; exact hlt
    have hp1 : (0 : ℝ) < 1 + t := by linarith
    have hp2 : (0 : ℝ) < 1 - t := by linarith
    have e_plus : chistar K n + δ = chistar K n * (1 + t) := by
      rw [ht_def]; field_simp
    have e_minus : chistar K n - δ = chistar K n * (1 - t) := by
      rw [ht_def]; field_simp
    rw [e_plus, e_minus, hd_chi hK hn hp2, hd_chi hK hn hp1]
    set C := n * (chistar K n) ^ (n - 1) * (n + 1) ^ 2 / K ^ n with hC_def
    have hC : 0 < C := by
      rw [hC_def]
      apply div_pos _ hKn
      have : 0 < (chistar K n) ^ (n - 1) := Real.rpow_pos_of_pos hχ _
      positivity
    have hA := Afn_pos hn hp1.le
    have hB := Bfn_pos hn hp2.le
    have hp : (0 : ℝ) < (1 + t) ^ (n - 1) := Real.rpow_pos_of_pos hp1 _
    have hq : (0 : ℝ) < (1 - t) ^ (n - 1) := Real.rpow_pos_of_pos hp2 _
    -- the cross-multiplied inequality, from Ffn > 0
    have Qineq : (1 - t) ^ (n - 1) * (Afn n t) ^ 2 < (1 + t) ^ (n - 1) * (Bfn n t) ^ 2 := by
      have hLR : Real.log ((1 + t) ^ (n - 1) * (Bfn n t) ^ 2)
          - Real.log ((1 - t) ^ (n - 1) * (Afn n t) ^ 2) = Ffn n t := by
        rw [Real.log_mul (ne_of_gt hp) (ne_of_gt (pow_pos hB 2)),
            Real.log_mul (ne_of_gt hq) (ne_of_gt (pow_pos hA 2)),
            Real.log_rpow hp1, Real.log_rpow hp2, Real.log_pow, Real.log_pow]
        push_cast; unfold Ffn; ring
      have hlog := Ffn_pos hn ht0 ht1
      rw [← hLR] at hlog
      exact (Real.log_lt_log_iff (mul_pos hq (pow_pos hA 2))
        (mul_pos hp (pow_pos hB 2))).mp (by linarith)
    -- conclude
    have hA2 : (0 : ℝ) < ((n + 1) + (n - 1) * (1 + t) ^ n) ^ 2 := pow_pos hA 2
    have hB2 : (0 : ℝ) < ((n + 1) + (n - 1) * (1 - t) ^ n) ^ 2 := pow_pos hB 2
    rw [div_lt_div_iff₀ hB2 hA2]
    have key := mul_lt_mul_of_pos_left Qineq hC
    unfold Afn Bfn at key
    nlinarith [key]
  · -- δ = χ*: χ*-δ = 0 ⇒ density 0 < density(2χ*)
    subst heq
    rw [sub_self]
    have h0 : hillDensity K n 0 = 0 := by
      unfold hillDensity
      rw [Real.zero_rpow (by linarith : n - 1 ≠ 0)]; simp
    rw [h0]
    unfold hillDensity
    have h2χ : (0 : ℝ) < chistar K n + chistar K n := by linarith
    have hb : (0 : ℝ) < K ^ n + (chistar K n + chistar K n) ^ n := by
      have := Real.rpow_nonneg h2χ.le n; linarith
    apply div_pos
    · exact mul_pos (mul_pos (by linarith : (0 : ℝ) < n) hKn) (Real.rpow_pos_of_pos h2χ _)
    · exact pow_pos hb 2

/-! ## Hill density unimodality, Lemma B.1 Part (b), and Regime III

Part (a) above (`right_skew_general`) compares the density at points equidistant
from the peak. The remaining content of Lemma B.1 and of the Regime III lemma
turns on the *unimodality* of the Hill density: `φ` rises on `[0, χ*]` and falls on
`[χ*, ∞)`. We establish this from the derivative

  `φ'(X) = n Kⁿ · X^{n-2} · ((n-1)Kⁿ - (n+1)Xⁿ) / (Kⁿ + Xⁿ)³`,

whose sign on `X > 0` is that of `(n-1)Kⁿ - (n+1)Xⁿ`, nonnegative exactly when
`Xⁿ ≤ Kⁿ(n-1)/(n+1) = (χ*)ⁿ`, i.e. `X ≤ χ*` (`chi_pow`). From unimodality:
* **Part (b)** (`right_skew_centro`, `hillPairSum_monotoneOn`): under `χ* ≥ 1/2`
  (i.e. `K ≥ K*(n)`, `half_le_chistar_iff`) the pair-sum `g(X) = h(X)+h(1-X)` is
  non-decreasing on `[0,1/2]`, so its `[0,1/2]`-max sits at `X = 1/2`;
* **Regime III** (`regimeIII_interior_critical_hill`): under `χ* < 1/2` the sign
  facts `g'(0) = φ(1) > 0` and `g'(χ*) = φ(1-χ*) - φ(χ*) < 0` are *derived*, then
  fed to the abstract IVT lemma `regimeIII_interior_critical`.
-/

/-- `ContinuousOn` of the Hill density on any set of nonnegative reals. -/
theorem hillDensity_continuousOn {K n : ℝ} (hK : 0 < K) (hn : 1 < n) {s : Set ℝ}
    (hs : ∀ x ∈ s, 0 ≤ x) : ContinuousOn (hillDensity K n) s := by
  unfold hillDensity
  apply ContinuousOn.div
  · exact continuousOn_const.mul
      (continuousOn_id.rpow_const (fun x _ => Or.inr (by linarith)))
  · exact (continuousOn_const.add
      (continuousOn_id.rpow_const (fun x _ => Or.inr (by linarith)))).pow 2
  · intro x hx
    have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
    have hxn : 0 ≤ x ^ n := Real.rpow_nonneg (hs x hx) n
    positivity

/-- `ContinuousOn` of the Hill tail on any set of nonnegative reals. -/
theorem hillTail_continuousOn {K n : ℝ} (hK : 0 < K) (hn : 1 < n) {s : Set ℝ}
    (hs : ∀ x ∈ s, 0 ≤ x) : ContinuousOn (hillTail K n) s := by
  unfold hillTail
  apply ContinuousOn.div continuousOn_const
  · exact continuousOn_const.add
      (continuousOn_id.rpow_const (fun x _ => Or.inr (by linarith)))
  · intro x hx
    have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
    have hxn : 0 ≤ x ^ n := Real.rpow_nonneg (hs x hx) n
    positivity

/-- **The Hill density derivative** `φ'(X) = n Kⁿ X^{n-2}((n-1)Kⁿ-(n+1)Xⁿ)/(Kⁿ+Xⁿ)³`
at `X > 0`, from the `rpow` const-power derivative and the quotient rule. -/
theorem hillDensity_hasDerivAt {K n : ℝ} (hK : 0 < K) (hn : 1 < n) {X : ℝ} (hX : 0 < X) :
    HasDerivAt (hillDensity K n)
      (n * K ^ n * (X ^ (n - 2) * ((n - 1) * K ^ n - (n + 1) * X ^ n)) / (K ^ n + X ^ n) ^ 3) X := by
  have hXne : X ≠ 0 := ne_of_gt hX
  have hKn : (0 : ℝ) < K ^ n := Real.rpow_pos_of_pos hK n
  have hXn : (0 : ℝ) ≤ X ^ n := Real.rpow_nonneg hX.le n
  have hD : (0 : ℝ) < K ^ n + X ^ n := by linarith
  have hnum : HasDerivAt (fun x : ℝ => n * K ^ n * x ^ (n - 1))
      (n * K ^ n * ((n - 1) * X ^ (n - 2))) X := by
    have := (Real.hasDerivAt_rpow_const (p := n - 1) (Or.inl hXne)).const_mul (n * K ^ n)
    rwa [show n - 1 - 1 = n - 2 from by ring] at this
  have hinner : HasDerivAt (fun x : ℝ => K ^ n + x ^ n) (n * X ^ (n - 1)) X :=
    (hasDerivAt_const_add_iff (K ^ n)).mpr (Real.hasDerivAt_rpow_const (p := n) (Or.inl hXne))
  have hden : HasDerivAt (fun x : ℝ => (K ^ n + x ^ n) ^ 2)
      (2 * (K ^ n + X ^ n) ^ 1 * (n * X ^ (n - 1))) X := by
    have := hinner.pow 2
    simpa using this
  have hdenne : (K ^ n + X ^ n) ^ 2 ≠ 0 := by positivity
  have hquot := hnum.div hden hdenne
  convert hquot using 1
  have e2 : X ^ (n - 1) = X ^ (n - 2) * X := by
    rw [← Real.rpow_add_one hXne, show n - 2 + 1 = n - 1 by ring]
  have e3 : X ^ n = X ^ (n - 1) * X := by
    rw [← Real.rpow_add_one hXne, show n - 1 + 1 = n by ring]
  rw [e3, e2, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **Rising tail**: the Hill density is strictly increasing on `[0, χ*]`. -/
theorem hillDensity_strictMonoOn {K n : ℝ} (hK : 0 < K) (hn : 1 < n) :
    StrictMonoOn (hillDensity K n) (Icc 0 (chistar K n)) := by
  have hχ : 0 < chistar K n := chistar_pos hK hn
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (chistar K n))
    (hillDensity_continuousOn hK hn (fun x hx => hx.1))
  intro x hx
  rw [interior_Icc, mem_Ioo] at hx
  have hx0 : 0 < x := hx.1
  rw [(hillDensity_hasDerivAt hK hn hx0).deriv]
  have hnp : (0 : ℝ) < n + 1 := by linarith
  have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
  have h1 : x ^ n < K ^ n * ((n - 1) / (n + 1)) := by
    rw [← chi_pow hK hn]; exact Real.rpow_lt_rpow hx0.le hx.2 (by linarith)
  have h2 : K ^ n * ((n - 1) / (n + 1)) * (n + 1) = K ^ n * (n - 1) := by field_simp
  have hkey : x ^ n * (n + 1) < K ^ n * (n - 1) := by
    have := mul_lt_mul_of_pos_right h1 hnp; rwa [h2] at this
  have hsign : 0 < (n - 1) * K ^ n - (n + 1) * x ^ n := by nlinarith [hkey]
  have hXn2 : 0 < x ^ (n - 2) := Real.rpow_pos_of_pos hx0 _
  apply div_pos
  · exact mul_pos (mul_pos (by linarith) hKn) (mul_pos hXn2 hsign)
  · positivity

/-- **Falling tail**: the Hill density is strictly decreasing on `[χ*, ∞)`. -/
theorem hillDensity_strictAntiOn {K n : ℝ} (hK : 0 < K) (hn : 1 < n) :
    StrictAntiOn (hillDensity K n) (Ici (chistar K n)) := by
  have hχ : 0 < chistar K n := chistar_pos hK hn
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    (hillDensity_continuousOn hK hn (fun x hx => le_trans hχ.le (mem_Ici.mp hx)))
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hx0 : 0 < x := lt_trans hχ hx
  rw [(hillDensity_hasDerivAt hK hn hx0).deriv]
  have hnp : (0 : ℝ) < n + 1 := by linarith
  have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
  have h1 : K ^ n * ((n - 1) / (n + 1)) < x ^ n := by
    rw [← chi_pow hK hn]; exact Real.rpow_lt_rpow hχ.le hx (by linarith)
  have h2 : K ^ n * ((n - 1) / (n + 1)) * (n + 1) = K ^ n * (n - 1) := by field_simp
  have hkey : K ^ n * (n - 1) < x ^ n * (n + 1) := by
    have := mul_lt_mul_of_pos_right h1 hnp; rwa [h2] at this
  have hsign : (n - 1) * K ^ n - (n + 1) * x ^ n < 0 := by nlinarith [hkey]
  have hXn2 : 0 < x ^ (n - 2) := Real.rpow_pos_of_pos hx0 _
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (mul_pos (by linarith) hKn)
      (mul_neg_of_pos_of_neg hXn2 hsign)
  · positivity

/-- **Lemma B.1, Part (b): centro-symmetric monotonicity (Regime II).** When the
density peak sits at or above the midpoint (`χ* ≥ 1/2`, i.e. `K ≥ K*(n)`), the Hill
density satisfies `φ(X) ≤ φ(1-X)` for every `X ∈ [0, 1/2]`. (Manuscript Lemma B.1(b),
the pointwise form.) -/
theorem right_skew_centro {K n : ℝ} (hK : 0 < K) (hn : 1 < n)
    (hχ : 1 / 2 ≤ chistar K n) {X : ℝ} (hX0 : 0 ≤ X) (hXhalf : X ≤ 1 / 2) :
    hillDensity K n X ≤ hillDensity K n (1 - X) := by
  have hmono := (hillDensity_strictMonoOn hK hn).monotoneOn
  have hXle : X ≤ chistar K n := le_trans hXhalf hχ
  by_cases hc : 1 - X ≤ chistar K n
  · exact hmono ⟨hX0, hXle⟩ ⟨by linarith, hc⟩ (by linarith)
  · rw [not_le] at hc
    set Δ2 := (1 - X) - chistar K n with hΔ2
    have hΔ2pos : 0 < Δ2 := by rw [hΔ2]; linarith
    have hΔ2le : Δ2 ≤ chistar K n := by rw [hΔ2]; nlinarith [hχ, hX0]
    have e1X : 1 - X = chistar K n + Δ2 := by rw [hΔ2]; ring
    have hskew := right_skew_general hK hn hΔ2pos hΔ2le
    have hXle2 : X ≤ chistar K n - Δ2 := by rw [hΔ2]; nlinarith [hχ]
    have hge0 : 0 ≤ chistar K n - Δ2 := le_trans hX0 hXle2
    have hlt : hillDensity K n X < hillDensity K n (1 - X) :=
      calc hillDensity K n X
          ≤ hillDensity K n (chistar K n - Δ2) :=
            hmono ⟨hX0, hXle⟩ ⟨hge0, by linarith [hΔ2pos]⟩ hXle2
        _ < hillDensity K n (chistar K n + Δ2) := hskew
        _ = hillDensity K n (1 - X) := by rw [← e1X]
    exact hlt.le

/-- **Lemma B.1(b), pair-sum form.** Under `χ* ≥ 1/2`, the centro-symmetric pair-sum
`g(X) = h(X) + h(1-X)` is monotone non-decreasing on `[0, 1/2]`; its maximum on
`[0,1/2]` therefore sits at `X = 1/2` (the Regime II max-location of §5). -/
theorem hillPairSum_monotoneOn {K n : ℝ} (hK : 0 < K) (hn : 1 < n)
    (hχ : 1 / 2 ≤ chistar K n) :
    MonotoneOn (fun X => hillTail K n X + hillTail K n (1 - X)) (Icc 0 (1 / 2)) := by
  have hcont : ContinuousOn (fun X => hillTail K n X + hillTail K n (1 - X)) (Icc 0 (1 / 2)) := by
    apply ContinuousOn.add (hillTail_continuousOn hK hn (fun x hx => hx.1))
    apply (hillTail_continuousOn hK hn (s := Icc 0 1) (fun x hx => hx.1)).comp
      ((continuous_const.sub continuous_id).continuousOn)
    intro x hx
    simp only [Set.mem_Icc, id_eq] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) (1 / 2)),
      HasDerivAt (fun X => hillTail K n X + hillTail K n (1 - X))
        (-(hillDensity K n x) + hillDensity K n (1 - x)) x := by
    intro x hx
    rw [interior_Icc, mem_Ioo] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have h1mx : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    have hinner : HasDerivAt (fun X : ℝ => 1 - X) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hcomp : HasDerivAt (fun X => hillTail K n (1 - X)) (hillDensity K n (1 - x)) x := by
      have := (hillTail_hasDeriv hK hn.le h1mx).comp x hinner
      simpa using this
    exact (hillTail_hasDeriv hK hn.le hx0).add hcomp
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) hcont
  · exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hderiv x hx).deriv]
    rw [interior_Icc, mem_Ioo] at hx
    have := right_skew_centro hK hn hχ hx.1.le (le_of_lt hx.2)
    linarith

/-- **Lemma regime-iii-critical, Hill-specialized.** When the density peak sits
strictly below the midpoint (`χ* < 1/2`, i.e. `K < K*(n)`), the pair-sum
`g(X) = h(X)+h(1-X)` has an interior critical point in `(0, χ*)`: a point where
`φ(1-X₀) = φ(X₀)`. The sign facts `g'(0) = φ(1) > 0` and
`g'(χ*) = φ(1-χ*) - φ(χ*) < 0` are *derived* from the Hill density (peak value at
`1` positive, density past the peak strictly smaller) and fed to the abstract IVT
lemma `regimeIII_interior_critical`. -/
theorem regimeIII_interior_critical_hill {K n : ℝ} (hK : 0 < K) (hn : 1 < n)
    (hχ : chistar K n < 1 / 2) :
    ∃ X0 ∈ Ioo (0 : ℝ) (chistar K n), hillDensity K n (1 - X0) = hillDensity K n X0 := by
  have hχpos : 0 < chistar K n := chistar_pos hK hn
  set gp : ℝ → ℝ := fun X => hillDensity K n (1 - X) - hillDensity K n X with hgp
  have hcont : ContinuousOn gp (Icc 0 (chistar K n)) := by
    apply ContinuousOn.sub
    · apply (hillDensity_continuousOn hK hn (s := Icc 0 1) (fun x hx => hx.1)).comp
        ((continuous_const.sub continuous_id).continuousOn)
      intro x hx
      simp only [Set.mem_Icc, id_eq] at hx ⊢
      constructor <;> linarith [hx.1, hx.2, hχ]
    · exact hillDensity_continuousOn hK hn (fun x hx => hx.1)
  have hφ0 : hillDensity K n 0 = 0 := by
    unfold hillDensity; rw [Real.zero_rpow (by linarith : n - 1 ≠ 0)]; simp
  have hφ1 : 0 < hillDensity K n 1 := by
    unfold hillDensity
    have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
    rw [Real.one_rpow, Real.one_rpow]
    have hnpos : 0 < n := by linarith
    positivity
  have hpos0 : 0 < gp 0 := by rw [hgp]; simp only [sub_zero]; rw [hφ0]; simpa using hφ1
  have hneg : gp (chistar K n) < 0 := by
    rw [hgp]; simp only
    have hanti := hillDensity_strictAntiOn hK hn
    have : hillDensity K n (1 - chistar K n) < hillDensity K n (chistar K n) :=
      hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
    linarith
  obtain ⟨X0, hX0mem, hX0val⟩ := regimeIII_interior_critical hχpos hcont hpos0 hneg
  exact ⟨X0, hX0mem, sub_eq_zero.mp hX0val⟩

/-- `χ* ≥ 1/2 ↔ K ≥ K*(n)`: the Regime II boundary expressed in `K` is the
density-peak-above-midpoint condition. Lets the Regime II results above be read off
directly from the manuscript's `K ≥ K*(n)`. -/
theorem half_le_chistar_iff {K n : ℝ} (hK : 0 < K) (hn : 1 < n) :
    1 / 2 ≤ chistar K n ↔ Kstar n ≤ K := by
  have hbase1 : (0 : ℝ) < (n - 1) / (n + 1) := div_pos (by linarith) (by linarith)
  set r := ((n - 1) / (n + 1)) ^ (1 / n) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hbase1 _
  have hKstar : Kstar n = 1 / 2 * r⁻¹ := by
    unfold Kstar; congr 1
    rw [hr, ← Real.inv_rpow hbase1.le, inv_div]
  have hchi : chistar K n = K * r := by unfold chistar; rw [← hr]
  rw [hchi, hKstar, ← div_eq_mul_inv, div_le_iff₀ hrpos]

end TwoGenie
