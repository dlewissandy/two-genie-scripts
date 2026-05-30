import TwoGenie.Priors

/-!
# Lomax (Pareto Type II) threshold prior — a second robustness instance

A third `ThresholdPrior`, after Hill and Pareto Type I, exhibiting another genuinely
different heavy-tailed family for the §4–§5 robustness pass. Unlike Pareto Type I,
the Lomax tail is supported from `0` (no positive lower scale, no kink): the density
peaks at `X = 0` and decreases monotonically, so it is the modal-at-zero,
monotone-decreasing companion to Pareto's modal-at-`xm` shape.

We use the **Lomax** survival tail with positive scale `lam` and shape `alpha`:

  `F̄(X) = (1 + X/lam)^{-alpha}`,   `f(X) = (alpha/lam)(1 + X/lam)^{-alpha-1}`.

The tail is smooth on `[0,1]`, `F̄(0) = 1`, monotone non-increasing, polynomially
heavy.

* `lomaxTail_antitoneOn` — **(Q2a)**, the source of condition (A).
* `lomaxTail_lipschitz` — **(Q2b)**, the `alpha/lam` Lipschitz bound on `[0,1]`
  (convex mean value theorem on the smooth tail).
* `lomaxPrior` — a fully-certified `ThresholdPrior` instance (Q2a + Q2b proved).
* `lomaxDensity_antitoneOn`, `lomaxPairSum_antitoneOn` — the (Q5) pair-sum content.
  Because the Lomax density is monotone *decreasing* (its mode is at the boundary
  `X = 0`, not the interior), the centro-symmetric pair-sum is non-increasing on
  `[0,1/2]`: the easy direction of the Hill Lemma B.1(b), with no interior peak.

Nothing in this file is deferred or `sorry`'d.
-/

set_option linter.unusedVariables false

namespace TwoGenie

open Set

variable (lam alpha : ℝ)

/-- Lomax (Pareto Type II) survival tail: `(1 + X/lam)^{-alpha}`. -/
noncomputable def lomaxTail (X : ℝ) : ℝ := (1 + X / lam) ^ (-alpha)

/-- Lomax density: `(alpha/lam)(1 + X/lam)^{-alpha-1}`. -/
noncomputable def lomaxDensity (X : ℝ) : ℝ := (alpha / lam) * (1 + X / lam) ^ (-alpha - 1)

variable {lam alpha}

/-- `F̄(0) = 1`: at `X = 0` there is no community coverage. -/
theorem lomaxTail_zero (hlam : 0 < lam) : lomaxTail lam alpha 0 = 1 := by
  unfold lomaxTail
  rw [zero_div, add_zero, Real.one_rpow]

/-- `F̄(1) = (1 + 1/lam)^{-alpha}`: the saturation value at full coverage. -/
theorem lomaxTail_one (hlam : 0 < lam) :
    lomaxTail lam alpha 1 = (1 + 1 / lam) ^ (-alpha) := by
  unfold lomaxTail
  rfl

/-- The base `1 + X/lam` is positive (indeed `≥ 1`) for `X ≥ 0` and `lam > 0`. -/
theorem lomax_base_pos (hlam : 0 < lam) {X : ℝ} (hX : 0 ≤ X) : 0 < 1 + X / lam := by
  have : 0 ≤ X / lam := div_nonneg hX hlam.le
  linarith

/-- The base `1 + X/lam` is `≥ 1` for `X ≥ 0` and `lam > 0`. -/
theorem lomax_base_ge_one (hlam : 0 < lam) {X : ℝ} (hX : 0 ≤ X) : 1 ≤ 1 + X / lam := by
  have : 0 ≤ X / lam := div_nonneg hX hlam.le
  linarith

/-- **(Q1, calculus core)** `F̄'(X) = -f(X)`: the Lomax tail derivative is the
negative density, from which the density integrates to 1. Proved via the inner
`X ↦ 1 + X/lam` derivative and the `Real.rpow` const-power rule. -/
theorem lomaxTail_hasDeriv (hlam : 0 < lam) {X : ℝ} (hX : 0 ≤ X) :
    HasDerivAt (lomaxTail lam alpha) (-(lomaxDensity lam alpha X)) X := by
  have hbase : 0 < 1 + X / lam := lomax_base_pos hlam hX
  have hinner : HasDerivAt (fun X : ℝ => 1 + X / lam) (1 / lam) X := by
    have h := ((hasDerivAt_id X).div_const lam).const_add (1 : ℝ)
    simpa using h
  have hpow := hinner.rpow_const (Or.inl (ne_of_gt hbase)) (p := -alpha)
  unfold lomaxTail
  convert hpow using 1
  unfold lomaxDensity
  rw [show -alpha - 1 = (-alpha) - 1 by ring]
  ring

/-- **(Q2a)** The Lomax tail is monotone non-increasing on `[0,1]`: the base
`1 + X/lam` grows with `X` and stays `≥ 1 > 0`, and `t ↦ t^{-alpha}` is antitone on
positives for `alpha > 0`. This is the source of structural condition (A). -/
theorem lomaxTail_antitoneOn (hlam : 0 < lam) (ha : 0 < alpha) :
    AntitoneOn (lomaxTail lam alpha) (Icc 0 1) := by
  intro X hX Y hY hXY
  unfold lomaxTail
  have hXpos : 0 < 1 + X / lam := lomax_base_pos hlam hX.1
  have hYpos : 0 < 1 + Y / lam := lomax_base_pos hlam hY.1
  have hle : 1 + X / lam ≤ 1 + Y / lam := by
    have : X / lam ≤ Y / lam := div_le_div_of_nonneg_right hXY hlam.le
    linarith
  rw [Real.rpow_neg hXpos.le, Real.rpow_neg hYpos.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hXpos alpha)
    (Real.rpow_le_rpow hXpos.le hle ha.le)

/-- **(Q2b)** The Lomax tail is `(alpha/lam)`-Lipschitz on `[0,1]`. The tail is
smooth with `F̄'(X) = -f(X)`, and `|f(X)| = (alpha/lam)(1 + X/lam)^{-alpha-1} ≤
alpha/lam` on `[0,1]`, because a base `≥ 1` raised to a non-positive power is `≤ 1`.
Apply the convex mean value theorem. -/
theorem lomaxTail_lipschitz (hlam : 0 < lam) (ha : 0 < alpha) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |lomaxTail lam alpha x - lomaxTail lam alpha y| ≤ (alpha / lam) * |x - y| := by
  have hderiv : ∀ z ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (lomaxTail lam alpha) (-(lomaxDensity lam alpha z)) (Icc 0 1) z :=
    fun z hz => (lomaxTail_hasDeriv hlam hz.1).hasDerivWithinAt
  have hbound : ∀ z ∈ Icc (0 : ℝ) 1, ‖-(lomaxDensity lam alpha z)‖ ≤ alpha / lam := by
    intro z hz
    have hbase1 : 1 ≤ 1 + z / lam := lomax_base_ge_one hlam hz.1
    have hbasepos : 0 < 1 + z / lam := lomax_base_pos hlam hz.1
    have hple : (1 + z / lam) ^ (-alpha - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase1 (by linarith)
    have hpnn : 0 ≤ (1 + z / lam) ^ (-alpha - 1) := Real.rpow_nonneg hbasepos.le _
    have hcnn : 0 ≤ alpha / lam := div_nonneg ha.le hlam.le
    have hdens_nonneg : 0 ≤ lomaxDensity lam alpha z :=
      mul_nonneg hcnn hpnn
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hdens_nonneg]
    unfold lomaxDensity
    calc (alpha / lam) * (1 + z / lam) ^ (-alpha - 1)
        ≤ (alpha / lam) * 1 := mul_le_mul_of_nonneg_left hple hcnn
      _ = alpha / lam := mul_one _
  intro x hx y hy
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc 0 1) hy hx
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at key

/-- The Lomax (Pareto Type II) family as a fully-certified `ThresholdPrior`: (Q2a)
and (Q2b) both proved. -/
noncomputable def lomaxPrior (hlam : 0 < lam) (ha : 0 < alpha) : ThresholdPrior where
  tail := lomaxTail lam alpha
  antitone := lomaxTail_antitoneOn hlam ha
  lipConst := alpha / lam
  lipschitz := lomaxTail_lipschitz hlam ha

/-! ## (Q5) The centro-symmetric max location — the easy, monotone-density direction

The analog of Hill's Lemma B.1(b). The Lomax density has its mode at the boundary
`X = 0` and is monotone decreasing on `[0,1]`, so the centro-symmetric pair-sum is
*non-increasing* on `[0,1/2]`: its `[0,1/2]`-max sits at the left endpoint `X = 0`.
This is the easy direction (no interior peak to chase, unlike the Hill case). -/

/-- The Lomax density is monotone non-increasing on `[0,1]`: same shape as the tail
antitone, with exponent `-alpha-1` (also negative for `alpha > 0`). -/
theorem lomaxDensity_antitoneOn (hlam : 0 < lam) (ha : 0 < alpha) :
    AntitoneOn (lomaxDensity lam alpha) (Icc 0 1) := by
  intro X hX Y hY hXY
  unfold lomaxDensity
  have hXpos : 0 < 1 + X / lam := lomax_base_pos hlam hX.1
  have hYpos : 0 < 1 + Y / lam := lomax_base_pos hlam hY.1
  have hle : 1 + X / lam ≤ 1 + Y / lam := by
    have : X / lam ≤ Y / lam := div_le_div_of_nonneg_right hXY hlam.le
    linarith
  have hcnn : 0 ≤ alpha / lam := div_nonneg ha.le hlam.le
  apply mul_le_mul_of_nonneg_left _ hcnn
  rw [show (-alpha - 1 : ℝ) = -(alpha + 1) by ring,
      Real.rpow_neg hXpos.le, Real.rpow_neg hYpos.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hXpos (alpha + 1))
    (Real.rpow_le_rpow hXpos.le hle (by linarith))

/-- `ContinuousOn` of the Lomax tail on any set of nonnegative reals. -/
theorem lomaxTail_continuousOn (hlam : 0 < lam) {s : Set ℝ} (hs : ∀ x ∈ s, 0 ≤ x) :
    ContinuousOn (lomaxTail lam alpha) s := by
  unfold lomaxTail
  apply ContinuousOn.rpow_const
  · exact (continuousOn_const.add (continuousOn_id.div_const lam))
  · intro x hx
    exact Or.inl (ne_of_gt (lomax_base_pos hlam (hs x hx)))

/-- **(Q5) centro-symmetric pair-sum, Lomax (easy) direction.** Because the density
is monotone decreasing, the pair-sum `g(X) = F̄(X) + F̄(1-X)` is non-increasing on
`[0, 1/2]`: its derivative at `X` is `f(1-X) - f(X) ≤ 0`, since `X ≤ 1-X` there and
the density is antitone. So the `[0,1/2]`-max sits at the left endpoint `X = 0`. -/
theorem lomaxPairSum_antitoneOn (hlam : 0 < lam) (ha : 0 < alpha) :
    AntitoneOn (fun X => lomaxTail lam alpha X + lomaxTail lam alpha (1 - X))
      (Icc 0 (1 / 2)) := by
  have hcont : ContinuousOn
      (fun X => lomaxTail lam alpha X + lomaxTail lam alpha (1 - X)) (Icc 0 (1 / 2)) := by
    apply ContinuousOn.add (lomaxTail_continuousOn hlam (fun x hx => hx.1))
    apply (lomaxTail_continuousOn hlam (s := Icc 0 1) (fun x hx => hx.1)).comp
      ((continuous_const.sub continuous_id).continuousOn)
    intro x hx
    simp only [Set.mem_Icc, id_eq] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) (1 / 2)),
      HasDerivAt (fun X => lomaxTail lam alpha X + lomaxTail lam alpha (1 - X))
        (-(lomaxDensity lam alpha x) + lomaxDensity lam alpha (1 - x)) x := by
    intro x hx
    rw [interior_Icc, mem_Ioo] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have h1mx : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    have hinner : HasDerivAt (fun X : ℝ => 1 - X) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hcomp : HasDerivAt (fun X => lomaxTail lam alpha (1 - X))
        (lomaxDensity lam alpha (1 - x)) x := by
      have := (lomaxTail_hasDeriv (alpha := alpha) hlam h1mx).comp x hinner
      simpa using this
    exact (lomaxTail_hasDeriv hlam hx0).add hcomp
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2)) hcont
  · exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hderiv x hx).deriv]
    rw [interior_Icc, mem_Ioo] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have h1mx_mem : (1 - x) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> [linarith [hx.2]; linarith [hx.1]]
    have hx_mem : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, by linarith [hx.2]⟩
    have hle : x ≤ 1 - x := by linarith [hx.2]
    have := lomaxDensity_antitoneOn hlam ha hx_mem h1mx_mem hle
    linarith

end TwoGenie
