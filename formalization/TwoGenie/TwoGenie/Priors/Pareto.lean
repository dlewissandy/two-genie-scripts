import TwoGenie.Priors

/-!
# Pareto (Type I) threshold prior — a robustness instance

A second `ThresholdPrior`, for the robustness pass a reviewer flags as missing (the Hill
phase diagrams are otherwise "a case study presented as a theorem"). The point is
that the prior-agnostic results of §4–§5 hold for *any* `ThresholdPrior`; here we
exhibit a genuinely different heavy-tailed family.

We use the **Pareto Type I** survival tail with positive scale `xm` and shape `α`:

  `F̄(X) = 1` for `X ≤ xm`,   `F̄(X) = (xm / X)^α` for `X ≥ xm`.

The scale `xm > 0` is the minimum threshold, and the density peaks at `xm > 0` —
so unlike a zero-centred family the *modal* threshold is positive (physical for an
awareness threshold). The tail is polynomial (heavy), `F̄(0) = 1`, monotone
non-increasing.

* `paretoTail_antitoneOn` — **(Q2a)**, the source of condition (A).
* `paretoTail_lipschitz` — **(Q2b)**, the `α/xm` Lipschitz bound on `[0,1]` (convex
  mean value theorem on the smooth piece, glued across the kink at `xm`).
* `paretoPrior` — a fully-certified `ThresholdPrior` instance (Q2a + Q2b proved).
-/

namespace TwoGenie

open Set

variable (xm α : ℝ)

/-- Pareto Type I survival tail: `1` below the scale `xm`, `(xm/X)^α` above. -/
noncomputable def paretoTail (X : ℝ) : ℝ := if X ≤ xm then 1 else (xm / X) ^ α

variable {xm α}

/-- **(Q2a)** The Pareto tail is monotone non-increasing on `[0,1]`: flat at `1`
below the scale, polynomially decreasing above it. This is the source of
structural condition (A). -/
theorem paretoTail_antitoneOn (hxm : 0 < xm) (hα : 0 < α) :
    AntitoneOn (paretoTail xm α) (Icc 0 1) := by
  intro X _ Y _ hXY
  simp only [paretoTail]
  by_cases hY1 : Y ≤ xm
  · -- Y ≤ xm ⇒ X ≤ xm; both branches are 1.
    have hX1 : X ≤ xm := le_trans hXY hY1
    simp [hY1, hX1]
  · have hYpos : 0 < Y := lt_trans hxm (not_le.mp hY1)
    rw [if_neg hY1]
    by_cases hX1 : X ≤ xm
    · -- X ≤ xm < Y : need (xm/Y)^α ≤ 1
      rw [if_pos hX1]
      exact Real.rpow_le_one (le_of_lt (div_pos hxm hYpos))
        (by rw [div_le_one hYpos]; exact le_of_lt (not_le.mp hY1)) (le_of_lt hα)
    · -- xm < X ≤ Y : (xm/Y)^α ≤ (xm/X)^α
      rw [if_neg hX1]
      have hXpos : 0 < X := lt_trans hxm (not_le.mp hX1)
      exact Real.rpow_le_rpow (le_of_lt (div_pos hxm hYpos)) (by gcongr) (le_of_lt hα)

/-- **(Q2b)** The Pareto tail is `(α/xm)`-Lipschitz on `[0,1]`. The tail equals
`(xm / max xm X)^α`; the smooth piece `t ↦ (xm/t)^α` is `(α/xm)`-Lipschitz on
`[xm,∞)` (mean value theorem; `|g'(t)| = α(xm/t)^α/t ≤ α/xm`), and `max xm ·` is
`1`-Lipschitz, so the composition is `(α/xm)`-Lipschitz across the kink at `xm`. -/
theorem paretoTail_lipschitz (hxm : 0 < xm) (hα : 0 < α) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |paretoTail xm α x - paretoTail xm α y| ≤ (α / xm) * |x - y| := by
  -- The tail in closed form, with the kink absorbed into `max`.
  have heq : ∀ X : ℝ, paretoTail xm α X = (xm / max xm X) ^ α := by
    intro X
    unfold paretoTail
    split_ifs with h
    · rw [max_eq_left h, div_self (ne_of_gt hxm), Real.one_rpow]
    · rw [max_eq_right (le_of_lt (not_le.mp h))]
  -- Smooth piece is (α/xm)-Lipschitz on `Ici xm`.
  have hsmooth : ∀ u ∈ Ici xm, ∀ v ∈ Ici xm,
      |(xm / u) ^ α - (xm / v) ^ α| ≤ (α / xm) * |u - v| := by
    have hderiv : ∀ t ∈ Ici xm,
        HasDerivWithinAt (fun t => (xm / t) ^ α)
          ((-(xm) / t ^ 2) * α * (xm / t) ^ (α - 1)) (Ici xm) t := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hxm ht
      have hinner : HasDerivAt (fun s => xm / s) (-(xm) / t ^ 2) t := by
        have h := (hasDerivAt_const t xm).div (hasDerivAt_id t) (ne_of_gt ht0)
        convert h using 1
        simp only [id_eq]; ring
      exact (hinner.rpow_const (Or.inl (ne_of_gt (div_pos hxm ht0)))).hasDerivWithinAt
    have hbound : ∀ t ∈ Ici xm,
        ‖(-(xm) / t ^ 2) * α * (xm / t) ^ (α - 1)‖ ≤ α / xm := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hxm ht
      have hr : (0 : ℝ) < xm / t := div_pos hxm ht0
      have hr1 : xm / t ≤ 1 := by rw [div_le_one ht0]; exact ht
      have hpos : 0 ≤ (xm / t ^ 2) * α * (xm / t) ^ (α - 1) :=
        mul_nonneg (mul_nonneg (div_nonneg hxm.le (by positivity)) hα.le)
          (Real.rpow_nonneg hr.le _)
      rw [Real.norm_eq_abs,
        show (-(xm) / t ^ 2) * α * (xm / t) ^ (α - 1)
            = -((xm / t ^ 2) * α * (xm / t) ^ (α - 1)) by ring, abs_neg, abs_of_nonneg hpos]
      have hid : (xm / t) * (xm / t) ^ (α - 1) = (xm / t) ^ α := by
        rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hr)]
        congr 1; ring
      rw [show (xm / t ^ 2) * α * (xm / t) ^ (α - 1)
            = α / t * ((xm / t) * (xm / t) ^ (α - 1)) by ring, hid,
          div_mul_eq_mul_div, div_le_div_iff₀ ht0 hxm]
      have hrα : (xm / t) ^ α ≤ 1 := Real.rpow_le_one hr.le hr1 hα.le
      have h2 : 0 ≤ (xm / t) ^ α := Real.rpow_nonneg hr.le α
      nlinarith [mul_le_mul_of_nonneg_left hrα (mul_nonneg hα.le hxm.le),
        mul_le_mul_of_nonneg_left ht hα.le, h2, hα.le, hxm.le]
    intro u hu v hv
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      (convex_Ici xm) hv hu
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at key
  -- Combine: paretoTail = smooth ∘ (max xm ·), and `max xm ·` is 1-Lipschitz.
  intro x hx y hy
  rw [heq x, heq y]
  have hmax : |max xm x - max xm y| ≤ |x - y| := by
    rw [max_comm xm x, max_comm xm y]; exact abs_max_sub_max_le_abs x y xm
  calc |(xm / max xm x) ^ α - (xm / max xm y) ^ α|
      ≤ (α / xm) * |max xm x - max xm y| :=
        hsmooth _ (le_max_left xm x) _ (le_max_left xm y)
    _ ≤ (α / xm) * |x - y| :=
        mul_le_mul_of_nonneg_left hmax (div_nonneg hα.le hxm.le)

/-- The Pareto Type I family as a fully-certified `ThresholdPrior`: (Q2a) and
(Q2b) both proved. -/
noncomputable def paretoPrior (hxm : 0 < xm) (hα : 0 < α) : ThresholdPrior where
  tail := paretoTail xm α
  antitone := paretoTail_antitoneOn hxm hα
  lipConst := α / xm
  lipschitz := paretoTail_lipschitz hxm hα

/-! ### Endpoint values (Q3)/(Q4) for the Pareto prior

The (B-low)/(B-high) conditions are evaluated at the prior's endpoint tail values.
At `X = 0 ≤ xm` the survival is `1` (no community coverage); at `X = 1` it is `1` if
the scale `xm ≥ 1`, otherwise `xm^α`. These feed `modelFdelta_condBlow_iff` /
`modelFdelta_condBhigh_iff`. -/

/-- `F̄(0) = 1`: below the scale `xm` the Pareto survival is flat at `1`. -/
theorem paretoTail_zero (hxm : 0 < xm) : paretoTail xm α 0 = 1 := by
  unfold paretoTail; rw [if_pos (le_of_lt hxm)]

/-- `F̄(1) = 1` if `xm ≥ 1`, else `xm^α` (the saturation value at full salience). -/
theorem paretoTail_one :
    paretoTail xm α 1 = if (1 : ℝ) ≤ xm then 1 else xm ^ α := by
  unfold paretoTail
  by_cases h : (1 : ℝ) ≤ xm
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, div_one]

/-! ## (Q5) The centro-symmetric max location — Pareto Type I

The analog of Hill's Lemma B.1(b) for the modal-at-`xm` Pareto family. Unlike the
Lomax case (density peaking at the boundary `X = 0`), the Pareto density is *flat at
zero* on `[0,xm]` and peaks at the interior scale `xm`. The centro-symmetric pair-sum
`g(X) = F̄(X) + F̄(1-X)` therefore *rises* on `[0,xm]` and *falls* on `[xm,1/2]`, so
its `[0,1/2]`-max sits at the interior point `X = xm`. We prove the two pieces and
glue them by `le_total X xm`. -/

/-- Pareto smooth-piece density `α xm^α t^{-α-1}`, the density on `(xm,∞)` where the
tail is `(xm/t)^α`. It is non-negative and monotone decreasing for `α > 0`. -/
noncomputable def paretoSmoothDensity (xm α t : ℝ) : ℝ := α * xm ^ α * t ^ (-α - 1)

/-- The smooth piece `t ↦ (xm/t)^α` has derivative `-α xm^α t^{-α-1}` for `t > 0`:
the chain rule on `t ↦ xm/t` composed with `t ↦ t^α`, with the closed form rewritten
to the smooth-piece density. -/
theorem paretoSmooth_hasDeriv (hxm : 0 < xm) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (xm / s) ^ α) (-(paretoSmoothDensity xm α t)) t := by
  have hr : (0 : ℝ) < xm / t := div_pos hxm ht
  have hinner : HasDerivAt (fun s => xm / s) (-(xm) / t ^ 2) t := by
    have h := (hasDerivAt_const t xm).div (hasDerivAt_id t) (ne_of_gt ht)
    convert h using 1
    simp only [id_eq]; ring
  have hpow := hinner.rpow_const (Or.inl (ne_of_gt hr)) (p := α)
  convert hpow using 1
  unfold paretoSmoothDensity
  -- `α xm^α t^{-α-1} = α (xm/t)^{α-1} (xm/t^2)`, matching the chain-rule output.
  have hid : (xm / t) ^ (α - 1) = (xm / t) ^ α / (xm / t) := by
    rw [eq_div_iff (ne_of_gt hr), ← Real.rpow_add_one (ne_of_gt hr)]
    congr 1; ring
  rw [hid]
  have hxmt : (xm / t) ^ α = xm ^ α / t ^ α := by
    rw [Real.div_rpow hxm.le ht.le]
  rw [hxmt]
  rw [show (-α - 1 : ℝ) = (-α) - 1 by ring, Real.rpow_sub ht, Real.rpow_neg ht.le,
    Real.rpow_one]
  field_simp

/-- The Pareto smooth-piece density is monotone non-increasing on `(0,∞)`: with
exponent `-α-1 < 0`, `t ↦ t^{-α-1}` is antitone on positives. -/
theorem paretoSmoothDensity_antitoneOn (hxm : 0 < xm) (hα : 0 < α) :
    AntitoneOn (paretoSmoothDensity xm α) (Ioi 0) := by
  intro s hs t ht hst
  simp only [mem_Ioi] at hs ht
  unfold paretoSmoothDensity
  have hcnn : 0 ≤ α * xm ^ α := mul_nonneg hα.le (Real.rpow_nonneg hxm.le _)
  apply mul_le_mul_of_nonneg_left _ hcnn
  rw [show (-α - 1 : ℝ) = -(α + 1) by ring, Real.rpow_neg hs.le, Real.rpow_neg ht.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hs (α + 1))
    (Real.rpow_le_rpow hs.le hst (by linarith))

/-- **(Q5) upper piece.** On `[xm, 1/2]` both arguments `X` and `1-X` exceed `xm`, so
the tail is smooth there, and the pair-sum `g(X) = F̄(X) + F̄(1-X)` is non-increasing:
its derivative is `f(1-X) - f(X) ≤ 0`, since `X ≤ 1-X` makes `f(X) ≥ f(1-X)` by the
smooth-piece density antitone. So the `[xm,1/2]`-max sits at the left endpoint `xm`. -/
theorem paretoPairSum_antitoneOn_upper (hxm : 0 < xm) (hα : 0 < α) (hxm12 : xm < 1 / 2) :
    AntitoneOn (fun X => paretoTail xm α X + paretoTail xm α (1 - X)) (Icc xm (1 / 2)) := by
  -- Positivity of both arguments on `Icc xm (1/2)`.
  have hXposOf : ∀ X ∈ Icc xm (1 / 2), (0 : ℝ) < X := fun X hX => lt_of_lt_of_le hxm hX.1
  have h1XposOf : ∀ X ∈ Icc xm (1 / 2), (0 : ℝ) < 1 - X := fun X hX => by
    rcases hX with ⟨_, h2⟩; linarith
  -- On `Icc xm (1/2)` the tail collapses to the smooth piece for both arguments.
  have hsmoothX : ∀ X ∈ Icc xm (1 / 2), paretoTail xm α X = (xm / X) ^ α := by
    intro X hX
    unfold paretoTail
    by_cases h : X ≤ xm
    · have hXeq : X = xm := le_antisymm h hX.1
      rw [if_pos h, hXeq, div_self (ne_of_gt hxm), Real.one_rpow]
    · rw [if_neg h]
  have hsmooth1X : ∀ X ∈ Icc xm (1 / 2), paretoTail xm α (1 - X) = (xm / (1 - X)) ^ α := by
    intro X hX
    unfold paretoTail
    have h1X : xm < 1 - X := by rcases hX with ⟨_, h2⟩; linarith
    rw [if_neg (not_le.mpr h1X)]
  -- The smooth pair-sum is continuous on `Icc xm (1/2)`.
  have hsmoothcont : ContinuousOn
      (fun X => (xm / X) ^ α + (xm / (1 - X)) ^ α) (Icc xm (1 / 2)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.rpow_const
      · exact continuousOn_const.div continuousOn_id
          (fun x hx => ne_of_gt (hXposOf x hx))
      · exact fun x hx => Or.inl (ne_of_gt (div_pos hxm (hXposOf x hx)))
    · apply ContinuousOn.rpow_const
      · exact continuousOn_const.div ((continuous_const.sub continuous_id).continuousOn)
          (fun x hx => ne_of_gt (h1XposOf x hx))
      · exact fun x hx => Or.inl (ne_of_gt (div_pos hxm (h1XposOf x hx)))
  -- The smooth pair-sum has the expected derivative on the interior.
  have hderiv : ∀ X ∈ interior (Icc xm (1 / 2)),
      HasDerivAt (fun X => (xm / X) ^ α + (xm / (1 - X)) ^ α)
        (-(paretoSmoothDensity xm α X) + paretoSmoothDensity xm α (1 - X)) X := by
    intro X hX
    rw [interior_Icc, mem_Ioo] at hX
    have hXpos : (0 : ℝ) < X := lt_trans hxm hX.1
    have h1Xpos : (0 : ℝ) < 1 - X := by linarith [hX.2]
    have hinner : HasDerivAt (fun s : ℝ => 1 - s) (-1) X := by
      simpa using (hasDerivAt_id X).const_sub (1 : ℝ)
    have hcomp : HasDerivAt (fun s => (xm / (1 - s)) ^ α)
        (paretoSmoothDensity xm α (1 - X)) X := by
      have := (paretoSmooth_hasDeriv (α := α) hxm h1Xpos).comp X hinner
      simpa using this
    exact (paretoSmooth_hasDeriv hxm hXpos).add hcomp
  -- The smooth pair-sum is antitone, then transfer to the tail form by congruence.
  have hsmoothanti : AntitoneOn
      (fun X => (xm / X) ^ α + (xm / (1 - X)) ^ α) (Icc xm (1 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc xm (1 / 2)) hsmoothcont
    · exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro X hX
      rw [(hderiv X hX).deriv]
      rw [interior_Icc, mem_Ioo] at hX
      have hXpos : (0 : ℝ) < X := lt_trans hxm hX.1
      have h1Xpos : (0 : ℝ) < 1 - X := by linarith [hX.2]
      have hle : X ≤ 1 - X := by linarith [hX.2]
      have := paretoSmoothDensity_antitoneOn hxm hα (mem_Ioi.mpr hXpos)
        (mem_Ioi.mpr h1Xpos) hle
      linarith
  intro X hX Y hY hXY
  have hXeq : paretoTail xm α X + paretoTail xm α (1 - X)
      = (xm / X) ^ α + (xm / (1 - X)) ^ α := by rw [hsmoothX X hX, hsmooth1X X hX]
  have hYeq : paretoTail xm α Y + paretoTail xm α (1 - Y)
      = (xm / Y) ^ α + (xm / (1 - Y)) ^ α := by rw [hsmoothX Y hY, hsmooth1X Y hY]
  simp only at hXeq hYeq ⊢
  rw [hXeq, hYeq]
  exact hsmoothanti hX hY hXY

/-- **(Q5) centro-symmetric max location for the Pareto Type I prior.** For
`0 < xm < 1/2` and `α > 0`, the pair-sum `g(X) = F̄(X) + F̄(1-X)` over `[0,1/2]` is
maximized at the interior scale `X = xm`, the modal threshold. On `[0,xm]` the tail is
flat (`F̄(X)=1`) while `F̄(1-X)` rises (antitone tail, decreasing argument `1-X`), so
`g` is non-decreasing; on `[xm,1/2]` the smooth-piece density dominates and `g` is
non-increasing (`paretoPairSum_antitoneOn_upper`). Both pieces yield `g X ≤ g xm`. -/
theorem paretoPairSum_le_at_threshold {xm α : ℝ} (hxm : 0 < xm) (hα : 0 < α) (hxm12 : xm < 1/2)
    {X : ℝ} (hX0 : 0 ≤ X) (hX12 : X ≤ 1/2) :
    paretoTail xm α X + paretoTail xm α (1 - X)
      ≤ paretoTail xm α xm + paretoTail xm α (1 - xm) := by
  rcases le_total X xm with hXxm | hxmX
  · -- `[0, xm]`: flat tail at `X`, antitone-only growth of the `1-X` term.
    have hX1 : paretoTail xm α X = paretoTail xm α xm := by
      unfold paretoTail
      rw [if_pos hXxm, if_pos (le_refl xm)]
    have h1X1 : (0 : ℝ) ≤ 1 - X := by linarith
    have h1xm1 : (0 : ℝ) ≤ 1 - xm := by linarith [hxm12]
    have hmem1X : (1 - X) ∈ Icc (0 : ℝ) 1 := ⟨h1X1, by linarith⟩
    have hmem1xm : (1 - xm) ∈ Icc (0 : ℝ) 1 := ⟨h1xm1, by linarith [hxm12]⟩
    have hle : 1 - xm ≤ 1 - X := by linarith
    have htail := paretoTail_antitoneOn hxm hα hmem1xm hmem1X hle
    rw [hX1]; linarith
  · -- `[xm, 1/2]`: the smooth, non-increasing piece.
    have hXmem : X ∈ Icc xm (1 / 2) := ⟨hxmX, by linarith [hX12]⟩
    have hxmmem : xm ∈ Icc xm (1 / 2) := ⟨le_refl xm, le_of_lt hxm12⟩
    have := paretoPairSum_antitoneOn_upper hxm hα hxm12 hxmmem hXmem hxmX
    simpa using this

end TwoGenie
