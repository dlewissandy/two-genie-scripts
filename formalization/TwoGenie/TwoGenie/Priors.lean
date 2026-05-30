import TwoGenie.Structural

/-!
# Threshold priors (the (Q1)/(Q2) abstraction)

Formalizes the prior-shape conditions of §5 (Q1)/(Q2). Downstream only two
properties of the threshold prior are used: its tail `F̄(X) = P(θ > X)` is
monotone non-increasing and (bounded) Lipschitz on `[0,1]`. We bundle exactly
those into `ThresholdPrior`. The plan's robustness question — "does the theorem
hold for *all* instances?" — becomes: produce a `ThresholdPrior` term. The Hill
family (`Priors/Hill.lean`) is one such term; Pareto / log-normal would be others.

`sigmabar_monotone` is the source of structural condition (A): population-averaged
operational awareness `σ̄_g(X) = c_g(1 - F̄(X))` is monotone non-decreasing.
-/

namespace TwoGenie

open Set MeasureTheory

/-- A threshold prior, summarized by the two tail properties (Q2) the analysis
uses: monotone non-increasing and Lipschitz on `[0,1]`. The companion (Q1) — that
the tail comes from a density — is recorded per instance (see Hill). -/
structure ThresholdPrior where
  /-- the tail probability `F̄(X) = P(θ > X)` -/
  tail : ℝ → ℝ
  /-- (Q2a) the tail is monotone non-increasing on `[0,1]` -/
  antitone : AntitoneOn tail (Icc 0 1)
  /-- a Lipschitz constant for the tail on `[0,1]` -/
  lipConst : ℝ
  /-- (Q2b) the tail is `lipConst`-Lipschitz on `[0,1]` (bounded density) -/
  lipschitz : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    |tail x - tail y| ≤ lipConst * |x - y|

/-- Population-averaged operational awareness `σ̄_g(X) = c_g(1 - F̄(X))`
(eq. sigbar). -/
def sigmabar (P : ThresholdPrior) (cg : ℝ) (X : ℝ) : ℝ := cg * (1 - P.tail X)

/-- **Source of condition (A).** With `c_g ≥ 0`, population-averaged operational
awareness is monotone non-decreasing on `[0,1]`, because the tail is non-increasing.
This is exactly the monotonicity that the Lifting Theorem transfers to `F_Δ`. -/
theorem sigmabar_monotone (P : ThresholdPrior) {cg : ℝ} (hcg : 0 ≤ cg) :
    MonotoneOn (sigmabar P cg) (Icc 0 1) := by
  intro X hX Y hY hXY
  unfold sigmabar
  have htail : P.tail Y ≤ P.tail X := P.antitone hX hY hXY
  nlinarith [htail, hcg]

/-- **Outer threshold-prior averaging, derived rather than assumed.** The per-wisher
operational-awareness contribution fires the coefficient `c_g` exactly when the
realized salience `X` clears the wisher's threshold `θ`, i.e. it is
`c_g · 𝟙[X ≥ θ] = c_g · 𝟙_{Iic X}(θ)`. For **any** prior measure `μ` on the threshold
whose survival function is the prior's tail — `(μ (Ioi X)).toReal = P.tail X`, which
is just what `F̄(X) = P(θ > X)` *means* — the expectation of that contribution equals
`σ̄_g(X) = c_g(1 − F̄(X))`.

This is the outer averaging step of the Lifting Theorem (`Lifting.lean`): it turns
`sigmabar` from a bare *definition* into a *theorem*, `σ̄_g = E_θ[c_g · 𝟙[X ≥ θ]]`.
The only premise is the defining relation between the measure and its tail; no
density, smoothness, or specific family is needed. -/
theorem sigmabar_eq_integral (P : ThresholdPrior) (cg X : ℝ)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsurv : (μ (Ioi X)).toReal = P.tail X) :
    ∫ θ, (Iic X).indicator (fun _ => cg) θ ∂μ = sigmabar P cg X := by
  rw [integral_indicator_const cg measurableSet_Iic, smul_eq_mul]
  -- `μ.real (Iic X)` is definitionally `(μ (Iic X)).toReal`; name it the toReal form.
  show (μ (Iic X)).toReal * cg = sigmabar P cg X
  -- CDF from survival on a probability measure: `μ(Iic X) = 1 − μ(Ioi X)`.
  have hsum : (μ (Iic X)).toReal + (μ (Ioi X)).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
      ← compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ,
      ENNReal.toReal_one]
  have hcdf : (μ (Iic X)).toReal = 1 - P.tail X := by rw [← hsurv]; linarith
  rw [hcdf, sigmabar]; ring

/-! ## The model differential `F_Δ` and the condition transfer

Up to here the favoredness conditions (`CondA`/`CondBlow`/`CondBhigh`/`CondC` in
`Structural.lean`) were stated on an **abstract** `Fdelta : ℝ → ℝ`. Here `F_Δ` is
*defined* from the model primitives — the manuscript's

  `F_Δ(X) = u_w − B − M + B·σ̄_{G2}(X) + A·σ̄_{G1}(X)`,  `σ̄_g(X) = c_g(1 − F̄_g(X))` —

with a **separate prior per genie** (`P₂` for `G₂`, `P₁` for `G₁`; distinct `K`'s in
the Hill case — the manuscript's `(K_{G2},K_{G1})` plane). Matched-`K` is the `P₂=P₁`
slice. The conditions are discharged *to the extent each is model-intrinsic*:
* **(A) is derived** (`modelFdelta_condA`) from `sigmabar_monotone` on each prior,
  with no parameter hypothesis beyond `B, A, c_g ≥ 0`. The seam is closed for (A).
* **(B) reduces to explicit endpoint signs** (`modelFdelta_zero`,
  `modelFdelta_condBlow_iff`): with `F̄_g(0)=1`, (B-low) `⟺ u_w < B + M`.
* **(C) reduces to a tail-shape inequality** (`modelFdelta_pairsum`): the
  centro-symmetric pair-sum is `2(u_w−B−M) + B·c_{G2}(2−F̄_{G2}(X)−F̄_{G2}(1−X)) +
  A·c_{G1}(2−F̄_{G1}(X)−F̄_{G1}(1−X))`. Because (B-low) forces `u_w−B−M < 0`, (C) is
  **not** a sign condition — it needs the priors' growth to dominate near the centre,
  the prior-dependent basin condition characterised per family by the §6 frontiers,
  and is why (C) stays a hypothesis of the model capstone (`Capstone.lean`). -/

/-- The model population payoff differential `F_Δ` (eq. F-delta, §5), with a separate
threshold prior per genie (`P₂` for `G₂`, `P₁` for `G₁`). -/
noncomputable def modelFdelta (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 : ℝ) :
    ℝ → ℝ :=
  fun X => uw - Bcap - Mcap + Bcap * sigmabar P₂ cG2 X + Aa * sigmabar P₁ cG1 X

/-- **Condition (A), derived for the model `F_Δ`.** With non-negative amplitudes
`B, A` and coefficients `c_{G2}, c_{G1}`, `F_Δ` is non-decreasing on `[0,1]` — a
direct consequence of `sigmabar_monotone` on each prior (each `σ̄_g` is
non-decreasing). This is the manuscript's "(A) Monotonicity"; no parameter
constraint is needed, and it holds for distinct priors. -/
theorem modelFdelta_condA (P₂ P₁ : ThresholdPrior) (uw Mcap : ℝ) {Bcap Aa cG2 cG1 : ℝ}
    (hB : 0 ≤ Bcap) (hA : 0 ≤ Aa) (hcG2 : 0 ≤ cG2) (hcG1 : 0 ≤ cG1) :
    CondA (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1) := by
  intro X hX Y hY hXY
  have e2 := mul_le_mul_of_nonneg_left (sigmabar_monotone P₂ hcG2 hX hY hXY) hB
  have e1 := mul_le_mul_of_nonneg_left (sigmabar_monotone P₁ hcG1 hX hY hXY) hA
  simp only [modelFdelta]; linarith

/-- `F_Δ(0) = u_w − B − M` (using `F̄_g(0)=1` for both priors, i.e. `σ̄_g(0)=0`). -/
theorem modelFdelta_zero (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 : ℝ)
    (h2 : P₂.tail 0 = 1) (h1 : P₁.tail 0 = 1) :
    modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1 0 = uw - Bcap - Mcap := by
  simp only [modelFdelta, sigmabar, h2, h1]; ring

/-- **Condition (B-low) for the model, made explicit.** With `F̄_g(0)=1`, the all-`G1`
corner is a rest point exactly when `u_w < B + M` — the manuscript's "constraint
inequality on the controls". -/
theorem modelFdelta_condBlow_iff (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 : ℝ)
    (h2 : P₂.tail 0 = 1) (h1 : P₁.tail 0 = 1) :
    CondBlow (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1) ↔ uw < Bcap + Mcap := by
  unfold CondBlow
  rw [modelFdelta_zero P₂ P₁ uw Bcap Mcap Aa cG2 cG1 h2 h1]
  constructor <;> intro h <;> linarith

/-- **Condition (C) for the model, reduced to a tail-shape inequality.** The
centro-symmetric pair-sum is `2(u_w−B−M) + B·c_{G2}(2−F̄_{G2}(X)−F̄_{G2}(1−X)) +
A·c_{G1}(2−F̄_{G1}(X)−F̄_{G1}(1−X))` — one growth term per prior. -/
theorem modelFdelta_pairsum (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 X : ℝ) :
    modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1 X
        + modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1 (1 - X)
      = 2 * (uw - Bcap - Mcap)
        + Bcap * cG2 * (2 - P₂.tail X - P₂.tail (1 - X))
        + Aa * cG1 * (2 - P₁.tail X - P₁.tail (1 - X)) := by
  simp only [modelFdelta, sigmabar]; ring

/-- **(Q2) continuity of the tail.** The Lipschitz field of a `ThresholdPrior`
delivers the manuscript's (Q2) continuity of the tail on `[0,1]` (bounded density ⇒
continuous survival function), so it need not be carried as a separate field. -/
theorem ThresholdPrior.tail_continuousOn (P : ThresholdPrior) :
    ContinuousOn P.tail (Icc 0 1) := by
  have hL : LipschitzOnWith (Real.toNNReal P.lipConst) P.tail (Icc 0 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
    calc |P.tail x - P.tail y| ≤ P.lipConst * |x - y| := P.lipschitz x hx y hy
      _ ≤ max P.lipConst 0 * |x - y| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  exact hL.continuousOn

/-- **Continuity of the model `F_Δ` on `[0,1]`.** An affine combination of the
`σ̄_g = c_g(1−F̄_g)`, each continuous because the tail is (Q2)-continuous. This is the
continuity the favoredness and accessibility analyses use on the grid `[0,1]`. -/
theorem modelFdelta_continuousOn (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 : ℝ) :
    ContinuousOn (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1) (Icc 0 1) := by
  have h2 : ContinuousOn (fun X => sigmabar P₂ cG2 X) (Icc 0 1) :=
    continuousOn_const.mul (continuousOn_const.sub P₂.tail_continuousOn)
  have h1 : ContinuousOn (fun X => sigmabar P₁ cG1 X) (Icc 0 1) :=
    continuousOn_const.mul (continuousOn_const.sub P₁.tail_continuousOn)
  unfold modelFdelta
  exact (continuousOn_const.add (continuousOn_const.mul h2)).add (continuousOn_const.mul h1)

/-- `F_Δ(1) = u_w + A·σ̄_{G1}(1) − B(1−σ̄_{G2}(1)) − M` (eq. lift-B-high). -/
theorem modelFdelta_one (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 : ℝ) :
    modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1 1
      = uw + Aa * sigmabar P₁ cG1 1 - Bcap * (1 - sigmabar P₂ cG2 1) - Mcap := by
  unfold modelFdelta; ring

/-- **Condition (B-high) for the model, made explicit** (eq. basin-B-high), the
symmetric partner of `modelFdelta_condBlow_iff`: the all-`G2` corner is a rest point
exactly when `u_w + A·σ̄_{G1}(1) > B(1−σ̄_{G2}(1)) + M`. -/
theorem modelFdelta_condBhigh_iff (P₂ P₁ : ThresholdPrior) (uw Bcap Mcap Aa cG2 cG1 : ℝ) :
    CondBhigh (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1)
      ↔ 0 < uw + Aa * sigmabar P₁ cG1 1 - Bcap * (1 - sigmabar P₂ cG2 1) - Mcap := by
  unfold CondBhigh; rw [modelFdelta_one]

end TwoGenie
