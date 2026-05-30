import TwoGenie.PerWisher

/-!
# The Ratio-Favoredness Lifting Theorem 5.3

The formalization assumes the §2 mean-field (sufficient-information-density) closure:
testimonial influence enters only through the population-averaged binding fraction, so
the perceived utilities are functions of the scalar calibration state. No graph
topology, local-neighborhood interaction, or spatial mixing process is modeled.

**Scope (read this).** This module formalizes the *mechanism* of Theorem 5.3 —
that affine functions commute with expectation — and applies it to the **inner**
(fast-calibration-chain) averaging layer. The condition-transfer half of the
theorem is formalized alongside it in `Priors.lean`. Specifically:

* **Proved:** `∫ (p + q·b) dμ = p + q·∫ b dμ` for a probability measure
  (`affine_commute_integral`), and hence `∫ uPerc^g(b) dν = uPerc^g(E_ν[b])`
  (`lift_uPercG1/2`) — the inner layer is exact because perceived utilities are
  affine in `b`.
* **Outer averaging, derived:** `E_θ[c_g·𝟙[X≥θ]] = c_g(1 − F̄(X)) = σ̄_g(X)` is
  proved as `Priors.sigmabar_eq_integral` — for *any* prior measure whose survival
  function is the tail, the expectation of the harm indicator is `σ̄_g`. So
  `sigmabar` is a theorem about an expectation, no longer a bare definition.
* **Condition transfer, derived in `Priors.lean`:** the model differential
  `F_Δ := Ū_{G2} − Ū_{G1}` is *defined* there from `σ̄_g` (`modelFdelta`), and the
  structural conditions transfer to it to the extent each is model-intrinsic: (A) is
  **derived** (`modelFdelta_condA`); (B-low)/(B-high) reduce to the explicit control
  inequalities (`modelFdelta_condBlow_iff`, `modelFdelta_condBhigh_iff`); (C) reduces
  to the tail-shape pair-sum (`modelFdelta_pairsum`). Because (B-low) forces
  `u_w − B − M < 0`, (C) is a prior-dependent *basin* condition, not a sign
  condition, so it remains a hypothesis of the model capstone (`Capstone.lean`),
  characterised per family by the §6 frontiers rather than universally derivable.

What is **not** packaged as one Lean statement is the single composed identity
`Ū_g(X) = u_perc^g(σ̄_g(X), ᾱ)`: the inner (`lift_uPercG1/2`) and outer
(`sigmabar_eq_integral`) averaging layers are each kernel-checked, but their
composition into one double-expectation theorem is left implicit. The deductive
payoff — the (A)/(B)/(C)-on-the-model-`F_Δ` transfer — is fully kernel-checked,
with (C) retained as the basin hypothesis it is.
-/

namespace TwoGenie

open MeasureTheory

/-- **Affine–expectation commutation**, the mechanism of the Lifting Theorem:
for any probability measure `μ` and integrable identity, `∫ (p + q·b) dμ =
p + q·∫ b dμ`. -/
theorem affine_commute_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (p q : ℝ) (hint : Integrable (fun b => b) μ) :
    ∫ b, (p + q * b) ∂μ = p + q * ∫ b, b ∂μ := by
  rw [integral_add (integrable_const p) (hint.const_mul q), integral_const_mul,
    integral_const]
  simp

/-- **Exact fast-chain averaging of `uPercG2`** (eq. uperc-G2). Because the
perceived utility is affine in the calibration state `b`, integrating it against
the fast-chain stationary distribution `ν` equals evaluating it at the stationary
mean `E_ν[b]` — the boundary-preserving stationary mean `b*(X;θ)` in the paper. -/
theorem lift_uPercG2 {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun b => b) ν) (uaG2 ualtG2 Bcap : ℝ) :
    ∫ b, uPercG2 uaG2 ualtG2 Bcap b ∂ν = uPercG2 uaG2 ualtG2 Bcap (∫ b, b ∂ν) := by
  simp only [uPercG2_affine]
  exact affine_commute_integral (uaG2 + ualtG2 - Bcap) Bcap hint

/-- **Exact fast-chain averaging of `uPercG1`** (eq. uperc-G1). -/
theorem lift_uPercG1 {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun b => b) ν) (uaG1 ualtG1 Mcap Aa : ℝ) :
    ∫ b, uPercG1 uaG1 ualtG1 Mcap Aa b ∂ν = uPercG1 uaG1 ualtG1 Mcap Aa (∫ b, b ∂ν) := by
  simp only [uPercG1_affine]
  exact affine_commute_integral (uaG1 + ualtG1 + Mcap) (-Aa) hint

end TwoGenie
