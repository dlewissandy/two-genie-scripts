import Mathlib

/-!
# Primitives: harm, welfare, the audit, and the Cauchy–Schwarz welfare lift

This module formalizes §3 of the manuscript ("Welfare and altruistic utility").

The four-axis Jain harm taxonomy (greed, ego, aggression, deceit) is treated as
*one instantiation* of a `d`-dimensional theory: we work over an arbitrary real
inner-product space `V`. The Jain case is `V = EuclideanSpace ℝ (Fin 4)` (see
`jainHarmSpace` below). This decouples the deductive content from `d = 4` and
answers the plan's Open Question 1: none of the results in this file depend on
`d = 4`; they hold in any real inner-product space.

Key formalized claims:
* `welfare_aDN`         — `w(aDN) = 0` (the welfare baseline is doing nothing).
* `inner_lam_welfare`   — `⟪λ, w a⟫ = c(aDN) - c(a)`, the audit score gap.
* `audit_scalar_guarantee` — the argmin guarantee `c(a*) ≤ c(aDN)` lifts to
                          `0 ≤ ⟪λ, w(a*)⟫` (the λ-weighted welfare is nonnegative).
* `wagg_cauchy_schwarz` — the **Cauchy–Schwarz welfare lift** (eq. Wagg-bound),
                          stated in inner-product form, proved from Cauchy–Schwarz.
* `wagg_nonneg`         — the downstream sign corollary `0 ≤ Wagg`. This is the
                          fact §4–§6 actually consume, so the Cauchy–Schwarz lift
                          is load-bearing, not decorative.
-/

set_option linter.unusedSectionVars false

namespace TwoGenie

open scoped RealInnerProductSpace

/-- The deliberation move set. `aDR`, `aDN` are terminal (grant / refuse); `aSU`,
`aSA` are non-terminal (ask the wisher / propose a modified wish). -/
inductive Action where
  | aDR
  | aDN
  | aSU
  | aSA
deriving DecidableEq, Repr

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Welfare of an action (eq. welfare-def): harm averted relative to doing nothing,
`w(a) = Hdisc(aDN) - Hdisc(a)`. Signed; `Hdisc : Action → V` is the
present-value-aggregated harm of each action. -/
def welfare (Hdisc : Action → V) (a : Action) : V := Hdisc Action.aDN - Hdisc a

/-- The welfare baseline: doing nothing has zero welfare. -/
@[simp] theorem welfare_aDN (Hdisc : Action → V) : welfare Hdisc Action.aDN = 0 := by
  simp [welfare]

/-- The audit's per-candidate score (eq. audit): `c(a) = ⟪λ, Hdisc a⟫`. -/
def auditScore (lam : V) (Hdisc : Action → V) (a : Action) : ℝ := ⟪lam, Hdisc a⟫

/-- The λ-weighted welfare of an action equals its score gap to the baseline:
`⟪λ, w a⟫ = c(aDN) - c(a)`. -/
theorem inner_lam_welfare (lam : V) (Hdisc : Action → V) (a : Action) :
    ⟪lam, welfare Hdisc a⟫ = auditScore lam Hdisc Action.aDN - auditScore lam Hdisc a := by
  unfold welfare auditScore
  rw [inner_sub_right]

/-- **Audit scalar guarantee** (§3, "Because `aDN` is always in the move set …").
Because `aDN` is always available, the terminal `aStar` selected by the audit's
argmin satisfies `c(aStar) ≤ c(aDN)`; hence its λ-weighted welfare is nonnegative
relative to doing nothing. This is the scalar guarantee the framework then lifts
to a community-level sign claim. -/
theorem audit_scalar_guarantee (lam : V) (Hdisc : Action → V) {aStar : Action}
    (hmin : auditScore lam Hdisc aStar ≤ auditScore lam Hdisc Action.aDN) :
    0 ≤ ⟪lam, welfare Hdisc aStar⟫ := by
  rw [inner_lam_welfare]; linarith

/-! ## The Cauchy–Schwarz welfare lift

§3 lifts the per-binding scalar guarantee `λ · dH̄ ≥ 0` to the social-welfare
aggregate `W_agg := ⟪ᾱ, dH̄⟫` via a parallel/perpendicular decomposition of `ᾱ`
relative to `λ`, bounding the cross term by Cauchy–Schwarz. We reproduce that
inequality exactly. `ᾱ` (`altbar`) is the population-mean altruism vector;
`dH̄` (`dHbar`) is the population-mean audit harm-reduction vector. -/

/-- Coefficient of the `lam`-parallel component of `x`: `⟪lam,x⟫ / ⟪lam,lam⟫`. -/
noncomputable def projCoef (lam x : V) : ℝ := ⟪lam, x⟫ / ⟪lam, lam⟫

/-- The `lam`-perpendicular component of `x`. -/
noncomputable def perp (lam x : V) : V := x - (projCoef lam x) • lam

/-- `⟪lam, lam⟫ ≠ 0` when `lam ≠ 0`. -/
private theorem inner_self_ne (lam : V) (hlam : lam ≠ 0) : ⟪lam, lam⟫ ≠ 0 := by
  rw [real_inner_self_eq_norm_mul_norm]
  exact mul_ne_zero (norm_ne_zero_iff.mpr hlam) (norm_ne_zero_iff.mpr hlam)

/-- The perpendicular component is genuinely orthogonal to `lam`. -/
theorem inner_lam_perp (lam x : V) (hlam : lam ≠ 0) : ⟪lam, perp lam x⟫ = 0 := by
  have hne := inner_self_ne lam hlam
  unfold perp projCoef
  rw [inner_sub_right, real_inner_smul_right]
  field_simp
  ring

/-- Decomposition identity: `⟪a, h⟫ = projCoef·⟪lam,h⟫ + ⟪a⊥, h⊥⟫`. -/
theorem inner_decomp (lam a h : V) (hlam : lam ≠ 0) :
    ⟪a, h⟫ = (projCoef lam a) * ⟪lam, h⟫ + ⟪perp lam a, perp lam h⟫ := by
  have hne := inner_self_ne lam hlam
  unfold perp projCoef
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm a lam]
  field_simp
  ring

/-- **Cauchy–Schwarz welfare lift** (eq. Wagg-bound), inner-product form.
With `ᾱ`-component along `λ` of coefficient `projCoef λ ᾱ` and perpendicular
components `ᾱ⊥, dH̄⊥`,
`⟪ᾱ, dH̄⟫ ≥ (projCoef λ ᾱ)·⟪λ, dH̄⟫ − ‖ᾱ⊥‖·‖dH̄⊥‖`.
In the manuscript's trigonometric form, `projCoef λ ᾱ = cos θλ · ‖ᾱ‖ / ‖λ‖` and
`‖ᾱ⊥‖ = sin θλ · ‖ᾱ‖`. The cross term is bounded by Cauchy–Schwarz
(`abs_real_inner_le_norm`), which is therefore a *used* step, not dead code. -/
theorem wagg_cauchy_schwarz (lam altbar dHbar : V) (hlam : lam ≠ 0) :
    (projCoef lam altbar) * ⟪lam, dHbar⟫ - ‖perp lam altbar‖ * ‖perp lam dHbar‖
      ≤ ⟪altbar, dHbar⟫ := by
  rw [inner_decomp lam altbar dHbar hlam]
  have hcs : -(‖perp lam altbar‖ * ‖perp lam dHbar‖) ≤ ⟪perp lam altbar, perp lam dHbar⟫ := by
    have := abs_real_inner_le_norm (perp lam altbar) (perp lam dHbar)
    rw [abs_le] at this
    linarith [this.1]
  linarith

/-- The social-welfare aggregate `W_agg := ⟪ᾱ, dH̄⟫` (eq. Wagg-def). -/
noncomputable def Wagg (altbar dHbar : V) : ℝ := ⟪altbar, dHbar⟫

/-- **Sign corollary** (the fact §4–§6 actually consume). If the parallel term
dominates the (Cauchy–Schwarz-bounded) perpendicular cross term, then
`0 ≤ W_agg`. The hypothesis `cross_dominated` is the inner-product form of the
manuscript's `θλ + ∠(λ, dH̄) ≤ π/2` condition combined with the
scalar-preservation assumption `0 ≤ ⟪λ, dH̄⟫`. -/
theorem wagg_nonneg (lam altbar dHbar : V) (hlam : lam ≠ 0)
    (cross_dominated :
      ‖perp lam altbar‖ * ‖perp lam dHbar‖ ≤ (projCoef lam altbar) * ⟪lam, dHbar⟫) :
    0 ≤ Wagg altbar dHbar := by
  unfold Wagg
  have := wagg_cauchy_schwarz lam altbar dHbar hlam
  linarith

/-- The Jain four-axis instantiation. Nothing above depends on this choice; it is
recorded to show that `d = 4` is one instance of the `d`-dimensional theory. -/
abbrev jainHarmSpace : Type := EuclideanSpace ℝ (Fin 4)

end TwoGenie
