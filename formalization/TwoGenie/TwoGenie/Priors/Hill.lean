import TwoGenie.Priors

/-!
# The Hill-derivative prior specialization (§5)

Formalizes §5 ("Hill-prior specialization"). The Hill tail and density are

  `h(X) = K^n / (K^n + X^n)`,  `f(X) = n K^n X^{n-1} / (K^n + X^n)^2`,

with median threshold `K > 0` and cooperativity `n ≥ 1`.

What is kernel-checked here:
* `hillTail_zero`, `hillTail_one` — endpoint values `h(0)=1`, `h(1)=σ`.
* `hillTail_nonneg`, `hillTail_le_one`.
* `hillTail_antitoneOn` — **(Q2a)** the tail is monotone non-increasing (uses
  monotonicity of `X ↦ X^n`); this is the source of structural condition (A).
* `regimeIII_interior_critical` — **Regime III** interior critical point of the
  pair-sum, by the intermediate value theorem (the manuscript's
  `lem:regime-iii-critical`), from the sign facts `g'(0)>0`, `g'(χ*)<0`.
* `frontier_T1_iff`, `frontier_T2_iff`, `frontier_T3_iff` — the algebraic
  rearrangement of the frontier conditions (T1)/(T2)/(T3) into the
  `u_d + d ± … ≥ 1` no-erosion forms.
* `hillTail_hasDeriv` — `h'(X) = -f(X)` (the `rpow` const-power derivative and the
  quotient rule); the calculus core of (Q1).

* `hillTail_lipschitz` — **(Q2b)** the Lipschitz constant `n/K^n` on `[0,1]`
  (bounded-density bound + the convex mean value theorem); discharges
  `hillPrior.lipschitz`, so `hillPrior` is a fully-certified `ThresholdPrior`.
* Lemma B.1 (right-skew): the `n=2` case is `right_skew_two` (below); the general
  `n>1` case is `right_skew_general` in `Priors/RightSkew.lean` (the full
  `H(t), H'(t)` construction). Both are proved.

Nothing in this file is deferred or `sorry`'d.
-/

set_option linter.unusedVariables false

namespace TwoGenie

open Set

variable (K n : ℝ)

/-- The Hill tail `h(X) = K^n / (K^n + X^n)` (eq. sec:hill-specialization). -/
noncomputable def hillTail (X : ℝ) : ℝ := K ^ n / (K ^ n + X ^ n)

/-- The Hill density `f(X) = n K^n X^{n-1} / (K^n + X^n)^2`
(eq. sec:hill-specialization-density). -/
noncomputable def hillDensity (X : ℝ) : ℝ :=
  n * K ^ n * X ^ (n - 1) / (K ^ n + X ^ n) ^ 2

/-- The Hill density peak location `χ* = K((n-1)/(n+1))^{1/n}`. -/
noncomputable def chistar : ℝ := K * ((n - 1) / (n + 1)) ^ (1 / n)

/-- The regime threshold `K*(n) = ½((n+1)/(n-1))^{1/n}` (eq. K-star). -/
noncomputable def Kstar : ℝ := (1 / 2) * ((n + 1) / (n - 1)) ^ (1 / n)

variable {K n}

theorem hillTail_pos_denom (hK : 0 < K) (hn : 1 ≤ n) (X : ℝ) (hX : 0 ≤ X) :
    0 < K ^ n + X ^ n := by
  have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
  have hXn : 0 ≤ X ^ n := Real.rpow_nonneg hX n
  linarith

theorem hillTail_nonneg (hK : 0 < K) (hn : 1 ≤ n) {X : ℝ} (hX : 0 ≤ X) :
    0 ≤ hillTail K n X := by
  unfold hillTail
  exact div_nonneg (le_of_lt (Real.rpow_pos_of_pos hK n))
    (le_of_lt (hillTail_pos_denom hK hn X hX))

theorem hillTail_le_one (hK : 0 < K) (hn : 1 ≤ n) {X : ℝ} (hX : 0 ≤ X) :
    hillTail K n X ≤ 1 := by
  unfold hillTail
  rw [div_le_one (hillTail_pos_denom hK hn X hX)]
  have hXn : 0 ≤ X ^ n := Real.rpow_nonneg hX n
  linarith

/-- `h(0) = 1`: at `X = 0` there is no community coverage. -/
theorem hillTail_zero (hK : 0 < K) (hn : 1 ≤ n) : hillTail K n 0 = 1 := by
  unfold hillTail
  have hn0 : n ≠ 0 := (lt_of_lt_of_le one_pos hn).ne'
  rw [Real.zero_rpow hn0, add_zero, div_self (Real.rpow_pos_of_pos hK n).ne']

/-- `h(1) = σ = K^n/(K^n+1)`: the saturation value at full coverage. -/
theorem hillTail_one (hK : 0 < K) (hn : 1 ≤ n) :
    hillTail K n 1 = K ^ n / (K ^ n + 1) := by
  unfold hillTail
  rw [Real.one_rpow]

/-- **(Q2a)** The Hill tail is monotone non-increasing on `[0,1]`: since `X ↦ X^n`
is non-decreasing for `n ≥ 1`, the denominator grows and the tail falls. This is
the source of structural condition (A). -/
theorem hillTail_antitoneOn (hK : 0 < K) (hn : 1 ≤ n) :
    AntitoneOn (hillTail K n) (Icc 0 1) := by
  intro X hX Y hY hXY
  unfold hillTail
  have hXYn : X ^ n ≤ Y ^ n := Real.rpow_le_rpow hX.1 hXY (by linarith)
  gcongr
  exact hillTail_pos_denom hK hn X hX.1

/-! ## Regime III: interior critical point by the intermediate value theorem -/

/-- **Regime III interior critical point** (`lem:regime-iii-critical`). When the
density peak sits below the midpoint (`K < K*(n)`, i.e. `χ* < 1/2`), the pair-sum
derivative `g'(X) = φ(1-X) - φ(X)` is positive at `0` and negative at `χ*`, so by
the intermediate value theorem it vanishes somewhere in `(0, χ*)`. Stated for an
abstract continuous `g'` with the two sign facts the manuscript establishes. -/
theorem regimeIII_interior_critical {gprime : ℝ → ℝ} {chi : ℝ} (hchi : 0 < chi)
    (hcont : ContinuousOn gprime (Icc 0 chi))
    (hpos0 : 0 < gprime 0) (hneg : gprime chi < 0) :
    ∃ X0 ∈ Ioo 0 chi, gprime X0 = 0 := by
  have hmem : (0 : ℝ) ∈ Ioo (gprime chi) (gprime 0) := ⟨hneg, hpos0⟩
  have hsub := intermediate_value_Ioo' (le_of_lt hchi) hcont
  obtain ⟨X0, hX0, hval⟩ := hsub hmem
  exact ⟨X0, hX0, hval⟩

/-! ## Frontier conditions (T1)/(T2)/(T3): the no-erosion algebraic rearrangement

The "Equivalently, writing `w = d + u_d` and rearranging" step of §5. The
asymptotic limit derivations (the `K → 0`, `K → ∞` collapses of `W_max`) are the
deferred analytic content; the algebraic equivalence below is exact. -/

/-- (T1) at the small-`K` corner: `w + (â+b̂)/2 ≥ b+1 ⟺ u_d + d + (a-b)/2 ≥ 1`
(no-erosion `â = a`, `b̂ = b`, `w = d + u_d`). -/
theorem frontier_T1_iff (d ud a b : ℝ) :
    (d + ud) + (a + b) / 2 ≥ b + 1 ↔ ud + d + (a - b) / 2 ≥ 1 := by
  constructor <;> intro h <;> linarith

/-- (T2) at the `K_{G2} → ∞, K_{G1} → 0` corner:
`w + â/2 ≥ b+1 ⟺ u_d + d + a/2 - b ≥ 1`. -/
theorem frontier_T2_iff (d ud a b : ℝ) :
    (d + ud) + a / 2 ≥ b + 1 ↔ ud + d + a / 2 - b ≥ 1 := by
  constructor <;> intro h <;> linarith

/-- (T3) at the `K_{G1} → ∞, K_{G2} → 0` corner:
`w + b̂/2 ≥ b+1 ⟺ u_d + d - b/2 ≥ 1`. -/
theorem frontier_T3_iff (d ud b : ℝ) :
    (d + ud) + b / 2 ≥ b + 1 ↔ ud + d - b / 2 ≥ 1 := by
  constructor <;> intro h <;> linarith

/-! ## Basin-boundary functions `π_low, π_high, π_bind` (eq. pi-low/high/bind) -/

/-- `π_low := w - b - 1` (eq. pi-low); (Q3) ⟺ `π_low < 0`. -/
def piLow (w b : ℝ) : ℝ := w - b - 1

/-- `π_high := w - b - 1 + b̂(1-σ_{G2}) + â(1-σ_{G1})` (eq. pi-high);
(Q4) ⟺ `π_high > 0`. -/
def piHigh (w b bhat ahat sigG2 sigG1 : ℝ) : ℝ :=
  w - b - 1 + bhat * (1 - sigG2) + ahat * (1 - sigG1)

/-- `π_bind := 2(w-b-1) + 2(b̂+â) - W_max` (eq. pi-bind); (Q5) ⟺ `π_bind ≥ 0`. -/
def piBind (w b bhat ahat Wmax : ℝ) : ℝ := 2 * (w - b - 1) + 2 * (bhat + ahat) - Wmax

/-! ### `π_bind`-to-frontier linkage

The three frontier conditions of \Cref{prop:frontiers} arise by substituting the
corner value of `W_max := max_{[0,½]}[b̂ g_{G2} + â g_{G1}]` into `π_bind ≥ 0`. The
*limit* that collapses `W_max` to each corner value (`K → 0, ∞`) is the deferred
analytic content; the algebraic substitution below, taking that value as input, is
mechanized, and matches `frontier_T1/T2/T3_iff`. This is what wires `piBind` into the
basin-existence test rather than leaving it a free definition. -/

/-- (T1) small-`K` corner `W_max → â + b̂`: `π_bind ≥ 0 ⟺ w + (â+b̂)/2 ≥ b+1`. -/
theorem piBind_nonneg_T1 (w b bhat ahat : ℝ) :
    0 ≤ piBind w b bhat ahat (ahat + bhat) ↔ w + (ahat + bhat) / 2 ≥ b + 1 := by
  unfold piBind; constructor <;> intro h <;> linarith

/-- (T2) corner `K_{G2}→∞, K_{G1}→0`, `W_max → 2b̂ + â`: `π_bind ≥ 0 ⟺ w + â/2 ≥ b+1`. -/
theorem piBind_nonneg_T2 (w b bhat ahat : ℝ) :
    0 ≤ piBind w b bhat ahat (2 * bhat + ahat) ↔ w + ahat / 2 ≥ b + 1 := by
  unfold piBind; constructor <;> intro h <;> linarith

/-- (T3) corner `K_{G1}→∞, K_{G2}→0`, `W_max → 2â + b̂`: `π_bind ≥ 0 ⟺ w + b̂/2 ≥ b+1`. -/
theorem piBind_nonneg_T3 (w b bhat ahat : ℝ) :
    0 ≤ piBind w b bhat ahat (2 * ahat + bhat) ↔ w + bhat / 2 ≥ b + 1 := by
  unfold piBind; constructor <;> intro h <;> linarith

/-! ## (Q1)/(Q2b) analytic content and Lemma B.1 (`n=2`) — all proved

The `rpow`-calculus and mean-value lemmas the plan flagged as the dominant Phase-3
labor. (The general-`n` Lemma B.1 is in `Priors/RightSkew.lean`.) -/

/-- (Q1, calculus core) `h'(X) = -f(X)`: the Hill tail derivative is the negative
density, from which the density integrates to 1. Proved via the `Real.rpow`
const-power derivative and the quotient rule. -/
theorem hillTail_hasDeriv (hK : 0 < K) (hn : 1 ≤ n) {X : ℝ} (hX : 0 ≤ X) :
    HasDerivAt (hillTail K n) (-(hillDensity K n X)) X := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ n) (n * X ^ (n - 1)) X :=
    Real.hasDerivAt_rpow_const (Or.inr hn)
  have hden : HasDerivAt (fun x : ℝ => K ^ n + x ^ n) (n * X ^ (n - 1)) X :=
    (hasDerivAt_const_add_iff (K ^ n)).mpr hpow
  have hposD : (0 : ℝ) < K ^ n + X ^ n := by
    have h1 := Real.rpow_pos_of_pos hK n
    have h2 := Real.rpow_nonneg hX n
    linarith
  have hquot := (hasDerivAt_const X (K ^ n)).div hden hposD.ne'
  unfold hillTail
  convert hquot using 1
  unfold hillDensity
  have hD : K ^ n + X ^ n ≠ 0 := hposD.ne'
  field_simp
  ring

/-- **(Q2b)** The Hill tail is `(n/K^n)`-Lipschitz on `[0,1]`: the density bound
`f(z) = n K^n z^{n-1}/(K^n+z^n)^2 ≤ n/K^n` on `[0,1]` (drop `z^{n-1} ≤ 1`, bound
the denominator below by `K^{2n}`), composed with the one-dimensional mean value
theorem. Discharges `hillPrior.lipschitz`. -/
theorem hillTail_lipschitz (hK : 0 < K) (hn : 1 ≤ n) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |hillTail K n x - hillTail K n y| ≤ (n / K ^ n) * |x - y| := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hderiv : ∀ z ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (hillTail K n) (-(hillDensity K n z)) (Icc 0 1) z :=
    fun z hz => (hillTail_hasDeriv hK hn hz.1).hasDerivWithinAt
  have hbound : ∀ z ∈ Icc (0 : ℝ) 1, ‖-(hillDensity K n z)‖ ≤ n / K ^ n := by
    intro z hz
    have hKn : 0 < K ^ n := Real.rpow_pos_of_pos hK n
    have hzn : 0 ≤ z ^ n := Real.rpow_nonneg hz.1 n
    have hzn1' : 0 ≤ z ^ (n - 1) := Real.rpow_nonneg hz.1 _
    have hzn1 : z ^ (n - 1) ≤ 1 := Real.rpow_le_one hz.1 hz.2 (by linarith)
    have hposz : 0 < K ^ n + z ^ n := by linarith
    have hdenpos : 0 < (K ^ n + z ^ n) ^ 2 := pow_pos hposz 2
    have hdens_nonneg : 0 ≤ hillDensity K n z := by
      unfold hillDensity
      exact div_nonneg (mul_nonneg (mul_nonneg hn0 hKn.le) hzn1') (le_of_lt hdenpos)
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hdens_nonneg]
    unfold hillDensity
    rw [div_le_div_iff₀ hdenpos hKn]
    have t1 : 0 ≤ (1 - z ^ (n - 1)) * (n * (K ^ n) ^ 2) :=
      mul_nonneg (by linarith) (mul_nonneg hn0 (sq_nonneg _))
    have t2 : 0 ≤ n * (K ^ n) * z ^ n := mul_nonneg (mul_nonneg hn0 hKn.le) hzn
    have t3 : 0 ≤ n * (z ^ n) ^ 2 := mul_nonneg hn0 (sq_nonneg _)
    nlinarith [t1, t2, t3]
  intro x hx y hy
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc 0 1) hy hx
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at key

/-- The Hill density at `n = 2` in elementary (rpow-free) form:
`φ(X) = 2 K² X / (K² + X²)²`. -/
theorem hillDensity_two (K X : ℝ) :
    hillDensity K 2 X = 2 * K ^ 2 * X / (K ^ 2 + X ^ 2) ^ 2 := by
  unfold hillDensity
  have e1 : K ^ (2 : ℝ) = K ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e2 : X ^ (2 : ℝ) = X ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e3 : X ^ ((2 : ℝ) - 1) = X := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  rw [e1, e2, e3]

/-- **Lemma B.1, the `n = 2` (operative) case** — the cooperativity used in every
phase diagram. At `n = 2` the right-skew claim reduces to a polynomial identity:
with `χ*² = K²/3`, the density-ratio numerator difference is `2δ³(8χ*²+δ²) > 0`.
Kernel-checked, unlike the general-`n` `right_skew` above. -/
theorem right_skew_two (hK : 0 < K) {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ chistar K 2) :
    hillDensity K 2 (chistar K 2 - δ) < hillDensity K 2 (chistar K 2 + δ) := by
  have hcpos : 0 < chistar K 2 := by
    unfold chistar
    exact mul_pos hK (Real.rpow_pos_of_pos (by norm_num) _)
  have hsqrt : ((1 / 3 : ℝ) ^ ((1 / 2 : ℝ))) ^ 2 = 1 / 3 := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 3),
        show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  have hc2 : (chistar K 2) ^ 2 = K ^ 2 / 3 := by
    unfold chistar
    rw [show ((2 : ℝ) - 1) / ((2 : ℝ) + 1) = 1 / 3 by norm_num, mul_pow, hsqrt]
    ring
  have hK2 : K ^ 2 = 3 * (chistar K 2) ^ 2 := by rw [hc2]; ring
  have hd1 : (0 : ℝ) < (K ^ 2 + (chistar K 2 - δ) ^ 2) ^ 2 := by positivity
  have hd2 : (0 : ℝ) < (K ^ 2 + (chistar K 2 + δ) ^ 2) ^ 2 := by positivity
  rw [hillDensity_two, hillDensity_two, div_lt_div_iff₀ hd1 hd2, hK2]
  nlinarith [mul_pos (pow_pos hcpos 4) (pow_pos hδ 3),
             mul_pos (pow_pos hcpos 2) (pow_pos hδ 5), hcpos, hδ]

/-- The Hill family as a `ThresholdPrior` (the robustness question's concrete
witness). (Q2a) is fully proved; (Q2b)'s constant relies on `hillTail_lipschitz`. -/
noncomputable def hillPrior (hK : 0 < K) (hn : 1 ≤ n) : ThresholdPrior where
  tail := hillTail K n
  antitone := hillTail_antitoneOn hK hn
  lipConst := n / K ^ n
  lipschitz := hillTail_lipschitz hK hn

/-- **Hill discharge of model (B-low).** For the two-prior Hill model the tail-`0`
hypotheses of `modelFdelta_condBlow_iff` are exactly `hillTail_zero` (`F̄_g(0)=1`),
so (B-low) reduces, with no residual hypothesis, to the control inequality
`u_w < B + M` — the (Q3) endpoint condition of §5. -/
theorem hill_modelFdelta_condBlow_iff {K₂ n₂ K₁ n₁ : ℝ}
    (hK₂ : 0 < K₂) (hn₂ : 1 ≤ n₂) (hK₁ : 0 < K₁) (hn₁ : 1 ≤ n₁)
    (uw Bcap Mcap Aa cG2 cG1 : ℝ) :
    CondBlow (modelFdelta (hillPrior hK₂ hn₂) (hillPrior hK₁ hn₁) uw Bcap Mcap Aa cG2 cG1)
      ↔ uw < Bcap + Mcap := by
  apply modelFdelta_condBlow_iff
  · exact hillTail_zero hK₂ hn₂
  · exact hillTail_zero hK₁ hn₁

/-! ## The Hill prior is the log-logistic (Fisk) distribution

The manuscript's Hill tail `Kⁿ/(Kⁿ+Xⁿ)` is exactly the survival function `1/(1+(X/K)ⁿ)`
of the log-logistic (Fisk) distribution with scale `K` and shape `n`. So the
log-logistic prior is the Hill prior under its standard name; it needs no separate
discharge. -/

/-- **Hill tail = log-logistic survival.** `Kⁿ/(Kⁿ+Xⁿ) = 1/(1+(X/K)ⁿ)`. -/
theorem hillTail_eq_logLogistic {K n : ℝ} (hK : 0 < K) (hn : 1 ≤ n) (X : ℝ) (hX : 0 ≤ X) :
    hillTail K n X = 1 / (1 + (X / K) ^ n) := by
  unfold hillTail
  have hKn : (0 : ℝ) < K ^ n := Real.rpow_pos_of_pos hK n
  have hXn : (0 : ℝ) ≤ X ^ n := Real.rpow_nonneg hX n
  have hD : (0 : ℝ) < K ^ n + X ^ n := by linarith
  have h2 : (1 : ℝ) + X ^ n / K ^ n ≠ 0 :=
    ne_of_gt (by have := div_nonneg hXn hKn.le; linarith)
  rw [Real.div_rpow hX hK.le]
  field_simp

/-- The **log-logistic (Fisk) prior**, scale `K` and shape `n`: definitionally the
Hill prior (`hillTail_eq_logLogistic`), exposed under its standard name so it appears
in the robustness menu without a redundant re-certification. -/
noncomputable def logLogisticPrior (hK : 0 < K) (hn : 1 ≤ n) : ThresholdPrior :=
  hillPrior hK hn

end TwoGenie
