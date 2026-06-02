import TwoGenie.Structural

/-!
# Basin accessibility: the race, cycling rule-out, and Proposition 5.4

Formalizes §4.2 ("Basin accessibility"). Directional selection pressure
(Theorem 5.1) is separated from operational accessibility, governed by three
constraints.

The accessibility inequalities scale with the **effective informational population
size** `Nc` (the §2 mean-field / sufficient-information-density closure); no literal
community scale is assumed. The interaction degree governs closure validity, while
`Nc` sets the barrier scale `c_depth·Nc/η_s` — orthogonal knobs.

Kernel-checked:
* `race_iff` — eq. (9): legibility wins the race against resource crisis,
  `τ_Θ < τ_{S=0} ⟺ c̄(Θ-L₀) < ρ_L(S₀-S_min)`.
* `ledger_monotone`, `resource_antitone` — eq. (joint-dynamics): the slow-plane
  coordinates advance monotonically, so the joint chain **cannot cycle**
  (the Weitz limit-cycle regime is structurally excluded under Assumptions 3, 5).
* `cdepth_nonneg` — the quasi-potential barrier height `c_depth = -∫₀^{χ*} F_Δ`
  is non-negative when `F_Δ ≤ 0` on `[0, χ*]` (from (A) + (B-low)).
* `prop54_log` — **Proposition 5.4**, operational form. The Kramers/Laplace
  asymptotic `E[τ] ∼ √Nc · exp(c_depth·Nc/η_s)` is **not derived here** — it is
  the plan's Phase-3 / CSLib analytic content. Following the plan's fallback
  ("axiomatize the residual asymptotic step"), we take the Kramers *form* as an
  explicit hypothesis and verify what the paper concludes from it: the
  log-linearized accessibility constraint eq. (10),
  `log E[τ] = log c + ½ log Nc + c_depth·Nc/η_s`, whose dominant term is the
  barrier exponent. No `sorry`: the deferred step is a visible hypothesis.
-/

namespace TwoGenie

open MeasureTheory

/-- **Legibility-vs-resource race** (eq. 9). With all rates positive, the
legibility ledger crosses its threshold before the resource pool hits crisis iff
`c̄(Θ-L₀) < ρ_L(S₀-S_min)`. Here `τ_Θ = (Θ-L₀)/(ρ_L Nc λ)`,
`τ_{S=0} = (S₀-S_min)/(c̄ Nc λ)`. -/
theorem race_iff (rhoL cbar Nc lam Theta L0 S0 Smin : ℝ)
    (hrho : 0 < rhoL) (hc : 0 < cbar) (hNc : 0 < Nc) (hlam : 0 < lam) :
    (Theta - L0) / (rhoL * Nc * lam) < (S0 - Smin) / (cbar * Nc * lam)
      ↔ cbar * (Theta - L0) < rhoL * (S0 - Smin) := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  rw [show (Theta - L0) * (cbar * Nc * lam) = (Nc * lam) * (cbar * (Theta - L0)) by ring,
      show (S0 - Smin) * (rhoL * Nc * lam) = (Nc * lam) * (rhoL * (S0 - Smin)) by ring,
      mul_lt_mul_iff_right₀ (show (0 : ℝ) < Nc * lam by positivity)]

/-- **Cycling rule-out, part 1** (eq. joint-dynamics): the legibility ledger
`L_t = L₀ + ρ_L Nc λ · t` is monotone non-decreasing (it cannot return). -/
theorem ledger_monotone (L0 m : ℝ) (hm : 0 ≤ m) : Monotone (fun t => L0 + m * t) := by
  intro a b hab
  dsimp only
  nlinarith [mul_le_mul_of_nonneg_left hab hm]

/-- **Cycling rule-out, part 2** (eq. joint-dynamics): the resource pool
`S_t = S₀ - c̄ Nc λ · t` is monotone non-increasing. Together with
`ledger_monotone`, the slow-plane coordinates advance monotonically, structurally
excluding the Weitz oscillating regime. -/
theorem resource_antitone (S0 m : ℝ) (hm : 0 ≤ m) : Antitone (fun t => S0 - m * t) := by
  intro a b hab
  dsimp only
  nlinarith [mul_le_mul_of_nonneg_left hab hm]

/-- The quasi-potential barrier height `c_depth = -∫₀^{χ*} F_Δ` (the manuscript's
`cdepth`). -/
noncomputable def cdepth (Fdelta : ℝ → ℝ) (chistar : ℝ) : ℝ :=
  -∫ x in (0 : ℝ)..chistar, Fdelta x

/-- **Barrier height is non-negative.** Under (A) + (B-low) the differential is
non-positive on `[0, χ*]` (it is negative below its first zero `χ*`), so its
integral is `≤ 0` and the barrier height `c_depth = -∫ ≥ 0`. -/
theorem cdepth_nonneg (Fdelta : ℝ → ℝ) {chistar : ℝ} (hchi : 0 ≤ chistar)
    (hneg : ∀ x ∈ Set.Icc (0 : ℝ) chistar, Fdelta x ≤ 0) :
    0 ≤ cdepth Fdelta chistar := by
  unfold cdepth
  have h1 : 0 ≤ ∫ x in (0 : ℝ)..chistar, (-Fdelta x) := by
    apply intervalIntegral.integral_nonneg hchi
    intro x hx
    have := hneg x hx
    linarith
  rw [intervalIntegral.integral_neg] at h1
  linarith

/-- **Barrier height is strictly positive.** If `F_Δ` is continuous and *strictly*
negative on the open interval `(0, χ*)` with `χ* > 0`, then `∫₀^{χ*} F_Δ < 0`, so the
barrier `c_depth = -∫ > 0`. This is the strict strengthening of `cdepth_nonneg` the
accessibility ceiling needs in order to divide by `c_depth`. -/
theorem cdepth_pos (Fdelta : ℝ → ℝ) {chistar : ℝ} (hchi : 0 < chistar)
    (hcont : Continuous Fdelta) (hneg : ∀ x ∈ Set.Ioo (0 : ℝ) chistar, Fdelta x < 0) :
    0 < cdepth Fdelta chistar := by
  unfold cdepth
  have hpos : 0 < ∫ x in (0 : ℝ)..chistar, (-Fdelta x) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.neg.intervalIntegrable 0 chistar)
      (fun x hx => by have := hneg x hx; linarith) hchi
  rwa [intervalIntegral.integral_neg] at hpos

/-- **Barrier height strictly positive, from a threshold root.** `IsThresholdRoot`
gives `F_Δ < 0` everywhere below `χ*`, in particular on `(0, χ*)`, which is exactly
what `cdepth_pos` needs — so the strict barrier needed to divide by `c_depth` follows
directly from the threshold-root structure, with no extra positivity hypothesis. -/
theorem cdepth_pos_of_threshold_root (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta) {chistar : ℝ}
    (hRoot : IsThresholdRoot Fdelta chistar) : 0 < cdepth Fdelta chistar := by
  obtain ⟨hmem, _, hbelow, _⟩ := hRoot
  exact cdepth_pos Fdelta hmem.1 hcont (fun x hx => hbelow x hx.2)

/-- **Ledger hitting time (eq. 8).** A strictly rising linear ledger
`L_t = L₀ + m·t` (`m = ρ_L N_c λ > 0`) crosses the legibility threshold `Θ` at the
single time `τ_Θ = (Θ − L₀)/m`. This is the closed form the race condition `race_iff`
reads against; the analogous resource-crisis time is the same algebra with the
depletion rate. -/
theorem ledger_hitting_time (L0 m Theta t : ℝ) (hm : 0 < m) :
    L0 + m * t = Theta ↔ t = (Theta - L0) / m := by
  rw [eq_div_iff (ne_of_gt hm)]; constructor <;> intro h <;> linarith

/-- The running quasi-potential barrier `-∫₀^x F_Δ` (definitionally `cdepth Fdelta x`;
named for the variational statement). -/
noncomputable def runningDepth (Fdelta : ℝ → ℝ) (x : ℝ) : ℝ := cdepth Fdelta x

/-- **The running barrier is maximized at the threshold `χ*`.** Under `IsThresholdRoot`
(`F_Δ < 0` below `χ*`, `> 0` above), the running depth `-∫₀^x F_Δ` increases up to `χ*`
and decreases after, so it is maximal at `χ*` on `[0,1]`. This closes the variational
gap: the barrier top of the discrete chain sits at `χ*`. -/
theorem cdepth_le_threshold (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta) {chistar : ℝ}
    (hRoot : IsThresholdRoot Fdelta chistar) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, cdepth Fdelta x ≤ cdepth Fdelta chistar := by
  obtain ⟨_, hzero, hbelow, habove⟩ := hRoot
  intro x hx
  unfold cdepth
  rcases le_total x chistar with hxc | hcx
  · have hsub : (∫ y in (0 : ℝ)..chistar, Fdelta y)
        = (∫ y in (0 : ℝ)..x, Fdelta y) + ∫ y in x..chistar, Fdelta y :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
    have hneg : (∫ y in x..chistar, Fdelta y) ≤ 0 := by
      have h0 : 0 ≤ ∫ y in x..chistar, (-Fdelta y) := by
        apply intervalIntegral.integral_nonneg hxc
        intro y hy
        rcases lt_or_eq_of_le hy.2 with h | h
        · linarith [hbelow y h]
        · rw [h, hzero]; norm_num
      rw [intervalIntegral.integral_neg] at h0
      linarith
    linarith
  · have hsub : (∫ y in (0 : ℝ)..x, Fdelta y)
        = (∫ y in (0 : ℝ)..chistar, Fdelta y) + ∫ y in chistar..x, Fdelta y :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
    have hpos : 0 ≤ ∫ y in chistar..x, Fdelta y := by
      apply intervalIntegral.integral_nonneg hcx
      intro y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · rw [← h]; exact le_of_eq hzero.symm
      · exact (habove y h (hy.2.trans hx.2)).le
    linarith

/-- `runningDepth` is maximal at `χ*` (restatement of `cdepth_le_threshold`). -/
theorem runningDepth_max_at_threshold (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    {chistar : ℝ} (hRoot : IsThresholdRoot Fdelta chistar) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, runningDepth Fdelta x ≤ runningDepth Fdelta chistar :=
  cdepth_le_threshold Fdelta hcont hRoot

/-- **Lipschitz Riemann-sum error (the discrete-to-continuous bridge).** For an
`L`-Lipschitz `F_Δ`, the right-endpoint Riemann sum on the uniform grid `j/N_c`
approximates the integral with explicit, finite error:
`|∫₀^{k/N_c} F_Δ − (1/N_c)Σ_{j=1}^{k} F_Δ(j/N_c)| ≤ L·k/N_c²`. No asymptotics: a
direct per-cell mean-value estimate summed over the partition. This is the lemma
that lets the `c_depth`-rate drop its bridge hypothesis. -/
theorem riemann_sum_error_lipschitz (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |Fdelta x - Fdelta y| ≤ L * |x - y|)
    {Nc : ℕ} (hNc : 0 < Nc) (k : ℕ) :
    |(∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
        - (∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / Nc|
      ≤ L * k / (Nc : ℝ) ^ 2 := by
  have hNcR : (0 : ℝ) < Nc := by exact_mod_cast hNc
  set a : ℕ → ℝ := fun i => (i : ℝ) / Nc with ha
  have hcell : ∀ i : ℕ, a (i + 1) - a i = 1 / Nc := by
    intro i; simp only [ha]; push_cast; ring
  have hmono : ∀ i : ℕ, a i ≤ a (i + 1) := by
    intro i
    have h := hcell i
    have h2 : (0 : ℝ) < 1 / Nc := by positivity
    linarith
  have hint : ∀ i : ℕ, IntervalIntegrable Fdelta MeasureTheory.volume (a i) (a (i + 1)) :=
    fun i => hcont.intervalIntegrable _ _
  -- partition the integral
  have hsplit : (∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
      = ∑ i ∈ Finset.range k, ∫ x in (a i)..(a (i + 1)), Fdelta x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => hint i)]
    have h0 : a 0 = 0 := by simp [ha]
    have hk0 : a k = (k : ℝ) / Nc := by simp only [ha]
    rw [h0, hk0]
  -- the Riemann sum as constant cell integrals
  have hsum2 : (∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / Nc
      = ∑ i ∈ Finset.range k, ∫ _ in (a i)..(a (i + 1)), Fdelta (a (i + 1)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const, hcell i, smul_eq_mul]
    have : a (i + 1) = ((i + 1 : ℝ) / Nc) := by simp only [ha]; push_cast; ring
    rw [this]; ring
  rw [hsplit, hsum2, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range k,
      (∫ x in (a i)..(a (i + 1)), Fdelta x) - ∫ _ in (a i)..(a (i + 1)), Fdelta (a (i + 1))
        = ∫ x in (a i)..(a (i + 1)), (Fdelta x - Fdelta (a (i + 1))) :=
    fun i _ => (intervalIntegral.integral_sub (hint i) intervalIntegrable_const).symm
  rw [Finset.sum_congr rfl hterm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ i ∈ Finset.range k,
      |∫ x in (a i)..(a (i + 1)), (Fdelta x - Fdelta (a (i + 1)))| ≤ L / Nc * (1 / Nc) := by
    intro i _
    have hcellbound : ∀ x ∈ Set.uIoc (a i) (a (i + 1)),
        ‖Fdelta x - Fdelta (a (i + 1))‖ ≤ L / Nc := by
      intro x hx
      rw [Set.uIoc_of_le (hmono i)] at hx
      have hxle : |x - a (i + 1)| ≤ 1 / Nc := by
        rw [abs_of_nonpos (by linarith [hx.2])]
        linarith [hx.1, hcell i]
      rw [Real.norm_eq_abs]
      calc |Fdelta x - Fdelta (a (i + 1))| ≤ L * |x - a (i + 1)| := hLip x (a (i + 1))
        _ ≤ L * (1 / Nc) := mul_le_mul_of_nonneg_left hxle hL
        _ = L / Nc := by ring
    have hk := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a i) (b := a (i + 1)) (C := L / Nc)
      (f := fun x => Fdelta x - Fdelta (a (i + 1))) hcellbound
    rw [Real.norm_eq_abs] at hk
    have hwidth : |a (i + 1) - a i| = 1 / Nc := by
      rw [hcell i]; exact abs_of_nonneg (by positivity)
    rw [hwidth] at hk
    exact hk
  calc ∑ i ∈ Finset.range k,
          |∫ x in (a i)..(a (i + 1)), (Fdelta x - Fdelta (a (i + 1)))|
      ≤ ∑ _i ∈ Finset.range k, L / Nc * (1 / Nc) := Finset.sum_le_sum hbound
    _ = (k : ℝ) * (L / Nc * (1 / Nc)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = L * k / (Nc : ℝ) ^ 2 := by ring

/-- **Proposition 5.4 (operational form), eq. (10).** *Given* the Kramers/Laplace
asymptotic form for the mean fixation time (the Phase-3 analytic step, taken here
as an explicit hypothesis rather than derived), the mean fixation time
log-linearizes so the barrier exponent `c_depth·Nc/η_s` is the dominant term. This
is the content that the operational-accessibility constraint eq. (10) reads off. -/
theorem prop54_log (c cdepthVal etas Nc meanFix : ℝ) (hc : 0 < c) (hNc : 0 < Nc)
    (hForm : meanFix = c * Real.sqrt Nc * Real.exp (cdepthVal * Nc / etas)) :
    Real.log meanFix = Real.log c + Real.log Nc / 2 + cdepthVal * Nc / etas := by
  rw [hForm, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (le_of_lt hNc), Real.log_exp]

/-! ## Proposition 5.4, rate form — a kernel-checked replacement for the asymptotic

The exact Laplace/Kramers asymptotic `E[τ] ∼ √Nc · exp(c_depth·Nc/η_s)` is *not*
proved here (its `√Nc` prefactor needs the discrete Laplace method, beyond the
current library). But the operational-accessibility constraint eq. (10) only uses
the **exponent**, with the prefactor "absorbed into the logarithm." That part we
*can* prove rigorously and finitely, by the plan's fallback ("an explicit
finite-`Nc` bound provable by direct calculation"): a sum of positive terms lies
between its largest term and `card ×` its largest term.

`log_Pprod` exhibits `log P_k` as the discrete quasi-potential barrier exponent
`-(1/η_s) Σ_{j≤k} F_Δ(j/Nc)`; `fixation_sum_brackets` brackets the
mean-first-passage sum; `fixation_log_rate` reads off the log-rate: the exponent
is the barrier term **exactly**, the sub-exponential prefactor pinned to
`[1, Nc-1]` (an `O(log Nc)` correction). That is exactly the precision eq. (10)
operates at — and it does not depend on, or claim, the exact `√Nc`. -/

/-- `log P_k = -(1/η_s) Σ_{j=1}^{k} F_Δ(j/Nc)`: the log of the Karlin–Taylor
partial product is the discrete quasi-potential barrier exponent. -/
theorem log_Pprod (Nc : ℕ) (etas : ℝ) (Fdelta : ℝ → ℝ) (k : ℕ) :
    Real.log (Pprod Nc etas Fdelta k)
      = ∑ j ∈ Finset.Ico 1 (k + 1), (-(Fdelta ((j : ℝ) / (Nc : ℝ)) / etas)) := by
  unfold Pprod alpha
  rw [Real.log_prod (fun j _ => (Real.exp_pos _).ne')]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.log_exp]

/-- **Prop 5.4 (rate form), brackets.** The mean-first-passage / quasi-potential
sum `Σ_{k=1}^{Nc-1} P_k` is bracketed between its largest term and `(Nc-1)` times
its largest term. Elementary (positive terms), no asymptotics. -/
theorem fixation_sum_brackets (Nc : ℕ) (etas : ℝ) (Fdelta : ℝ → ℝ) (hNc : 2 ≤ Nc) :
    ∃ kmax ∈ Finset.Ico 1 Nc,
      Pprod Nc etas Fdelta kmax ≤ ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k ∧
      ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k
        ≤ ((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax := by
  have hne : (Finset.Ico 1 Nc).Nonempty := by rw [Finset.nonempty_Ico]; omega
  obtain ⟨kmax, hkmem, hkmax⟩ :=
    Finset.exists_max_image (Finset.Ico 1 Nc) (Pprod Nc etas Fdelta) hne
  have hcard : ((Finset.Ico 1 Nc).card : ℝ) = (Nc : ℝ) - 1 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 1 ≤ Nc), Nat.cast_one]
  refine ⟨kmax, hkmem, ?_, ?_⟩
  · exact Finset.single_le_sum (fun i _ => (Pprod_pos Nc etas Fdelta i).le) hkmem
  · calc ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k
        ≤ (Finset.Ico 1 Nc).card • Pprod Nc etas Fdelta kmax :=
          Finset.sum_le_card_nsmul _ _ _ (fun b hb => hkmax b hb)
      _ = ((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax := by rw [nsmul_eq_mul, hcard]

/-- **Prop 5.4 (rate form), log.** The log of the mean-first-passage sum equals the
discrete barrier exponent `log P_{kmax}` up to an additive `O(log Nc)` term
(`0 ≤ · ≤ log(Nc-1)`). The exponential rate is exact; the prefactor is pinned
logarithmically — the resolution eq. (10) works at. -/
theorem fixation_log_rate (Nc : ℕ) (etas : ℝ) (Fdelta : ℝ → ℝ) (hNc : 2 ≤ Nc) :
    ∃ kmax ∈ Finset.Ico 1 Nc,
      Real.log (Pprod Nc etas Fdelta kmax)
          ≤ Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k) ∧
      Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
          ≤ Real.log (Pprod Nc etas Fdelta kmax) + Real.log ((Nc : ℝ) - 1) := by
  obtain ⟨kmax, hkmem, hlo, hhi⟩ := fixation_sum_brackets Nc etas Fdelta hNc
  have hPpos : 0 < Pprod Nc etas Fdelta kmax := Pprod_pos Nc etas Fdelta kmax
  have hNc1 : (0 : ℝ) < (Nc : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hNc
    linarith
  have hSpos : 0 < ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k :=
    lt_of_lt_of_le hPpos hlo
  refine ⟨kmax, hkmem, Real.log_le_log hPpos hlo, ?_⟩
  calc Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
      ≤ Real.log (((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax) := Real.log_le_log hSpos hhi
    _ = Real.log (Pprod Nc etas Fdelta kmax) + Real.log ((Nc : ℝ) - 1) := by
        rw [Real.log_mul (ne_of_gt hNc1) (ne_of_gt hPpos)]; ring

/-- **Prop 5.4 (rate form), continuous-`c_depth`.** Re-expresses `fixation_log_rate`
against the continuous barrier height `c_depth = −∫₀^{χ*} F_Δ` (`cdepth`).

The discrete-to-continuous bridge — the Riemann-sum estimate
`(1/N_c)Σ_{j≤k} F_Δ(j/N_c) → ∫₀^{k/N_c} F_Δ` plus convergence of the grid-max to
the continuous max — enters as the two **named hypotheses** `hUpper`/`hLower`:
the discrete quasi-potential `log P_k` stays within an `O(1)` constant `C` of
`(N_c/η_s)·c_depth` (above for all `k`, below for some `k`). For an `L`-Lipschitz
`F_Δ` (the bounded-density tail, `hillTail_lipschitz`) this `C` is independent of
`N_c`, so the conclusion is `log(fixation sum) = (N_c/η_s)·c_depth + O(log N_c)`.

The bridge is a visible hypothesis, not a `sorry`; discharging it is the same
deferred analytic step as the Riemann/Lipschitz content. The wiring below is
kernel-checked. -/
theorem fixation_log_rate_cdepth (Nc : ℕ) (etas chistar C : ℝ) (Fdelta : ℝ → ℝ)
    (hNc : 2 ≤ Nc)
    (hUpper : ∀ k ∈ Finset.Ico 1 Nc,
        Real.log (Pprod Nc etas Fdelta k) ≤ ((Nc : ℝ) / etas) * cdepth Fdelta chistar + C)
    (hLower : ∃ k ∈ Finset.Ico 1 Nc,
        ((Nc : ℝ) / etas) * cdepth Fdelta chistar - C ≤ Real.log (Pprod Nc etas Fdelta k)) :
    ((Nc : ℝ) / etas) * cdepth Fdelta chistar - C
        ≤ Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k) ∧
    Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
        ≤ ((Nc : ℝ) / etas) * cdepth Fdelta chistar + C + Real.log ((Nc : ℝ) - 1) := by
  have hne : (Finset.Ico 1 Nc).Nonempty := by rw [Finset.nonempty_Ico]; omega
  obtain ⟨kmax, hkmem, hkmax⟩ :=
    Finset.exists_max_image (Finset.Ico 1 Nc) (Pprod Nc etas Fdelta) hne
  have hPpos : 0 < Pprod Nc etas Fdelta kmax := Pprod_pos Nc etas Fdelta kmax
  have hlo : Pprod Nc etas Fdelta kmax ≤ ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k :=
    Finset.single_le_sum (fun i _ => (Pprod_pos Nc etas Fdelta i).le) hkmem
  have hSpos : 0 < ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k := lt_of_lt_of_le hPpos hlo
  have hcard : ((Finset.Ico 1 Nc).card : ℝ) = (Nc : ℝ) - 1 := by
    rw [Nat.card_Ico, Nat.cast_sub (by omega : 1 ≤ Nc), Nat.cast_one]
  have hhi : ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k
      ≤ ((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax := by
    calc ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k
        ≤ (Finset.Ico 1 Nc).card • Pprod Nc etas Fdelta kmax :=
          Finset.sum_le_card_nsmul _ _ _ (fun b hb => hkmax b hb)
      _ = ((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax := by rw [nsmul_eq_mul, hcard]
  have hNc1 : (0 : ℝ) < (Nc : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hNc
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨k', hk'mem, hk'⟩ := hLower
    have hk'le : Real.log (Pprod Nc etas Fdelta k') ≤ Real.log (Pprod Nc etas Fdelta kmax) :=
      Real.log_le_log (Pprod_pos Nc etas Fdelta k') (hkmax k' hk'mem)
    have hkmaxle : Real.log (Pprod Nc etas Fdelta kmax)
        ≤ Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k) := Real.log_le_log hPpos hlo
    linarith
  · have hub := hUpper kmax hkmem
    have hsumlog : Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
        ≤ Real.log (((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax) := Real.log_le_log hSpos hhi
    rw [Real.log_mul (ne_of_gt hNc1) (ne_of_gt hPpos)] at hsumlog
    linarith

/-- **Explicit accessibility ceiling (no asymptotics).** From the *proved* rate bound
`log E[τ] ≤ (N_c/η_s)·c_depth + C + log(N_c−1)` (the `fixation_log_rate` upper bracket
read against `c_depth`) and a tenure budget on that same explicit quantity, fixation
completes within tenure: `E[τ] ≤ T·λ_seed`. The `log(N_c−1)` and `C` corrections are
kept — the ceiling is *not* pretended to be exactly linear in `N_c`. -/
theorem accessibility_sufficient {meanFix Nc etas cdepthVal C Tten lseed : ℝ}
    (hmf : 0 < meanFix) (hbudget : 0 < Tten * lseed)
    (hRate : Real.log meanFix
        ≤ (Nc / etas) * cdepthVal + C + Real.log (Nc - 1))
    (hBound : (Nc / etas) * cdepthVal + C + Real.log (Nc - 1)
        ≤ Real.log (Tten * lseed)) :
    meanFix ≤ Tten * lseed := by
  have hlog : Real.log meanFix ≤ Real.log (Tten * lseed) := le_trans hRate hBound
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hmf, Real.exp_log hbudget] at this

/-- **Leading-order ceiling, as a corollary with explicit side conditions.** Folding
the `log(N_c−1)` correction into a linear slack `ε·N_c` (`hNcLog`) turns the explicit
ceiling into the clean linear form `((c_depth/η_s)+ε)·N_c + C ≤ log(T·λ_seed)`. So the
displayed one-pager ceiling is the leading-order simplification of the kernel-checked
inequality `accessibility_sufficient`, not an independent asymptotic claim. -/
theorem leading_ceiling_sufficient {meanFix Nc etas cdepthVal C eps Tten lseed : ℝ}
    (hmf : 0 < meanFix) (hbudget : 0 < Tten * lseed)
    (hRate : Real.log meanFix
        ≤ (Nc / etas) * cdepthVal + C + Real.log (Nc - 1))
    (hNcLog : Real.log (Nc - 1) ≤ eps * Nc)
    (hBound : (cdepthVal / etas + eps) * Nc + C ≤ Real.log (Tten * lseed)) :
    meanFix ≤ Tten * lseed := by
  refine accessibility_sufficient hmf hbudget hRate ?_
  have e1 : (Nc / etas) * cdepthVal = (cdepthVal / etas) * Nc := by ring
  have e2 : (cdepthVal / etas + eps) * Nc = (cdepthVal / etas) * Nc + eps * Nc := by ring
  rw [e1]; rw [e2] at hBound; linarith [hNcLog]

/-- **Discrete barrier ≈ continuous barrier (derived from the Riemann bound).** The
discrete quasi-potential `log P_k` equals the continuous barrier `(N_c/η_s)·c_depth`
evaluated at the grid endpoint `k/N_c`, within the *explicit* error `L·k/(η_s·N_c)`.
No bridge hypothesis: this is `log_Pprod` + the reindex + `riemann_sum_error_lipschitz`.
Taking `k = k*` with `k*/N_c = χ*` (the barrier top) gives exactly the
`|log P − (N_c/η_s)·c_depth| ≤ C` that `fixation_log_rate_cdepth` previously assumed. -/
theorem discrete_barrier_near_cdepth (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |Fdelta x - Fdelta y| ≤ L * |x - y|)
    {Nc : ℕ} (hNc : 0 < Nc) {etas : ℝ} (hetas : 0 < etas) (k : ℕ) :
    |Real.log (Pprod Nc etas Fdelta k) - ((Nc : ℝ) / etas) * cdepth Fdelta ((k : ℝ) / Nc)|
      ≤ L * k / (etas * Nc) := by
  have hNcR : (0 : ℝ) < Nc := by exact_mod_cast hNc
  have hSeq : (∑ j ∈ Finset.Ico 1 (k + 1), Fdelta ((j : ℝ) / Nc))
      = ∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1; push_cast; ring
  have hlog : Real.log (Pprod Nc etas Fdelta k)
      = -(∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / etas := by
    rw [log_Pprod,
        show (∑ j ∈ Finset.Ico 1 (k + 1), -(Fdelta ((j : ℝ) / Nc) / etas))
            = (∑ j ∈ Finset.Ico 1 (k + 1), Fdelta ((j : ℝ) / Nc)) * (-(1 / etas)) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _ => by ring),
        hSeq]
    ring
  have hRiem := riemann_sum_error_lipschitz Fdelta hcont hL hLip hNc k
  unfold cdepth
  rw [hlog,
      show -(∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / etas
            - ((Nc : ℝ) / etas) * (-∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
          = ((Nc : ℝ) * (∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
              - ∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / etas from by ring]
  have hkey : |(Nc : ℝ) * (∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
      - ∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)| ≤ L * k / Nc := by
    have h1 : (Nc : ℝ) * (∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
        - ∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)
        = Nc * ((∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
            - (∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / Nc) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hNcR]
    calc (Nc : ℝ) * |(∫ x in (0 : ℝ)..((k : ℝ) / Nc), Fdelta x)
            - (∑ i ∈ Finset.range k, Fdelta ((i + 1 : ℝ) / Nc)) / Nc|
          ≤ Nc * (L * k / Nc ^ 2) := mul_le_mul_of_nonneg_left hRiem hNcR.le
      _ = L * k / Nc := by field_simp
  rw [abs_div, abs_of_pos hetas, div_le_iff₀ hetas,
      show L * k / (etas * Nc) * etas = L * k / Nc from by field_simp]
  exact hkey

/-- **Seed-rate floor for a non-empty accessibility window.** Purely the log/exp
restatement: the favoredness floor lies under the accessibility ceiling — i.e. some
community size is both favored and reachable — iff the exploration rate clears
`exp(c_depth·floor/η_s)/T_tenure`. With `floor = 1/(½−χ*)` this is the minimum seed
rate of the one-pager's synthesis box. -/
theorem window_nonempty_iff_seed_rate {floor cdepthVal etas Tten lseed : ℝ}
    (hcd : 0 < cdepthVal) (hetas : 0 < etas) (hTls : 0 < Tten * lseed) :
    floor ≤ (etas / cdepthVal) * Real.log (Tten * lseed)
      ↔ Real.exp (cdepthVal * floor / etas) ≤ Tten * lseed := by
  rw [← Real.le_log_iff_exp_le hTls, div_le_iff₀ hetas, div_mul_eq_mul_div,
      le_div_iff₀ hcd, mul_comm floor cdepthVal, mul_comm etas (Real.log (Tten * lseed))]

/-- **Discrete barrier ceiling for *every* `k` (the variational bound).** Combining
`discrete_barrier_near_cdepth` with `cdepth_le_threshold` (the barrier max at `χ*`):
`log P_k ≤ (N_c/η_s)·c_depth(χ*) + L/η_s` for all `k < N_c`. This is the bound that
actually justifies the accessibility ceiling — the max over `k`, no chosen endpoint. -/
theorem max_logPprod_le_cdepth (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |Fdelta x - Fdelta y| ≤ L * |x - y|)
    {chistar : ℝ} (hRoot : IsThresholdRoot Fdelta chistar)
    {Nc : ℕ} (hNc : 0 < Nc) {etas : ℝ} (hetas : 0 < etas) :
    ∀ k, k < Nc → Real.log (Pprod Nc etas Fdelta k)
        ≤ ((Nc : ℝ) / etas) * cdepth Fdelta chistar + L / etas := by
  intro k hk
  have hNcR : (0 : ℝ) < Nc := by exact_mod_cast hNc
  have hkle : (k : ℝ) ≤ Nc := by exact_mod_cast le_of_lt hk
  have hkNc : (k : ℝ) / Nc ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hNcR]; exact hkle⟩
  have hbar := discrete_barrier_near_cdepth Fdelta hcont hL hLip hNc hetas k
  have hupper : Real.log (Pprod Nc etas Fdelta k)
      ≤ ((Nc : ℝ) / etas) * cdepth Fdelta ((k : ℝ) / Nc) + L * (k : ℝ) / (etas * Nc) := by
    have := (abs_le.mp hbar).2; linarith
  have hmul : ((Nc : ℝ) / etas) * cdepth Fdelta ((k : ℝ) / Nc)
      ≤ ((Nc : ℝ) / etas) * cdepth Fdelta chistar :=
    mul_le_mul_of_nonneg_left (cdepth_le_threshold Fdelta hcont hRoot _ hkNc)
      (div_nonneg (Nat.cast_nonneg Nc) hetas.le)
  have herr : L * (k : ℝ) / (etas * Nc) ≤ L / etas := by
    rw [show L * (k : ℝ) / (etas * Nc) = (L / etas) * ((k : ℝ) / Nc) from by ring]
    calc (L / etas) * ((k : ℝ) / Nc) ≤ (L / etas) * 1 :=
          mul_le_mul_of_nonneg_left hkNc.2 (div_nonneg hL hetas.le)
      _ = L / etas := by ring
  linarith

/-- **Accessibility ceiling, no `hUpper` hypothesis (`#1`).** The log of the
mean-first-passage sum is bounded by the continuous barrier plus the honest finite
corrections `L/η_s + log(N_c−1)` — derived end-to-end from the Lipschitz Riemann bound
and the variational max, with no opaque bridge assumption. -/
theorem fixation_log_rate_cdepth_le (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |Fdelta x - Fdelta y| ≤ L * |x - y|)
    {chistar : ℝ} (hRoot : IsThresholdRoot Fdelta chistar)
    {Nc : ℕ} (hNc : 2 ≤ Nc) {etas : ℝ} (hetas : 0 < etas) :
    Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
      ≤ ((Nc : ℝ) / etas) * cdepth Fdelta chistar + L / etas + Real.log ((Nc : ℝ) - 1) := by
  have hNc0 : 0 < Nc := by omega
  obtain ⟨kmax, hkmem, _, hhi⟩ := fixation_sum_brackets Nc etas Fdelta hNc
  have hPpos : 0 < Pprod Nc etas Fdelta kmax := Pprod_pos Nc etas Fdelta kmax
  have hNc1 : (0 : ℝ) < (Nc : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hNc
    linarith
  have hSpos : 0 < ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k :=
    lt_of_lt_of_le hPpos
      (Finset.single_le_sum (fun i _ => (Pprod_pos Nc etas Fdelta i).le) hkmem)
  have hkmaxlt : kmax < Nc := (Finset.mem_Ico.mp hkmem).2
  calc Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
      ≤ Real.log (((Nc : ℝ) - 1) * Pprod Nc etas Fdelta kmax) := Real.log_le_log hSpos hhi
    _ = Real.log (Pprod Nc etas Fdelta kmax) + Real.log ((Nc : ℝ) - 1) := by
        rw [Real.log_mul (ne_of_gt hNc1) (ne_of_gt hPpos)]; ring
    _ ≤ ((Nc : ℝ) / etas) * cdepth Fdelta chistar + L / etas + Real.log ((Nc : ℝ) - 1) := by
        linarith [max_logPprod_le_cdepth Fdelta hcont hL hLip hRoot hNc0 hetas kmax hkmaxlt]

/-- **Accessibility capstone (`#8`): favored ∧ reachable, one inspectable theorem with
no hidden bridges.** For a community above the favoredness floor whose finite, corrected
barrier budget `(N_c/η_s)·c_depth(χ*) + L/η_s + log(N_c−1)` fits under `log(T·λ_seed)`,
the cooperative basin is both ratio-favored (cumulative sum positive) and reached within
tenure (mean-first-passage sum `≤ T·λ_seed`). Every hypothesis is concrete: continuity,
(C), Lipschitz, the threshold-root structure of `χ*`, the size floor, and the seed
budget. The `√N_c` Kramers prefactor is *not* used. -/
theorem accessible_and_favored (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    (hC : CondC Fdelta) {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |Fdelta x - Fdelta y| ≤ L * |x - y|)
    {chistar : ℝ} (hRoot : IsThresholdRoot Fdelta chistar) (hchi : chistar < 1 / 2)
    {Nc : ℕ} (hNc : 2 ≤ Nc) {etas : ℝ} (hetas : 0 < etas) {Tten lseed : ℝ}
    (hTls : 0 < Tten * lseed)
    (hfloor : 1 / (1 / 2 - chistar) < (Nc : ℝ))
    (hseed : ((Nc : ℝ) / etas) * cdepth Fdelta chistar + L / etas + Real.log ((Nc : ℝ) - 1)
        ≤ Real.log (Tten * lseed)) :
    (0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc))
      ∧ (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k) ≤ Tten * lseed := by
  refine ⟨favoredness_sufficient_threshold Fdelta hC hRoot hchi hfloor, ?_⟩
  have hlog : Real.log (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k) ≤ Real.log (Tten * lseed) :=
    le_trans (fixation_log_rate_cdepth_le Fdelta hcont hL hLip hRoot hNc hetas) hseed
  have hne : (Finset.Ico 1 Nc).Nonempty := by rw [Finset.nonempty_Ico]; omega
  obtain ⟨kmax, hkmem⟩ := hne
  have hSpos : 0 < ∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k :=
    lt_of_lt_of_le (Pprod_pos Nc etas Fdelta kmax)
      (Finset.single_le_sum (fun i _ => (Pprod_pos Nc etas Fdelta i).le) hkmem)
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hSpos, Real.exp_log hTls] at this

/-- **Attainability against resource depletion.** The capstone `accessible_and_favored`
with the free horizon `Tten` instantiated as the resource-pool depletion time
`(S0 - Smin) / (cbar * Nc * lambda_a)` of the negative-sum game. This is the exact form of
the manuscript's basin-attainability theorem after the tenure→depletion remodeling: a
community fixates before the shared pool empties precisely when its size clears the
favoredness floor and the barrier budget fits under the depletion deadline. The deadline is
a value substituted into the universally-quantified `Tten`, so this inherits the axiom base
of `accessible_and_favored` with no new proof obligation. -/
theorem accessible_and_favored_depletion (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    (hC : CondC Fdelta) {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |Fdelta x - Fdelta y| ≤ L * |x - y|)
    {chistar : ℝ} (hRoot : IsThresholdRoot Fdelta chistar) (hchi : chistar < 1 / 2)
    {Nc : ℕ} (hNc : 2 ≤ Nc) {etas : ℝ} (hetas : 0 < etas)
    {S0 Smin cbar lambda_a lseed : ℝ}
    (hdep : 0 < (S0 - Smin) / (cbar * (Nc : ℝ) * lambda_a) * lseed)
    (hfloor : 1 / (1 / 2 - chistar) < (Nc : ℝ))
    (hseed : ((Nc : ℝ) / etas) * cdepth Fdelta chistar + L / etas + Real.log ((Nc : ℝ) - 1)
        ≤ Real.log ((S0 - Smin) / (cbar * (Nc : ℝ) * lambda_a) * lseed)) :
    (0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc))
      ∧ (∑ k ∈ Finset.Ico 1 Nc, Pprod Nc etas Fdelta k)
          ≤ (S0 - Smin) / (cbar * (Nc : ℝ) * lambda_a) * lseed :=
  accessible_and_favored (Tten := (S0 - Smin) / (cbar * (Nc : ℝ) * lambda_a)) (lseed := lseed)
    Fdelta hcont hC hL hLip hRoot hchi hNc hetas hdep hfloor hseed

end TwoGenie
