import TwoGenie.PerWisher

/-!
# Community dynamics: the Moran–Fermi ratio identity and Theorem 5.1

Formalizes §4 ("Prior-agnostic community dynamics"), the heart of the paper.

The community evolves by the Moran–Fermi pairwise-comparison protocol. A focal
wisher adopts a reference's binding with the Fermi probability
`σ_β(d) = 1/(1 + e^{-βd})`. The state `j ∈ {0,…,Nc}` counts `G2`-bound wishers.

`Nc` is the **effective informational population size** under the §2 sufficient-
information-density (mean-field) closure — the scale at which testimonial exposure
tracks the population binding fraction — not a literal community headcount. No graph
topology or local-neighborhood interaction is modeled; the closure enters only
through the population-averaged binding fraction.

Results (all kernel-checked):
* `fermi_ratio`        — `σ_β(-d)/σ_β(d) = e^{-βd}` (the Fermi detailed-balance ratio).
* `switch_rate_ratio`  — eq. (5): `T⁻(j)/T⁺(j) = exp(-F_Δ(j/Nc)/η_s)`; the
                          combinatorial sampling prefactors cancel.
* `ratio_identity`     — eq. (7): `ρ_{G2,G1}/ρ_{G1,G2} = exp((1/η_s) Σ F_Δ(j/Nc))`,
                          from the shared Karlin–Taylor denominator.
* `ratio_favored_iff`  — **Theorem 5.1**: `ρ_{G2,G1}/ρ_{G1,G2} > 1 ⟺ Σ F_Δ > 0`.
* `log_ratio_identity` — the exact selection rate `log(ρ-ratio) = (1/η_s) Σ F_Δ`.
-/

namespace TwoGenie

open Finset

/-- The Fermi (logit) response `σ_β(d) = 1/(1 + e^{-βd})` (eq. fermi-response). -/
noncomputable def fermi (β d : ℝ) : ℝ := 1 / (1 + Real.exp (-(β * d)))

/-- The Fermi response is strictly positive. -/
theorem fermi_pos (β d : ℝ) : 0 < fermi β d := by
  unfold fermi; positivity

/-- **Fermi detailed-balance ratio**: `σ_β(-d)/σ_β(d) = e^{-βd}`. This is the
algebraic source of eq. (5). -/
theorem fermi_ratio (β d : ℝ) : fermi β (-d) / fermi β d = Real.exp (-(β * d)) := by
  have hfd : fermi β d ≠ 0 := ne_of_gt (fermi_pos β d)
  have hkey : fermi β (-d) = Real.exp (-(β * d)) * fermi β d := by
    unfold fermi
    rw [show -(β * -d) = β * d by ring]
    have hpq : Real.exp (β * d) * Real.exp (-(β * d)) = 1 := by
      rw [← Real.exp_add]; simp
    have hp : (0 : ℝ) < 1 + Real.exp (β * d) := by positivity
    have hq : (0 : ℝ) < 1 + Real.exp (-(β * d)) := by positivity
    field_simp
    nlinarith [hpq]
  rw [hkey, mul_div_assoc, div_self hfd, mul_one]

/-! ## Switch rates and the cancellation of combinatorial prefactors

`T⁺(j)` and `T⁻(j)` share the *same* combinatorial sampling prefactor `pref j`
(the manuscript's "combinatorial prefactors cancel in the ratio"): an up-switch
samples a `G1` focal and `G2` reference, a down-switch the mirror, and both
sampling probabilities equal `((Nc-j)/Nc)·(j/(Nc-1))`. We carry `pref j` abstractly
and require only `pref j ≠ 0`. -/

variable (Nc : ℕ) (etas : ℝ) (Fdelta : ℝ → ℝ)

/-- Up-switch probability `T⁺(j)`: sampling prefactor times the Fermi response at
the payoff difference `F_Δ(j/Nc)` (selection intensity `β = 1/η_s`). -/
noncomputable def Tplus (pref : ℕ → ℝ) (j : ℕ) : ℝ :=
  pref j * fermi (1 / etas) (Fdelta ((j : ℝ) / (Nc : ℝ)))

/-- Down-switch probability `T⁻(j)`: the mirror, same prefactor, Fermi response at
`-F_Δ(j/Nc)`. -/
noncomputable def Tminus (pref : ℕ → ℝ) (j : ℕ) : ℝ :=
  pref j * fermi (1 / etas) (-(Fdelta ((j : ℝ) / (Nc : ℝ))))

/-- **eq. (5)**: the switch-rate ratio is `exp(-F_Δ(j/Nc)/η_s)`; the shared
combinatorial prefactor cancels. -/
theorem switch_rate_ratio (pref : ℕ → ℝ) (j : ℕ) (hpref : pref j ≠ 0) :
    Tminus Nc etas Fdelta pref j / Tplus Nc etas Fdelta pref j
      = Real.exp (-(Fdelta ((j : ℝ) / (Nc : ℝ)) / etas)) := by
  unfold Tminus Tplus
  rw [mul_div_mul_left _ _ hpref, fermi_ratio]
  rw [show (1 / etas) * Fdelta ((j : ℝ) / (Nc : ℝ)) = Fdelta ((j : ℝ) / (Nc : ℝ)) / etas by
    ring]

/-! ## Karlin–Taylor fixation probabilities and the ratio identity

`α_j := exp(-F_Δ(j/Nc)/η_s)` is the switch-rate ratio of eq. (5). The
Karlin–Taylor birth–death machinery (eq. 6) gives, for the absorbing chain,
`ρ_{G2,G1} = 1/D` and `ρ_{G1,G2} = P_{Nc-1}/D` with the common denominator
`D = Σ_{i<Nc} P_i`, `P_i = Π_{j=1}^{i} α_j`. -/

/-- The switch-rate ratio `α_j = exp(-F_Δ(j/Nc)/η_s)` of eq. (5). -/
noncomputable def alpha (j : ℕ) : ℝ := Real.exp (-(Fdelta ((j : ℝ) / (Nc : ℝ)) / etas))

/-- Karlin–Taylor partial product `P_i = Π_{j=1}^{i} α_j`. -/
noncomputable def Pprod (i : ℕ) : ℝ := ∏ j ∈ Finset.Ico 1 (i + 1), alpha Nc etas Fdelta j

/-- Common Karlin–Taylor denominator `D = Σ_{i=0}^{Nc-1} P_i`. -/
noncomputable def Dsum : ℝ := ∑ i ∈ Finset.range Nc, Pprod Nc etas Fdelta i

/-- `G2`-fixation probability from a single seed: `ρ_{G2,G1} = 1/D` (eq. 6, `φ_1`). -/
noncomputable def rhoG2G1 : ℝ := 1 / Dsum Nc etas Fdelta

/-- Reverse fixation probability: `ρ_{G1,G2} = P_{Nc-1}/D` (`1 - φ_{Nc-1}`). -/
noncomputable def rhoG1G2 : ℝ := Pprod Nc etas Fdelta (Nc - 1) / Dsum Nc etas Fdelta

theorem alpha_pos (j : ℕ) : 0 < alpha Nc etas Fdelta j := Real.exp_pos _

theorem Pprod_pos (i : ℕ) : 0 < Pprod Nc etas Fdelta i :=
  Finset.prod_pos (fun j _ => alpha_pos Nc etas Fdelta j)

theorem Dsum_pos (hNc : 1 ≤ Nc) : 0 < Dsum Nc etas Fdelta :=
  Finset.sum_pos (fun i _ => Pprod_pos Nc etas Fdelta i)
    ⟨0, Finset.mem_range.mpr (by omega)⟩

/-- **Ratio identity** (eq. 7): the shared denominator cancels, leaving a single
product that telescopes into an exponential of the cumulative payoff sum:
`ρ_{G2,G1}/ρ_{G1,G2} = exp((1/η_s) Σ_{j=1}^{Nc-1} F_Δ(j/Nc))`. -/
theorem ratio_identity (hNc : 1 ≤ Nc) :
    rhoG2G1 Nc etas Fdelta / rhoG1G2 Nc etas Fdelta
      = Real.exp ((1 / etas) * ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / (Nc : ℝ))) := by
  have hD : Dsum Nc etas Fdelta ≠ 0 := ne_of_gt (Dsum_pos Nc etas Fdelta hNc)
  have hP : Pprod Nc etas Fdelta (Nc - 1) ≠ 0 := ne_of_gt (Pprod_pos Nc etas Fdelta (Nc - 1))
  -- The shared denominator cancels: ρ-ratio = 1 / P_{Nc-1}.
  have hcancel : rhoG2G1 Nc etas Fdelta / rhoG1G2 Nc etas Fdelta
      = 1 / Pprod Nc etas Fdelta (Nc - 1) := by
    unfold rhoG2G1 rhoG1G2
    field_simp
  rw [hcancel]
  -- P_{Nc-1} = exp(-(1/η_s) Σ F_Δ).
  have hPeq : Pprod Nc etas Fdelta (Nc - 1)
      = Real.exp (-((1 / etas) * ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / (Nc : ℝ)))) := by
    unfold Pprod alpha
    rw [Nat.sub_add_cancel hNc, ← Real.exp_sum]
    congr 1
    have hterm : ∀ j ∈ Finset.Ico 1 Nc,
        -(Fdelta ((j : ℝ) / (Nc : ℝ)) / etas)
          = (-(1 / etas)) * Fdelta ((j : ℝ) / (Nc : ℝ)) := by
      intro j _; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, neg_mul]
  rw [hPeq, Real.exp_neg, one_div, inv_inv]

/-- **Theorem 5.1** (Within-community ratio-favoredness). At any selection intensity
`β = 1/η_s > 0`, `G2` is ratio-favored over `G1` iff the cumulative payoff
differential over the interior grid is strictly positive. -/
theorem ratio_favored_iff (hNc : 1 ≤ Nc) (hetas : 0 < etas) :
    rhoG2G1 Nc etas Fdelta / rhoG1G2 Nc etas Fdelta > 1
      ↔ 0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / (Nc : ℝ)) := by
  rw [ratio_identity Nc etas Fdelta hNc, gt_iff_lt, Real.one_lt_exp_iff]
  have hinv : 0 < 1 / etas := by positivity
  constructor
  · intro h
    have hmul : (0 : ℝ) < etas * ((1 / etas) * ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / (Nc : ℝ))) :=
      mul_pos hetas h
    rwa [← mul_assoc, mul_one_div, div_self (ne_of_gt hetas), one_mul] at hmul
  · intro h
    exact mul_pos hinv h

/-- The exact selection rate: `log(ρ_{G2,G1}/ρ_{G1,G2}) = (1/η_s) Σ F_Δ(j/Nc)`.
This is the rate `F̄̄_Δ/η_s` of eq. (ratio-integral) at the discrete-sum level,
before the Riemann-sum approximation. -/
theorem log_ratio_identity (hNc : 1 ≤ Nc) :
    Real.log (rhoG2G1 Nc etas Fdelta / rhoG1G2 Nc etas Fdelta)
      = (1 / etas) * ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / (Nc : ℝ)) := by
  rw [ratio_identity Nc etas Fdelta hNc, Real.log_exp]

/-! ## The Karlin–Taylor fixation probability `φ_k` (eq. 6), derived not assumed

The closed forms `ρ_{G2,G1} = 1/D` and `ρ_{G1,G2} = P_{Nc-1}/D` are, in the
manuscript, the `k=1` and `k=Nc-1` specializations of the Karlin–Taylor
fixation-probability formula `φ_k = (Σ_{i<k} P_i)/D` (eq. 6) for the absorbing
birth–death chain. Here `φ_k` is defined and the connection is *proved*:
`φ` satisfies the absorbing boundary conditions `φ_0 = 0`, `φ_{Nc} = 1` and the
first-step harmonic recurrence `T⁺(j)(φ_{j+1}-φ_j) = T⁻(j)(φ_j-φ_{j-1})` — so it is
genuinely the fixation probability of the chain — and `ρ_{G2,G1} = φ_1`,
`ρ_{G1,G2} = 1 - φ_{Nc-1}`. The two `rho` definitions are thus theorems about `φ`,
not bare stipulations. -/

/-- **Karlin–Taylor fixation probability** from `k` G2-bound seeds (eq. 6):
`φ_k = (Σ_{i=0}^{k-1} P_i) / D`. -/
noncomputable def fixation (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range k, Pprod Nc etas Fdelta i) / Dsum Nc etas Fdelta

/-- `P_0 = 1` (empty product). -/
theorem Pprod_zero : Pprod Nc etas Fdelta 0 = 1 := by
  unfold Pprod; rw [Finset.Ico_self, Finset.prod_empty]

/-- `P_{i+1} = P_i · α_{i+1}` (one factor of the Karlin–Taylor product). -/
theorem Pprod_succ (i : ℕ) :
    Pprod Nc etas Fdelta (i + 1) = Pprod Nc etas Fdelta i * alpha Nc etas Fdelta (i + 1) := by
  unfold Pprod
  rw [Finset.prod_Ico_succ_top (show (1 : ℕ) ≤ i + 1 by omega)]

/-- Absorbing boundary at the all-`G1` corner: `φ_0 = 0`. -/
theorem fixation_zero : fixation Nc etas Fdelta 0 = 0 := by
  simp [fixation]

/-- Absorbing boundary at the all-`G2` corner: `φ_{Nc} = 1`. -/
theorem fixation_Nc (hNc : 1 ≤ Nc) : fixation Nc etas Fdelta Nc = 1 := by
  unfold fixation
  rw [show (∑ i ∈ Finset.range Nc, Pprod Nc etas Fdelta i) = Dsum Nc etas Fdelta from rfl,
      div_self (ne_of_gt (Dsum_pos Nc etas Fdelta hNc))]

/-- **`ρ_{G2,G1} = φ_1`**: single-seed G2-fixation probability is the `k=1` value of
the Karlin–Taylor formula (`P_0 = 1`, so `φ_1 = 1/D`). -/
theorem fixation_one : fixation Nc etas Fdelta 1 = rhoG2G1 Nc etas Fdelta := by
  unfold fixation rhoG2G1
  rw [Finset.sum_range_one, Pprod_zero]

/-- **`ρ_{G1,G2} = 1 - φ_{Nc-1}`**: reverse fixation is hitting `j=0` from `j=Nc-1`,
and `1 - φ_{Nc-1} = (D - Σ_{i<Nc-1}P_i)/D = P_{Nc-1}/D`. -/
theorem rhoG1G2_eq_one_sub_fixation (hNc : 1 ≤ Nc) :
    rhoG1G2 Nc etas Fdelta = 1 - fixation Nc etas Fdelta (Nc - 1) := by
  unfold rhoG1G2 fixation
  have hD : Dsum Nc etas Fdelta ≠ 0 := ne_of_gt (Dsum_pos Nc etas Fdelta hNc)
  have hsplit : Dsum Nc etas Fdelta
      = (∑ i ∈ Finset.range (Nc - 1), Pprod Nc etas Fdelta i) + Pprod Nc etas Fdelta (Nc - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, Nc = m + 1 := ⟨Nc - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show Dsum (m + 1) etas Fdelta
          = ∑ i ∈ Finset.range (m + 1), Pprod (m + 1) etas Fdelta i from rfl,
        Finset.sum_range_succ]
  rw [eq_sub_iff_add_eq, ← add_div,
      show Pprod Nc etas Fdelta (Nc - 1) + ∑ i ∈ Finset.range (Nc - 1), Pprod Nc etas Fdelta i
          = Dsum Nc etas Fdelta from by rw [hsplit]; ring]
  exact div_self hD

/-- **First-step harmonic recurrence** of the absorbing birth–death chain:
`T⁺(j)(φ_{j+1}-φ_j) = T⁻(j)(φ_j-φ_{j-1})` for `1 ≤ j`. Together with the boundary
values this characterizes `φ` as the chain's fixation probability; it holds because
`P_{j} = P_{j-1}·α_j` and the Fermi rates satisfy `σ_β(-d) = e^{-βd}σ_β(d)`. -/
theorem fixation_recurrence (pref : ℕ → ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Tplus Nc etas Fdelta pref j * (fixation Nc etas Fdelta (j + 1) - fixation Nc etas Fdelta j)
      = Tminus Nc etas Fdelta pref j
          * (fixation Nc etas Fdelta j - fixation Nc etas Fdelta (j - 1)) := by
  obtain ⟨jp, rfl⟩ : ∃ jp, j = jp + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hd1 : fixation Nc etas Fdelta (jp + 1 + 1) - fixation Nc etas Fdelta (jp + 1)
      = Pprod Nc etas Fdelta (jp + 1) / Dsum Nc etas Fdelta := by
    unfold fixation; rw [Finset.sum_range_succ]; ring
  have hd2 : fixation Nc etas Fdelta (jp + 1) - fixation Nc etas Fdelta jp
      = Pprod Nc etas Fdelta jp / Dsum Nc etas Fdelta := by
    unfold fixation; rw [Finset.sum_range_succ]; ring
  rw [hd1, hd2, Pprod_succ Nc etas Fdelta jp]
  unfold Tplus Tminus alpha
  set d := Fdelta ((↑(jp + 1) : ℝ) / (↑Nc : ℝ)) with hd
  have hfermi : fermi (1 / etas) (-d) = Real.exp (-(d / etas)) * fermi (1 / etas) d := by
    have h := fermi_ratio (1 / etas) d
    rw [show (1 / etas) * d = d / etas from by ring] at h
    rwa [div_eq_iff (ne_of_gt (fermi_pos (1 / etas) d))] at h
  rw [hfermi]
  ring

/-! ## The Moran–Fermi combinatorial prefactor, instantiated

`switch_rate_ratio` carries the sampling prefactor abstractly as `pref j`, needing
only `pref j ≠ 0`. The fact that the up- and down-switch rates *share* a prefactor
(so it cancels) is the manuscript's "combinatorial prefactors cancel": the up-switch
samples a G1-bound focal and a G2-bound reference, the down-switch the mirror, and
both sampling probabilities equal `j(Nc-j)/(Nc(Nc-1))`. -/

/-- Up-switch sampling factor: a `G1`-bound focal (one of `Nc-j`) and a `G2`-bound
reference (one of `j`), on a community of `Nc` with `Nc-1` candidate partners. -/
noncomputable def samplingUp (j : ℕ) : ℝ := ((Nc : ℝ) - j) / Nc * ((j : ℝ) / (Nc - 1))

/-- Down-switch sampling factor: the mirror (a `G2`-bound focal, a `G1`-bound
reference). -/
noncomputable def samplingDown (j : ℕ) : ℝ := ((j : ℝ) / Nc) * (((Nc : ℝ) - j) / (Nc - 1))

/-- **Shared combinatorial prefactor.** The up- and down-switch sampling factors are
equal, so the prefactor genuinely cancels in `switch_rate_ratio` — the fact that
file abstracts as `pref j`. -/
theorem sampling_symm (j : ℕ) : samplingUp Nc j = samplingDown Nc j := by
  unfold samplingUp samplingDown; ring

/-- The sampling prefactor is strictly positive for an interior state `1 ≤ j < Nc`
(`Nc ≥ 2`), so it satisfies the `pref j ≠ 0` hypothesis of `switch_rate_ratio`. -/
theorem samplingUp_pos {j : ℕ} (h1 : 1 ≤ j) (h2 : j < Nc) (hNc : 2 ≤ Nc) :
    0 < samplingUp Nc j := by
  unfold samplingUp
  have hNcR : (0 : ℝ) < Nc := by exact_mod_cast lt_of_lt_of_le (by norm_num) hNc
  have hjR : (0 : ℝ) < j := by exact_mod_cast h1
  have hjNc : (j : ℝ) < Nc := by exact_mod_cast h2
  have hNc1 : (0 : ℝ) < (Nc : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Nc := by exact_mod_cast hNc
    linarith
  exact mul_pos (div_pos (by linarith) hNcR) (div_pos hjR hNc1)

end TwoGenie
