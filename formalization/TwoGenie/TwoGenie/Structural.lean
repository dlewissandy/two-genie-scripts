import TwoGenie.Community

/-!
# Structural conditions (A), (B), (C) and Proposition 5.2

Formalizes §4.1.1 ("Favoredness Conditions") and Proposition 5.2
("Sufficiency of the favoredness conditions").

The three structural conditions on the payoff differential `F_Δ : ℝ → ℝ` are
predicates, *visible to any reader applying the theorem*:
* `CondA`       — (A) monotonicity on `[0,1]`.
* `CondBlow`    — (B-low) `F_Δ(0) < 0`.
* `CondBhigh`   — (B-high) `0 < F_Δ(1)`.
* `CondC`       — (C) centro-symmetric pair-sum `≥ 0` on `[0,1/2]`.
* `CondCstrict` — the strict clause of (C).

**Proposition 5.2** comes in two forms:
* `favoredness_sufficient` — the discrete core: *if* every interior grid pair-sum
  is `≥ 0` and one is `> 0`, the cumulative sum is `> 0`. The strict grid point is
  a hypothesis here.
* `favoredness_sufficient_cont` — the **manuscript's continuous statement**: from
  `CondC` on `[0,1/2]`, continuity of `F_Δ`, and a strict point `X₀ ∈ (0,1)`, the
  cumulative sum is `> 0` for *all* `N_c` above an explicit threshold
  (`⌊1/(2δ)⌋+1`, the `N_c > 1/w_*` of the prose). This discharges the discrete
  hypothesis via the continuous→grid bridge `grid_point_in_interval` (a grid point
  lands in any sub-`[0,1]` interval wider than `1/N_c`) and `condC_grid_nonneg`
  ((C) ⇒ all grid pairs `≥ 0`, by the `g(X)=g(1-X)` symmetry).
-/

namespace TwoGenie

open Finset

variable (Fdelta : ℝ → ℝ)

/-- (A) Monotonicity: `F_Δ` is non-decreasing on `[0,1]`. -/
def CondA : Prop := MonotoneOn Fdelta (Set.Icc 0 1)

/-- (B-low): `F_Δ(0) < 0` (the all-`G1` corner is a rest point). -/
def CondBlow : Prop := Fdelta 0 < 0

/-- (B-high): `0 < F_Δ(1)` (the all-`G2` corner is a rest point). -/
def CondBhigh : Prop := 0 < Fdelta 1

/-- (C): centro-symmetric pair-sum is non-negative on `[0,1/2]`. -/
def CondC : Prop := ∀ X ∈ Set.Icc (0 : ℝ) (1 / 2), 0 ≤ Fdelta X + Fdelta (1 - X)

/-- The strict clause of (C): strict positivity at some point of `[0,1/2]`. -/
def CondCstrict : Prop := ∃ X ∈ Set.Icc (0 : ℝ) (1 / 2), 0 < Fdelta X + Fdelta (1 - X)

/-- **The sharp basin criterion (net area).** The *net* centro-symmetric area on
`[0,½]` — i.e. `∫₀^{½} g`, which equals `∫₀¹ F_Δ` after folding `[½,1]` onto `[0,½]`
(proved as `condNet_integral_eq`).
This is what within-community favoredness actually turns on, and it is strictly
*weaker* than `CondC`: (C) forces **every** reflected pair `g(X) = F_Δ(X)+F_Δ(1−X)`
nonnegative; `CondNet` asks only that their integral be positive. See
`condNet_of_condC`. -/
def CondNet : Prop := 0 < ∫ X in (0 : ℝ)..(1 / 2), (Fdelta X + Fdelta (1 - X))

/-- **Region nesting** (§5, "The regions nest"): under (B-low), condition (C) at
`X = 0` forces (B-high). So `π_bind > 0` paired with (A)+(B-low) yields `π_high > 0`
automatically: `F_Δ(1) ≥ -F_Δ(0) > 0`. -/
theorem Bhigh_of_C_Blow (hC : CondC Fdelta) (hBlow : CondBlow Fdelta) :
    CondBhigh Fdelta := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) := by constructor <;> norm_num
  have := hC 0 h0
  simp only [sub_zero] at this
  unfold CondBhigh CondBlow at *
  linarith

/-! ## Proposition 5.2: the discrete pairing argument -/

/-- For an interior grid point, the reflected coordinate `(Nc-j)/Nc` equals the
real reflection `1 - j/Nc`. Bridges the natural-subtraction form used in the
pairing proof to condition (C)'s `1 - X` form. -/
theorem grid_reflect {Nc j : ℕ} (hj : j ∈ Finset.Ico 1 Nc) :
    (((Nc - j : ℕ) : ℝ)) / (Nc : ℝ) = 1 - (j : ℝ) / (Nc : ℝ) := by
  rw [Finset.mem_Ico] at hj
  have hjle : j ≤ Nc := le_of_lt hj.2
  have hNc0 : (Nc : ℝ) ≠ 0 := by
    have : 0 < Nc := lt_of_lt_of_le hj.1 (le_of_lt hj.2)
    positivity
  rw [Nat.cast_sub hjle]
  field_simp

/-- **Proposition 5.2** (Sufficiency of the favoredness conditions), discharged
form. If every interior centro-symmetric grid pair-sum is non-negative
(condition (C) on the grid) and at least one is strictly positive (the strict
clause), then the cumulative interior sum is strictly positive — so `G2` is
within-community ratio-favored by `ratio_favored_iff` (Theorem 5.1).

Proof: pairing `j ↔ Nc-j` is an involution of `{1,…,Nc-1}`, so
`Σ F_Δ((Nc-j)/Nc) = Σ F_Δ(j/Nc)`; hence `Σ_j [F_Δ(j/Nc)+F_Δ((Nc-j)/Nc)] = 2·Σ`.
The bracket sum is positive (all terms `≥ 0`, one `> 0`), so `Σ > 0`. -/
theorem favoredness_sufficient (Nc : ℕ) (Fdelta : ℝ → ℝ)
    (hpair : ∀ j ∈ Finset.Ico 1 Nc,
      0 ≤ Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc))
    (hstrict : ∃ j ∈ Finset.Ico 1 Nc,
      0 < Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc)) :
    0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc) := by
  -- The reflection `j ↦ Nc - j` is an involution of `Ico 1 Nc`; reindex.
  have hreindex :
      (∑ j ∈ Finset.Ico 1 Nc, Fdelta (((Nc - j : ℕ) : ℝ) / Nc))
        = ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc) := by
    apply Finset.sum_nbij' (fun j => Nc - j) (fun j => Nc - j)
    · intro a ha; simp only [Finset.mem_Ico] at *; omega
    · intro a ha; simp only [Finset.mem_Ico] at *; omega
    · intro a ha; simp only [Finset.mem_Ico] at ha; omega
    · intro a ha; simp only [Finset.mem_Ico] at ha; omega
    · intro a _; rfl
  -- The bracket sum equals 2·(interior sum).
  have hsum2 :
      ∑ j ∈ Finset.Ico 1 Nc, (Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc))
        = 2 * ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc) := by
    rw [Finset.sum_add_distrib, hreindex]; ring
  have hpos :
      0 < ∑ j ∈ Finset.Ico 1 Nc,
        (Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc)) :=
    Finset.sum_pos' hpair hstrict
  rw [hsum2] at hpos
  linarith

/-! ## The continuous → grid bridge (closing the Prop 5.2 gap)

`favoredness_sufficient` takes the strict grid point as a hypothesis. The
manuscript instead argues from continuity + a strict-positive interval of width
`w_*` and `N_c > 1/w_*`. The lemmas below supply that bridge: a grid point lands
in any sub-`[0,1]` interval wider than the grid step, continuity of `F_Δ` turns
the strict clause (C) into such an interval, and (C) gives non-negativity at
*all* grid points (by the `g(X)=g(1-X)` symmetry), so `favoredness_sufficient`
fires for all sufficiently large `N_c`. -/

/-- A grid point `j/N_c` lands in any interval `(a,b) ⊆ [0,1]` wider than `1/N_c`. -/
theorem grid_point_in_interval {a b : ℝ} {Nc : ℕ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hw : 1 < (b - a) * (Nc : ℝ)) :
    ∃ j : ℕ, 1 ≤ j ∧ j < Nc ∧ a < (j : ℝ) / Nc ∧ (j : ℝ) / Nc < b := by
  have hNc : 0 < (Nc : ℝ) := by
    rcases Nat.eq_zero_or_pos Nc with h | h
    · rw [h] at hw; norm_num at hw
    · exact_mod_cast h
  have haNc : 0 ≤ a * (Nc : ℝ) := mul_nonneg ha hNc.le
  refine ⟨⌊a * (Nc : ℝ)⌋₊ + 1, Nat.le_add_left 1 _, ?_, ?_, ?_⟩
  · -- j < Nc
    have hgt : a * (Nc : ℝ) < (↑(⌊a * (Nc : ℝ)⌋₊ + 1) : ℝ) := by
      push_cast; linarith [Nat.lt_floor_add_one (a * (Nc : ℝ))]
    have hle : (↑(⌊a * (Nc : ℝ)⌋₊ + 1) : ℝ) ≤ a * (Nc : ℝ) + 1 := by
      push_cast; linarith [Nat.floor_le haNc]
    have : (↑(⌊a * (Nc : ℝ)⌋₊ + 1) : ℝ) < (Nc : ℝ) := by nlinarith [mul_le_of_le_one_left hNc.le hb]
    exact_mod_cast this
  · rw [lt_div_iff₀ hNc]; push_cast; linarith [Nat.lt_floor_add_one (a * (Nc : ℝ))]
  · rw [div_lt_iff₀ hNc]; push_cast; nlinarith [Nat.floor_le haNc]

/-- (C) gives non-negativity of *every* interior grid pair-sum (by the
`g(X)=g(1-X)` symmetry, so `X > 1/2` reflects into `[0,1/2]`). -/
theorem condC_grid_nonneg (Fdelta : ℝ → ℝ) {Nc : ℕ} (hC : CondC Fdelta) (j : ℕ)
    (hj : j ∈ Finset.Ico 1 Nc) :
    0 ≤ Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc) := by
  rw [Finset.mem_Ico] at hj
  have hNc : 0 < (Nc : ℝ) := by
    have hn : 0 < Nc := by omega
    exact_mod_cast hn
  have hjle : (j : ℝ) ≤ Nc := by exact_mod_cast le_of_lt hj.2
  rw [grid_reflect (Finset.mem_Ico.mpr hj)]
  set X : ℝ := (j : ℝ) / Nc with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1 : X ≤ 1 := by rw [hX, div_le_one hNc]; exact hjle
  by_cases h : X ≤ 1 / 2
  · exact hC X ⟨hX0, h⟩
  · have := hC (1 - X) ⟨by linarith, by linarith⟩
    rw [show (1 : ℝ) - (1 - X) = X by ring] at this
    linarith

/-- **Proposition 5.2, continuous form.** Under (A is automatic), (C) on `[0,1/2]`,
continuity of `F_Δ`, and a strict point `X₀ ∈ (0,1)` of the centro-symmetric
pair-sum, the cumulative interior sum is strictly positive for all `N_c` above a
threshold determined by the width of the strict-positive interval. This is the
bridge the manuscript's prose argues and that `favoredness_sufficient` consumed
as a hypothesis. -/
theorem favoredness_sufficient_cont (Fdelta : ℝ → ℝ) (hC : CondC Fdelta)
    (hcont : Continuous Fdelta) {X₀ : ℝ} (hX₀0 : 0 < X₀) (hX₀1 : X₀ < 1)
    (hstrict : 0 < Fdelta X₀ + Fdelta (1 - X₀)) :
    ∃ N₀ : ℕ, ∀ Nc ≥ N₀, 0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc) := by
  -- g X := F_Δ X + F_Δ (1-X) is continuous and positive at X₀; get an open ball.
  set g : ℝ → ℝ := fun X => Fdelta X + Fdelta (1 - X) with hg
  have hgcont : Continuous g := hcont.add (hcont.comp (continuous_const.sub continuous_id))
  have hopen : IsOpen (g ⁻¹' Set.Ioi 0) := hgcont.isOpen_preimage _ isOpen_Ioi
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen X₀ hstrict
  -- δ chosen so the interval (X₀-δ, X₀+δ) stays inside (0,1) and the ball.
  set δ : ℝ := min (ε / 2) (min (X₀ / 2) ((1 - X₀) / 2)) with hδ_def
  have hδpos : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδX : δ ≤ X₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ1 : δ ≤ (1 - X₀) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set a : ℝ := X₀ - δ with ha_def
  set b : ℝ := X₀ + δ with hb_def
  have ha0 : (0 : ℝ) ≤ a := by rw [ha_def]; linarith
  have hb1 : b ≤ 1 := by rw [hb_def]; linarith
  have hwidth : b - a = 2 * δ := by rw [ha_def, hb_def]; ring
  have hgpos : ∀ X, a < X → X < b → 0 < g X := by
    intro X hXa hXb
    have hd : dist X X₀ < ε := by
      rw [Real.dist_eq, abs_lt]; rw [ha_def] at hXa; rw [hb_def] at hXb
      constructor <;> linarith
    exact hball (Metric.mem_ball.mpr hd)
  refine ⟨⌊1 / (2 * δ)⌋₊ + 1, fun Nc hNc => ?_⟩
  have h2δ : (0 : ℝ) < 2 * δ := by linarith
  have hNcbig : 1 < (b - a) * (Nc : ℝ) := by
    rw [hwidth]
    have hge : (1 : ℝ) / (2 * δ) < Nc := by
      have : (↑(⌊1 / (2 * δ)⌋₊ + 1) : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hNc
      have := Nat.lt_floor_add_one (1 / (2 * δ)); push_cast at *; linarith
    rw [div_lt_iff₀ h2δ] at hge; linarith [hge]
  obtain ⟨j, hj1, hjN, hja, hjb⟩ := grid_point_in_interval ha0 hb1 hNcbig
  refine favoredness_sufficient Nc Fdelta (fun k hk => condC_grid_nonneg Fdelta hC k hk) ?_
  refine ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjN⟩, ?_⟩
  rw [grid_reflect (Finset.mem_Ico.mpr ⟨hj1, hjN⟩)]
  exact hgpos _ hja hjb

/-- **Explicit `χ*`-based community-size floor (sharp Proposition 5.2).** With (C)
giving every reflected grid pair `≥ 0`, favoredness needs only one strictly positive
pair; the centro-symmetric sum is strictly positive on the whole interval `(χ, ½)`
(at the tipping point `χ = χ*`, both `F_Δ(X)` and `F_Δ(1−X)` are positive there).
A grid node lands in `(χ, ½)` as soon as

  `N_c > 1/(½ − χ)`,

the explicit floor. This is the operational hinge: the same `χ*` sets `c_depth`, so
this floor feeds the basin-accessibility window of Proposition 5.4. -/
theorem favoredness_sufficient_chistar (Fdelta : ℝ → ℝ) (hC : CondC Fdelta)
    {chi : ℝ} (hchi0 : 0 ≤ chi) (hchi : chi < 1 / 2)
    (hpos : ∀ X, chi < X → X < 1 / 2 → 0 < Fdelta X + Fdelta (1 - X))
    {Nc : ℕ} (hNc : 1 / (1 / 2 - chi) < (Nc : ℝ)) :
    0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc) := by
  have hw0 : (0 : ℝ) < 1 / 2 - chi := by linarith
  have hNcbig : 1 < (1 / 2 - chi) * (Nc : ℝ) := by
    rw [mul_comm]; exact (div_lt_iff₀ hw0).mp hNc
  obtain ⟨j, hj1, hjN, hja, hjb⟩ :=
    grid_point_in_interval hchi0 (by norm_num : (1 / 2 : ℝ) ≤ 1) hNcbig
  refine favoredness_sufficient Nc Fdelta (fun k hk => condC_grid_nonneg Fdelta hC k hk) ?_
  refine ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjN⟩, ?_⟩
  rw [grid_reflect (Finset.mem_Ico.mpr ⟨hj1, hjN⟩)]
  exact hpos _ hja hjb

/-- **`χ*` as a threshold root** of `F_Δ`: an interior zero with `F_Δ < 0` strictly
below it and `F_Δ > 0` strictly above it on `(χ, 1]`. This is the prose meaning of
`χ* = inf{X : F_Δ(X) ≥ 0}` under strict monotonicity, packaged so the floor theorem
can consume it instead of an ad-hoc positivity hypothesis. -/
def IsThresholdRoot (Fdelta : ℝ → ℝ) (chi : ℝ) : Prop :=
  chi ∈ Set.Ioo (0 : ℝ) 1 ∧ Fdelta chi = 0 ∧
    (∀ x, x < chi → Fdelta x < 0) ∧ (∀ x, chi < x → x ≤ 1 → 0 < Fdelta x)

/-- **From the threshold root to the `(χ,½)` positivity hypothesis.** If `χ` is a
threshold root and `χ < ½`, then on `(χ, ½)` both `F_Δ(X)` (as `X > χ`) and
`F_Δ(1−X)` (as `1−X > ½ > χ`) are strictly positive, so the centro-symmetric
pair-sum is strictly positive — exactly the hypothesis `favoredness_sufficient_chistar`
takes. -/
theorem threshold_root_pair_positive (Fdelta : ℝ → ℝ) {chi : ℝ}
    (hRoot : IsThresholdRoot Fdelta chi) :
    ∀ X, chi < X → X < 1 / 2 → 0 < Fdelta X + Fdelta (1 - X) := by
  obtain ⟨hmem, _, _, habove⟩ := hRoot
  intro X hXchi hXhalf
  have h1 : 0 < Fdelta X := habove X hXchi (by linarith)
  have h2 : 0 < Fdelta (1 - X) := habove (1 - X) (by linarith) (by linarith [hmem.1, hXchi])
  linarith

/-- **Explicit `χ*`-floor from a threshold root.** The firmed-up form of the finite
floor: given (C) and the threshold-root structure of `χ`, favoredness holds for every
`N_c > 1/(½ − χ)`. The `(χ,½)`-positivity hypothesis of `favoredness_sufficient_chistar`
is now *discharged* from `IsThresholdRoot`, not assumed ad hoc. -/
theorem favoredness_sufficient_threshold (Fdelta : ℝ → ℝ) (hC : CondC Fdelta)
    {chi : ℝ} (hRoot : IsThresholdRoot Fdelta chi) (hchi : chi < 1 / 2)
    {Nc : ℕ} (hNc : 1 / (1 / 2 - chi) < (Nc : ℝ)) :
    0 < ∑ j ∈ Finset.Ico 1 Nc, Fdelta ((j : ℝ) / Nc) :=
  favoredness_sufficient_chistar Fdelta hC (le_of_lt hRoot.1.1) hchi
    (threshold_root_pair_positive Fdelta hRoot) hNc

/-- **(C) is sufficient for the sharp net-area criterion — and strictly stronger.**
If `F_Δ` is continuous, satisfies (C) on `[0,½]`, and the centro-symmetric sum is
strictly positive at *some* interior point, then `CondNet` holds: the net area is
strictly positive. So (C)'s demand that *every* reflected pair be nonnegative is more
than the basin needs — net positivity is the operative condition. (The converse
fails: `CondNet` can hold with some pairs negative.) -/
theorem condNet_of_condC (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta)
    (hC : CondC Fdelta) {X₀ : ℝ} (hX₀ : X₀ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hstrict : 0 < Fdelta X₀ + Fdelta (1 - X₀)) :
    CondNet Fdelta := by
  unfold CondNet
  have hgc : Continuous (fun X => Fdelta X + Fdelta (1 - X)) :=
    hcont.add (hcont.comp (continuous_const.sub continuous_id))
  have hfi : IntervalIntegrable (fun X => Fdelta X + Fdelta (1 - X))
      MeasureTheory.volume 0 (1 / 2) := hgc.intervalIntegrable 0 (1 / 2)
  have hnn : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (1 / 2))),
      0 ≤ Fdelta x + Fdelta (1 - x) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    filter_upwards with x hx
    exact hC x ⟨le_of_lt hx.1, hx.2⟩
  refine (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnn hfi).mpr
    ⟨by norm_num, ?_⟩
  have hUopen : IsOpen {x : ℝ | 0 < Fdelta x + Fdelta (1 - x)} :=
    isOpen_lt continuous_const hgc
  have hopen2 : IsOpen ({x : ℝ | 0 < Fdelta x + Fdelta (1 - x)} ∩ Set.Ioo (0 : ℝ) (1 / 2)) :=
    hUopen.inter isOpen_Ioo
  have hne : ({x : ℝ | 0 < Fdelta x + Fdelta (1 - x)} ∩ Set.Ioo (0 : ℝ) (1 / 2)).Nonempty :=
    ⟨X₀, hstrict, hX₀⟩
  have hsub : ({x : ℝ | 0 < Fdelta x + Fdelta (1 - x)} ∩ Set.Ioo (0 : ℝ) (1 / 2))
      ⊆ Function.support (fun X => Fdelta X + Fdelta (1 - X)) ∩ Set.Ioc (0 : ℝ) (1 / 2) := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨Function.mem_support.mpr hx1.ne', Set.Ioo_subset_Ioc_self hx2⟩
  exact lt_of_lt_of_le (hopen2.measure_pos MeasureTheory.volume hne)
    (MeasureTheory.measure_mono hsub)

/-- **`CondNet` is literally `0 < ∫₀¹ F_Δ`.** Folding `[½,1]` onto `[0,½]` via the
substitution `X ↦ 1−X` gives `∫₀^{½}(F_Δ(X)+F_Δ(1−X)) = ∫₀¹ F_Δ`. This backs the
claim in the `CondNet` docstring that the net-area criterion is the integral of the
differential. -/
theorem condNet_integral_eq (Fdelta : ℝ → ℝ) (hcont : Continuous Fdelta) :
    (∫ X in (0 : ℝ)..(1 / 2), (Fdelta X + Fdelta (1 - X)))
      = ∫ X in (0 : ℝ)..1, Fdelta X := by
  have hF1 : IntervalIntegrable Fdelta MeasureTheory.volume 0 (1 / 2) :=
    hcont.intervalIntegrable 0 (1 / 2)
  have hF2 : IntervalIntegrable Fdelta MeasureTheory.volume (1 / 2) 1 :=
    hcont.intervalIntegrable (1 / 2) 1
  have hFc : IntervalIntegrable (fun X => Fdelta (1 - X)) MeasureTheory.volume 0 (1 / 2) :=
    (hcont.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 (1 / 2)
  rw [← intervalIntegral.integral_add_adjacent_intervals hF1 hF2,
    intervalIntegral.integral_add hF1 hFc]
  congr 1
  rw [intervalIntegral.integral_comp_sub_left Fdelta 1]
  norm_num

end TwoGenie
