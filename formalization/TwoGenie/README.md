# TwoGenie — a literate Lean 4 formalization

A mechanically-verified rendering of the mathematics in
*Accessibility and Favorability of Cooperative Basins in the Two Genie Game*
(Darrell Lewis-Sandy). Theorems are typed propositions; proofs are Lean terms
checked by the kernel. This is the "fifth artifact form" of the formalization
plan: the paper *is* the verified artifact.

The four-axis Jain harm taxonomy is treated as one instance of a `d`-dimensional
theory (the welfare layer is stated over an arbitrary real inner-product space),
answering the plan's Open Question 1: **none of the deductive results depend on
`d = 4`.** The Jain case is recorded as `jainHarmSpace := EuclideanSpace ℝ (Fin 4)`.

## What is verified

**The formalization is `sorry`-free.** Every result below — and everything it
depends on — is checked by the Lean kernel against only the three standard
mathlib axioms `[propext, Classical.choice, Quot.sound]`. This is proven, not
asserted: `Checks.lean` prints the axiom dependency of every headline result
(see the bottom of this file), `lake build` reports no `sorry` warnings, and CI
([`.github/workflows/lean.yml`](../../.github/workflows/lean.yml)) fails the build
if any declaration reports `sorryAx`.

A word on what that means precisely. Those three are the standard foundational
axioms of Lean/mathlib; this development introduces **no custom axioms** and
contains no `sorry`. It is *not* "axiom-free" — no nontrivial Lean development is.
The honest phrasing is: **no `sorry`, no custom axioms, depends only on standard
Lean/mathlib foundations.** And a kernel-checked theorem is not the same as its
*scientific interpretation*: the kernel certifies that each proof is valid for the
proposition as written, not that the proposition faithfully captures the manuscript's
intent (see *Honest caveats* and the modeling-fidelity note).

`sorry`-free is also **not** the same as "every manuscript premise is derived."
The status column separates the two:

* **✅ — kernel-verified from first principles.** Proved outright; the only
  inputs are mathlib's axioms.
* **🔶 — kernel-verified *conditional on a stated analytic hypothesis*.** The
  theorem is proved, but it takes one analytic step as an explicit hypothesis in
  its signature (no `sorry`, no hidden assumption — the premise is visible in the
  type) rather than deriving it. The three 🔶 rows are exactly the assumed-vs-
  verified boundary; each is explained under *Honest caveats* below.

### Headline results: manuscript claim → Lean (at a glance)

The five load-bearing results, with mechanization status stated bluntly. "Fully
mechanized" = proved from first principles; "Assumption-level" = some step enters as
an explicit hypothesis in the signature.

| Manuscript claim | Lean theorem | Fully mechanized? | Assumption-level? | Notes |
|---|---|---|---|---|
| **Thm 5.1** (`thm:ratio-favored`): ρ-ratio > 1 ⟺ ΣF_Δ(j/N_c) > 0 | `ratio_favored_iff`, `fixation_recurrence` | **Yes** | No | Karlin–Taylor identity; the fixation probability `φ_k` (eq. 6) and its absorbing-boundary recurrence are mechanized, so `ρ_{G2,G1}=φ_1`, `ρ_{G1,G2}=1−φ_{N_c−1}` are **derived**, not stipulated. |
| **Prop 5.2** (`prop:favoredness-sufficient`): (A)+(B)+(C) ⇒ Σ > 0 above an N_c threshold | `favoredness_sufficient`, `favoredness_sufficient_cont`, `favoredness_sufficient_chistar` | **Yes** | No | Continuous→grid bridge proved; explicit floor `N_c > 1/(½−χ*)` (`χ*`-form) or `⌊1/(2δ)⌋+1`. |
| **Thm 5.3** (`thm:abc-preserved`): conditions transfer through averaging | `affine_commute_integral`, `lift_uPercG1/2`, `sigmabar_eq_integral`, `modelFdelta_condA`, `modelFdelta_condBhigh_iff` | **Partial** | **Partial** | Inner affine-commute + outer averaging derived; (A) derived for the model; (B-low) and (B-high) both explicit; **(C) stays a hypothesis** (the basin). |
| **Prop 5.4** (`prop:basin-depth`): E[τ_fix] ∼ √N_c·exp(c_depth·N_c/η_s) | `fixation_log_rate_cdepth_le`, `accessible_and_favored`, `prop54_log` | **No** (rate/log-form only) | **only √N_c** | Discrete-barrier rate **and** the quasi-potential bridge are proved (`cdepth_le_threshold` + `riemann_sum_error_lipschitz`); only the √N_c Kramers prefactor (`prop54_log`) is assumed — and it is **not** used in the proved accessibility chain. |
| **Lemma B.1** (`lem:right-skew`) + **Regime III** (`lem:regime-iii-critical`): Hill density right-skew, centro-symmetric monotonicity, interior critical point | `right_skew_general`, `right_skew_two`, `right_skew_centro`, `regimeIII_interior_critical_hill` | **Yes** | No | Part (a) by the `H(t)/H'(t)` construction; **part (b)** and the Regime III sign facts derived from Hill-density **unimodality** (`hillDensity_strictMonoOn`/`_strictAntiOn`). |

The detailed per-declaration table follows.

| Manuscript result | Lean name | Status |
|---|---|---|
| §3 audit scalar guarantee `λ·w(a*) ≥ 0` | `audit_scalar_guarantee` | ✅ |
| §3 Cauchy–Schwarz welfare lift (eq. Wagg-bound) | `wagg_cauchy_schwarz` | ✅ |
| §3 sign corollary `0 ≤ W_agg` | `wagg_nonneg` | ✅ |
| §4 Banach fixed point `b*(X;θ)` (existence + uniqueness) | `Tmap_fixed`, `fixed_unique` | ✅ |
| §4 sharp-threshold reduction `b* = c_g` | `bstar_eq_cg` | ✅ |
| §5 Fermi ratio / switch-rate eq. (5) | `fermi_ratio`, `switch_rate_ratio` | ✅ |
| §5 Karlin–Taylor **ratio identity, eq. (7)** | `ratio_identity` | ✅ |
| §5 **Theorem 5.1** (within-community ratio-favoredness) | `ratio_favored_iff` | ✅ |
| §5 **Karlin–Taylor fixation `φ_k`** (eq. 6), boundaries `φ_0=0`, `φ_{N_c}=1` | `fixation`, `fixation_zero`, `fixation_Nc` | ✅ |
| §5 **`ρ_{G2,G1}=φ_1`, `ρ_{G1,G2}=1−φ_{N_c−1}`** (the `1/D`, `P_{N_c−1}/D` defs are theorems) | `fixation_one`, `rhoG1G2_eq_one_sub_fixation` | ✅ |
| §5 **fixation harmonic recurrence** `T⁺Δφ = T⁻Δφ` (φ *is* the chain's fixation prob.) | `fixation_recurrence` | ✅ |
| §5 Moran–Fermi **shared sampling prefactor** (up = down, cancels) | `sampling_symm`, `samplingUp_pos` | ✅ |
| §5 **Proposition 5.2**, discrete core (strict grid pair as hypothesis) | `favoredness_sufficient` | ✅ |
| §5 **Proposition 5.2**, continuous form + explicit `N_c` threshold | `favoredness_sufficient_cont` | ✅ |
| §5 **Cor.** explicit `χ*`-floor `N_c > 1/(½−χ*)` ⇒ favored | `favoredness_sufficient_chistar` | ✅ |
| §5 region nesting (`π_bind>0 ⇒ π_high>0`) | `Bhigh_of_C_Blow` | ✅ |
| §5 **Lifting Theorem 5.3** inner layer (affine commute over fast chain) | `affine_commute_integral`, `lift_uPercG1/2` | ✅ |
| §5 **Lifting Theorem 5.3** outer layer (`σ̄_g = E_θ[c_g·𝟙[X≥θ]]`, derived) | `sigmabar_eq_integral` | ✅ |
| §5 model `F_Δ := Ū_{G2}−Ū_{G1}` defined from primitives (eq. F-Δ) | `modelFdelta` | ✅ |
| §5 condition (A) **derived for the model** `F_Δ` (from σ̄ monotonicity) | `modelFdelta_condA` | ✅ |
| §5 condition (B-low) for the model `⟺ u_w < B+M` (control inequality) | `modelFdelta_condBlow_iff` | ✅ |
| §5 condition (B-high) for the model (explicit, symmetric partner of B-low) | `modelFdelta_condBhigh_iff`, `modelFdelta_one` | ✅ |
| §5 model `F_Δ` **continuous on `[0,1]`**; threshold-prior **(Q2) tail continuity** | `modelFdelta_continuousOn`, `ThresholdPrior.tail_continuousOn` | ✅ |
| §5 Hill instance: model (B-low) `⟺ u_w<B+M` (tail-0 hypothesis discharged) | `hill_modelFdelta_condBlow_iff` | ✅ |
| §5 condition (C) for the model reduced to the tail-shape pair-sum | `modelFdelta_pairsum` | ✅ |
| §5 end-to-end capstone, **abstract** `F_Δ` ((C)-on-grid ⇒ `G₂` favored) | `g2_ratio_favored_of_grid` | ✅ |
| §5 end-to-end capstone, **model** `F_Δ` ((A) derived, (C) = basin hyp.) | `g2_ratio_favored_model` | ✅ |
| §4.2 legibility-vs-resource race, eq. (9) | `race_iff` | ✅ |
| §4.2 cycling rule-out (monotone slow plane) | `ledger_monotone`, `resource_antitone` | ✅ |
| §4.2 barrier height `c_depth ≥ 0`; **`c_depth > 0`** (strict) | `cdepth_nonneg`, `cdepth_pos` | ✅ |
| §4.2 strict barrier `c_depth>0` **from the threshold root** (no extra hypothesis) | `cdepth_pos_of_threshold_root` | ✅ |
| §4.2 **ledger hitting time eq. (8)** `τ_Θ=(Θ−L₀)/m` (the race closed form) | `ledger_hitting_time` | ✅ |
| §4.2 **Proposition 5.4** discrete-barrier rate (unconditional) | `fixation_sum_brackets`, `fixation_log_rate` | ✅ |
| §4.2 **Lipschitz Riemann-sum error** `\|∫ − (1/N_c)Σ\| ≤ L·k/N_c²` | `riemann_sum_error_lipschitz` | ✅ |
| §4.2 **discrete barrier ≈ continuous** `\|log P_k − (N_c/η_s)c_depth(k/N_c)\| ≤ L·k/(η_s N_c)` | `discrete_barrier_near_cdepth` | ✅ |
| §4.2 **running barrier maximized at `χ*`** (variational gap closed) | `cdepth_le_threshold`, `runningDepth_max_at_threshold` | ✅ |
| §4.2 **max-`k` barrier bound** `log P_k ≤ (N_c/η_s)c_depth(χ*)+L/η_s` (all `k`) | `max_logPprod_le_cdepth` | ✅ |
| §4.2 **ceiling, NO bridge hypothesis** `log(Σ P_k) ≤ (N_c/η_s)c_depth(χ*)+L/η_s+log(N_c−1)` | `fixation_log_rate_cdepth_le` | ✅ |
| §4.2 **accessibility capstone** (favored ∧ reachable, no hidden bridges) | `accessible_and_favored` | ✅ |
| §4.2 (superseded) conditional cdepth-rate stating `hUpper`/`hLower` | `fixation_log_rate_cdepth` | ✅ |
| §4.2 explicit accessibility ceiling + leading-order corollary | `accessibility_sufficient`, `leading_ceiling_sufficient` | ✅ |
| §4.2 seed-rate floor ⟺ non-empty window | `window_nonempty_iff_seed_rate` | ✅ |
| §4.2 Prop 5.4 log-linearization eq. (10) (**only** the `√N_c` prefactor assumed) | `prop54_log` | 🔶 |
| §6 (Q2a) Hill tail monotone non-increasing | `hillTail_antitoneOn` | ✅ |
| §6 (Q2b) Hill tail Lipschitz, constant `n/Kⁿ` | `hillTail_lipschitz` | ✅ |
| §6 (Q1) Hill `h' = -f` (rpow calculus) | `hillTail_hasDeriv` | ✅ |
| §6 endpoints, regimes, frontier (T1)/(T2)/(T3) algebra | `hillTail_zero/one`, `regimeIII_interior_critical`, `frontier_T1/2/3_iff` | ✅ |
| §6/§B **Hill density derivative** `φ'(X) = nKⁿX^{n−2}((n−1)Kⁿ−(n+1)Xⁿ)/(Kⁿ+Xⁿ)³` | `hillDensity_hasDerivAt` | ✅ |
| §6/§B **Hill density unimodality**: `φ` strictly ↑ on `[0,χ*]`, strictly ↓ on `[χ*,∞)` | `hillDensity_strictMonoOn`, `hillDensity_strictAntiOn` | ✅ |
| §B **Lemma B.1 part (b)**: `φ(X) ≤ φ(1−X)` on `[0,½]`; `g=h(X)+h(1−X)` ↑ on `[0,½]` (under `χ*≥½`) | `right_skew_centro`, `hillPairSum_monotoneOn` | ✅ |
| §B **Regime III** (`lem:regime-iii-critical`), Hill: interior critical point, sign facts derived | `regimeIII_interior_critical_hill` | ✅ |
| §6 Regime II boundary `χ* ≥ ½ ⟺ K ≥ K*(n)` | `half_le_chistar_iff` | ✅ |
| §6 Hill `ThresholdPrior` instance (fully certified) | `hillPrior` | ✅ |
| §6 **Pareto Type I** `ThresholdPrior` instance (robustness) | `paretoTail_antitoneOn`, `paretoTail_lipschitz`, `paretoPrior` | ✅ |
| §6 Pareto **endpoints** (Q3)/(Q4) `F̄(0)=1`, `F̄(1)` | `paretoTail_zero`, `paretoTail_one` | ✅ |
| §6 **Lomax (Pareto II)** `ThresholdPrior` (heavy poly tail, monotone density) | `lomaxPrior`, `lomaxTail_lipschitz`, `lomaxTail_zero/one` | ✅ |
| §6 Lomax (Q5) pair-sum max at `X=0` (monotone-density direction) | `lomaxPairSum_antitoneOn` | ✅ |
| §6 **Fréchet (extreme-value II)** `ThresholdPrior` (heavy tail, unimodal, different family) | `frechetPrior`, `frechetTail_lipschitz`, `frechetTail_zero/one` | ✅ |
| §6 Fréchet density-mode bound `t^c e^{−t} ≤ c^c e^{−c}` (the (Q2b) crux) | `frechetCore_deriv_abs_le`, `rpow_mul_exp_neg_le` | ✅ |
| §6 Fréchet **(Q5) unimodality**: density rises on `(0,χ*_F]`, falls on `[χ*_F,∞)` | `frechetDensity_strictMonoOn`, `frechetDensity_strictAntiOn` | ✅ |
| §6 Fréchet **(Q5) right-skew** `φ(χ*_F−δ) < φ(χ*_F+δ)` (convexity-based, all `α>0`) | `frechetDensity_right_skew`, `frechet_skewH_pos` | ✅ |
| §6 Fréchet **(Q5) Regime II** (`χ*_F≥½`, max at ½) / **Regime III** (`χ*_F<½`, interior critical) | `frechetPairSum_monotoneOn`, `regimeIII_interior_critical_frechet` | ✅ |
| §6 Pareto **(Q5)** pair-sum max at the threshold `X=xm` | `paretoPairSum_le_at_threshold` | ✅ |
| §5/§6 **(Q1)** every prior density integrates to 1 (improper FTC, uniform) | `prior_density_integral`, `hill_integral_eq_one`, `lomax_integral_eq_one`, `pareto_integral_eq_one`, `frechet_integral_eq_one` | ✅ |
| §6 **Log-logistic (Fisk)** = Hill: `Kⁿ/(Kⁿ+Xⁿ)=1/(1+(X/K)ⁿ)`; named prior | `hillTail_eq_logLogistic`, `logLogisticPrior` | ✅ |
| §B **Lemma B.1** right-skew of Hill density, **general `n>1`** | `right_skew_general` | ✅ |
| §B Lemma B.1, `n=2` (direct polynomial proof) | `right_skew_two` | ✅ |

The general-`n` Lemma B.1 (`Priors/RightSkew.lean`) is the full Freidlin-style
construction: the derivative identity `H'(t) = n(n+1)t[(1+t)^{n-1}+(1-t)^{n-1}] +
2n(n-1)t(1-t²)^{n-1}` (`hasDerivAt_Hfn`), `H>0` from `H(0)=0` + `H'>0`
(`Hfn_pos`), the `f'(t) = 2(n²−1)H/[(1−t²)AB]` identity (`fp_eq`) giving `f>0`
(`Ffn_pos`), and the density reduction through `(χ*)^n = K^n(n-1)/(n+1)`
(`chi_pow`, `hd_chi`).

Proposition 5.2 has **two** verified forms. The discrete core
(`favoredness_sufficient`) takes a single strictly-positive interior grid pair as
hypothesis and pairs the grid by reflection. The continuous form
(`favoredness_sufficient_cont`) removes that hypothesis: from condition (C) plus a
*continuous* `F_Δ` with one strict interior point `0 < F_Δ(X₀)+F_Δ(1−X₀)`, it
derives an **explicit** community-size threshold `N₀ = ⌊1/(2δ)⌋+1` above which the
grid sum is strictly positive. The bridge is `grid_point_in_interval` (every
interval of grid-width `>1` contains an interior grid node) and `condC_grid_nonneg`
((C) makes every grid pair `≥ 0` via the `g(X)=g(1−X)` symmetry). This closes the
previous "depends on an infinite `N_c`" gap with a finite, computed bound.

## Honest caveats (not `sorry` — visible hypotheses and scope)

The artifact has no `sorry`. After the accessibility firm-up, **only one** 🔶 result
remains (the `√N_c` prefactor); the rest of the accessibility chain is now finite and
derived. A few items are scope/structuring choices worth stating plainly:

* **Prop 5.4, exact prefactor (the one remaining 🔶).** The *rate* `c_depth·N_c/η_s`
  is proved unconditionally and finitely (`fixation_log_rate`: the fixation sum is
  bracketed between its largest term and `(N_c−1)×` it, so `log = barrier exponent +
  O(log N_c)`). The exact `√N_c` Laplace prefactor is **not** derived — `prop54_log`
  takes the Kramers form `E[τ] = c·√N_c·exp(c_depth·N_c/η_s)` as a hypothesis. mathlib
  has no discrete-Laplace method; this is the plan's stated fallback, a visible
  hypothesis rather than a hidden `sorry`. (Per the reviewer, this prefactor is
  deliberately *not* pursued — the paper needs only the exponential barrier ceiling.)
* **Prop 5.4, continuous `c_depth` — bridge fully eliminated.** The old
  `fixation_log_rate_cdepth` took `hUpper`/`hLower` as hypotheses; that bridge is now
  *proved away*. The chain: `riemann_sum_error_lipschitz` (Lipschitz Riemann error
  `|∫ − (1/N_c)Σ| ≤ L·k/N_c²`) → `discrete_barrier_near_cdepth` (`|log P_k −
  (N_c/η_s)·c_depth(k/N_c)| ≤ L·k/(η_s N_c)`) → `cdepth_le_threshold` (the running
  barrier is maximized at `χ*` — the variational gap) → `max_logPprod_le_cdepth`
  (`log P_k ≤ (N_c/η_s)·c_depth(χ*) + L/η_s` for **all** `k`) →
  **`fixation_log_rate_cdepth_le`**, the ceiling `log(Σ P_k) ≤ (N_c/η_s)·c_depth(χ*) +
  L/η_s + log(N_c−1)` with **no bridge hypothesis at all**. `cdepth_pos` gives strict
  `c_depth > 0`. The clean linear ceiling (`leading_ceiling_sufficient`) and the
  exponential seed-rate (`window_nonempty_iff_seed_rate`) survive only as *leading-order*
  corollaries. The single inspectable operational claim is the capstone
  **`accessible_and_favored`**: concrete hypotheses (continuity, (C), Lipschitz, the
  `χ*` threshold-root, the size floor, the seed budget) ⟹ favored ∧ reachable, with the
  `√N_c` Kramers prefactor **not used anywhere in the proved chain**.
* **Lifting Theorem 5.3 and the condition transfer — now tied to the model.** The
  abstract `F_Δ` is no longer a free-floating `ℝ → ℝ`: `modelFdelta` *defines* it from
  the primitives (eq. F-Δ), and the conditions are discharged on it to the extent
  each is model-intrinsic. Proved: the affine-commute inner layer
  (`affine_commute_integral`, `lift_uPercG1/2`); the outer averaging
  `σ̄_g = E_θ[c_g·𝟙[X≥θ]]` (`sigmabar_eq_integral`); condition **(A)**, *derived*
  for the model with no parameter hypothesis (`modelFdelta_condA`); condition
  **(B-low)** reduced to the explicit control inequality `u_w < B+M`
  (`modelFdelta_condBlow_iff`); and the end-to-end result *over the model* `F_Δ`
  (`g2_ratio_favored_model`). What remains a **hypothesis** — correctly, not as an
  omission — is condition **(C)** on the model. `modelFdelta_pairsum` shows the
  centro-symmetric pair-sum is `2(u_w−B−M) + (B·c_{G2}+A·c_{G1})(2−F̄(X)−F̄(1−X))`;
  since (B-low) forces `u_w−B−M < 0`, (C) is a *prior-dependent shape* condition (the
  prior's growth must dominate near the centre), not a sign condition. That is the
  basin boundary itself — characterised per family by the §6 frontiers — so it
  enters the capstone as a hypothesis by the nature of the result, not for lack of a
  proof. What is genuinely *not* formalized: a closed-form characterisation of the
  (C) basin for an arbitrary `ThresholdPrior` (the §6 Hill/Pareto frontiers do this
  per family).
* **Cauchy–Schwarz lift is a verified island.** `wagg_cauchy_schwarz`/`wagg_nonneg`
  are correct and kernel-checked, but *no other declaration consumes them* — the
  type-checker confirms the manuscript reviewer's "decorative" charge. Giving the
  lift a quantitative `θλ`-robustness margin (so the basin's shrinkage in `θλ`
  becomes load-bearing) is the way to retire that finding; not yet done.
* **Accessibility is three results, not one.** `race_iff`, the cycling rule-out,
  and the fixation-rate bounds are each proved but not assembled into a single
  "fixation completes within tenure iff …" theorem. A structuring gap, not a
  correctness gap.
* **Modeling fidelity is yours to check.** The kernel certifies the *deduction*,
  not that the Lean statements faithfully transcribe the manuscript's intent — in
  particular that `Hfn`/`Hp`/`Ffn` match the paper's `H(t)`, `f(t)`, and that the
  structural conditions encode (A)/(B)/(C) as written. The table maps each Lean
  name to its manuscript result to make that audit tractable.

## Build

Requires no global toolchain: `elan` lives in a project-local `ELAN_HOME` under
`../.elan` (see `../setup.sh`). From this directory:

```sh
export ELAN_HOME="$(cd .. && pwd)/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
lake exe cache get          # one-time: download compiled mathlib oleans
lake build                  # builds all modules (no `sorry` warnings)
lake env lean Checks.lean   # prints the per-theorem axiom dependencies
```

## Provenance

* Lean toolchain: `leanprover/lean4:v4.29.0`
* mathlib: `v4.29.0` @ `8a178386ffc0` (the dependency against which proofs check)
* batteries `756e3321fd3b`, aesop `7152850e7b21`
* **No dependency on CSLib.** The plan placed CSLib in scope for Prop 5.4's
  Laplace asymptotic; here the rate is proved on mathlib alone and the exact
  prefactor is a visible hypothesis, so mathlib suffices.
* AI assistance: the Lean proof terms were developed with Claude (Anthropic). The
  kernel — not the assistant — certifies correctness; the disclosure is about
  provenance of effort, not of correctness.

## Reading guide (literate order)

`Primitives → PerWisher → Community → Structural → Lifting → Priors → Priors/Hill
→ Priors/Pareto → Priors/RightSkew → Accessibility → Capstone`. Each file opens
with a docstring tying its declarations to the manuscript's equations; read those
top-to-bottom for the prose-and-code interleave. The §1 village allegory and §7
discussion remain prose in the manuscript; the normative "interventions" framing
of §7 does not formalize and is not reproduced.

## Phase 4 — computational artifacts

`scripts/phase_diagram.py` (Hill) and `scripts/phase_diagram_pareto.py` (Pareto)
reproduce the §6 phase diagrams from the *same* basin-certificate formulas
verified in `Priors/Hill.lean` / `Priors/Pareto.lean` (`piLow`, `piHigh`,
`piBind`, and the kernel-checked tails). mathlib's `Real.rpow` is noncomputable,
so the float evaluation lives in Python (the plan's Phase-4 split); the Lean side
certifies the structure. Run inside the project uv venv:

```sh
source ../.venv/bin/activate
python scripts/phase_diagram.py          # figures/phase_diagram.{png,csv}
python scripts/phase_diagram_pareto.py   # figures/phase_diagram_pareto_*.{png,csv}
```

## `Checks.lean` output (kernel-honesty evidence)

Every checked declaration reports only the three standard mathlib axioms; **none
reports `sorryAx`.** A representative slice:

```
'TwoGenie.ratio_favored_iff'           depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGenie.favoredness_sufficient_cont' depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGenie.sigmabar_eq_integral'        depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGenie.modelFdelta_condA'           depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGenie.g2_ratio_favored_model'      depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGenie.hillTail_lipschitz'          depends on axioms: [propext, Classical.choice, Quot.sound]
'TwoGenie.right_skew_general'          depends on axioms: [propext, Classical.choice, Quot.sound]
```
