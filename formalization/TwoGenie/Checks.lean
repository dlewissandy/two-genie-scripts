import TwoGenie

/-!
# Reproducible kernel-honesty check, organized by manuscript section

Run with:  `lake env lean Checks.lean`

Section numbers follow the compiled manuscript:
  §2 The Two Genie Game · §3 Welfare and altruistic utility ·
  §4 Prior-agnostic wisher dynamics · §5 Prior-agnostic community dynamics ·
  §6 Hill-prior specialization · §8 Appendix (technical lemmas).

**Reading the output.**
* `[propext, Classical.choice, Quot.sound]`  →  kernel-verified, no `sorry` in the
  proof or anything it depends on.
* `… sorryAx …`  →  the declaration is asserted, not proved, or depends on one.

**The whole development is `sorry`-free**: every declaration below reports only
`[propext, Classical.choice, Quot.sound]`, including Lemma B.1 (`right_skew_general`)
at general `n>1`. Those three are the standard foundational axioms of Lean/mathlib;
this development introduces **no custom axioms** and contains no `sorry`. (This is
*not* the same as "axiom-free" — no nontrivial Lean development is; the honest claim
is "no `sorry`, no custom axioms, depends only on the standard mathlib foundations.")

**`sorry`-free is not the same as "every manuscript premise is derived," and a
kernel-checked theorem is not the same as its scientific interpretation.** After the
accessibility firm-up, **one** result takes an analytic asymptotic step as an explicit
*hypothesis* rather than deriving it (visible in the signature, not hidden in a `sorry`):
  1. `prop54_log` — Proposition 5.4 takes the Kramers/Laplace asymptotic *form* as a
     hypothesis. The discrete-barrier **rate/log-form** (`fixation_log_rate*`) is
     proved; the `√Nc` prefactor / continuum limit is not (no discrete-Laplace in
     mathlib, and per the reviewer it is deliberately not pursued). So "the rate-form
     consequences of Prop 5.4 are formalized", not "Prop 5.4 was formally verified".

The continuous-`c_depth` bridge is **no longer** an unproven hypothesis:
`riemann_sum_error_lipschitz` proves the Lipschitz Riemann-sum error and
`discrete_barrier_near_cdepth` derives `|log P_k − (Nc/η_s)·c_depth(k/Nc)| ≤ L·k/(η_s·Nc)`
from it — exactly the bound `fixation_log_rate_cdepth` states as `hUpper`/`hLower`.

One condition remains a *hypothesis by the nature of the result*, not a gap: the
model capstone `g2_ratio_favored_model` assumes condition **(C)** on the model `F_Δ`.
(A) is *derived* for the model (`modelFdelta_condA`) and the outer threshold-prior
averaging is *derived* (`sigmabar_eq_integral`); but (C) is the prior-dependent
basin boundary (`modelFdelta_pairsum`), characterised per family by the §6 frontiers,
not universally derivable. The README's status table marks all of this explicitly.

This pass additionally mechanizes, with no `sorry` or custom axiom: the
**Karlin–Taylor fixation probability** `φ_k` (eq. 6) — `ρ_{G2,G1} = φ_1`
(`fixation_one`) and `ρ_{G1,G2} = 1 − φ_{Nc-1}` (`rhoG1G2_eq_one_sub_fixation`) are
now *theorems*, and `φ` is shown to satisfy the absorbing-boundary harmonic recurrence
(`fixation_recurrence`), so it genuinely is the chain's fixation probability rather
than a stipulated closed form; **Lemma B.1 Part (b)** (`right_skew_centro`,
`hillPairSum_monotoneOn`) and the **Regime III** interior-critical-point lemma
(`regimeIII_interior_critical_hill`), both via Hill-density unimodality
(`hillDensity_strictMonoOn`/`_strictAntiOn`); and the model-`F_Δ` (B-high) inequality
(`modelFdelta_condBhigh_iff`) with (Q2) tail continuity (`ThresholdPrior.tail_continuousOn`).
The model-level *accessibility* chain still reads its continuity / Lipschitz /
threshold-root inputs as hypotheses (the model guarantees them on `[0,1]`, whereas the
abstract accessibility lemmas state them globally); this residual is disclosed, like
the `√Nc` deferral, rather than hidden.
-/

open TwoGenie

/-! ## §3 — Welfare and altruistic utility -/
#print axioms audit_scalar_guarantee   -- audit argmin ⇒ λ-weighted welfare ≥ 0
#print axioms inner_lam_welfare         -- ⟪λ, w a⟫ = c(aDN) − c(a)
#print axioms welfare_aDN               -- w(aDN) = 0
#print axioms inner_decomp              -- parallel/perp decomposition identity
#print axioms inner_lam_perp            -- perp component ⟂ λ
#print axioms wagg_cauchy_schwarz       -- Cauchy–Schwarz welfare lift (eq. Wagg-bound)
#print axioms wagg_nonneg               -- downstream sign corollary 0 ≤ W_agg

/-! ## §4 — Prior-agnostic wisher dynamics -/
#print axioms Tmap_affine               -- update is affine in b
#print axioms Tmap_fixed                -- Banach fixed point b*(X;θ) (existence)
#print axioms Tmap_contract             -- |T b − T b'| = |1−L_b|·|b−b'|
#print axioms contract_lt_one           -- contraction under step-size condition
#print axioms fixed_unique              -- Banach fixed point (uniqueness)
#print axioms bstar_eq_cg               -- sharp-threshold reduction b* = c_g
#print axioms bstar_below               -- below threshold (σ=0) ⇒ b* = 0
#print axioms uPercG2_affine            -- perceived utility G2 affine in b
#print axioms uPercG1_affine            -- perceived utility G1 affine in b

/-! ## §5 — Prior-agnostic community dynamics -/

/-! ### §5 Ratio favoredness -/
#print axioms fermi_ratio               -- Fermi detailed-balance ratio
#print axioms switch_rate_ratio         -- eq. (5) switch-rate ratio (prefactors cancel)
#print axioms ratio_identity            -- eq. (7) Karlin–Taylor ratio identity
#print axioms ratio_favored_iff         -- **Theorem 5.1** (within-community ratio-favoredness)
#print axioms log_ratio_identity        -- exact selection rate log(ρ-ratio)

/-! ### §5 Karlin–Taylor fixation `φ_k` (eq. 6), derived rather than assumed -/
#print axioms fixation                  -- φ_k = (Σ_{i<k} P_i)/D (eq. 6)
#print axioms Pprod_zero                 -- P_0 = 1
#print axioms Pprod_succ                 -- P_{i+1} = P_i·α_{i+1}
#print axioms fixation_zero              -- absorbing boundary φ_0 = 0
#print axioms fixation_Nc                -- absorbing boundary φ_{Nc} = 1
#print axioms fixation_one               -- **ρ_{G2,G1} = φ_1** (the 1/D def is a theorem)
#print axioms rhoG1G2_eq_one_sub_fixation -- **ρ_{G1,G2} = 1 − φ_{Nc-1}** (the P_{Nc-1}/D def is a theorem)
#print axioms fixation_recurrence        -- first-step harmonic recurrence T⁺Δφ = T⁻Δφ (φ IS the fixation prob)
#print axioms sampling_symm              -- up/down sampling factors equal (the cancelling prefactor)
#print axioms samplingUp_pos             -- the sampling prefactor is nonzero on interior states

/-! ### §5 Favoredness conditions and Proposition 5.2 -/
#print axioms favoredness_sufficient       -- Prop 5.2, discrete core (strict grid pair as hypothesis)
#print axioms grid_point_in_interval       -- continuous→grid bridge (grid point in any wide interval)
#print axioms condC_grid_nonneg            -- (C) ⇒ all grid pairs ≥ 0 (g(X)=g(1-X) symmetry)
#print axioms favoredness_sufficient_cont  -- **Proposition 5.2, continuous form** (with explicit Nc threshold)
#print axioms favoredness_sufficient_chistar  -- **explicit χ*-floor**: Nc > 1/(½−χ*) ⇒ favored
#print axioms threshold_root_pair_positive    -- χ* threshold-root ⇒ pair-sum > 0 on (χ*,½)
#print axioms favoredness_sufficient_threshold -- floor from IsThresholdRoot (hpos discharged, not assumed)
#print axioms condNet_of_condC             -- (C) ⇒ sharp net-area criterion (C is sufficient, strictly stronger)
#print axioms condNet_integral_eq          -- net-area = ∫₀¹ F_Δ (fold [½,1] onto [0,½])
#print axioms Bhigh_of_C_Blow              -- region nesting (C)+(B-low) ⇒ (B-high)
#print axioms grid_reflect                 -- (Nc−j)/Nc = 1 − j/Nc on the interior grid

/-! ### §5 Lifting Theorem 5.3 -/
#print axioms affine_commute_integral   -- inner affine-commutation layer of **Theorem 5.3** (affine commutes with E)
#print axioms lift_uPercG2              -- exact fast-chain averaging, G2 (inner layer)
#print axioms lift_uPercG1              -- exact fast-chain averaging, G1 (inner layer)
#print axioms sigmabar_eq_integral      -- **outer averaging derived**: σ̄_g = E_θ[c_g·𝟙[X≥θ]]

/-! ### §5 Basin accessibility and Proposition 5.4 -/
#print axioms race_iff                  -- eq. (9) legibility-vs-resource race
#print axioms ledger_monotone           -- cycling rule-out: ledger ↑
#print axioms resource_antitone         -- cycling rule-out: resource ↓
#print axioms cdepth_nonneg             -- barrier height c_depth ≥ 0
#print axioms cdepth_pos                -- barrier height c_depth > 0 (strict, F_Δ<0 on (0,χ*))
#print axioms riemann_sum_error_lipschitz -- **Lipschitz Riemann error** |∫ − (1/Nc)Σ| ≤ L·k/Nc² (finite, no asymptotics)
#print axioms accessibility_sufficient  -- explicit ceiling (with C + log(Nc−1)) ⇒ E[τ] ≤ T·λ_seed
#print axioms leading_ceiling_sufficient -- leading-order ceiling corollary (log(Nc−1) ≤ ε·Nc)
#print axioms log_Pprod                 -- log P_k = discrete barrier exponent
#print axioms fixation_sum_brackets     -- **Prop 5.4 rate form** (two-sided bracket)
#print axioms fixation_log_rate         -- **Prop 5.4 rate form** (discrete-barrier log)
#print axioms fixation_log_rate_cdepth  -- **Prop 5.4 rate form** (continuous c_depth, modulo Riemann bridge)
#print axioms discrete_barrier_near_cdepth -- **#5**: |log P_k − (Nc/η_s)c_depth(k/Nc)| ≤ L·k/(η_s·Nc), DERIVED from Riemann (no bridge hyp)
#print axioms cdepth_le_threshold       -- **#2** running barrier maximized at χ* (variational gap closed)
#print axioms runningDepth_max_at_threshold -- #2 restatement
#print axioms max_logPprod_le_cdepth    -- **#3** ∀ k<Nc, log P_k ≤ (Nc/η_s)c_depth(χ*)+L/η_s (justifies the ceiling)
#print axioms fixation_log_rate_cdepth_le -- **#1** ceiling with NO hUpper: log(Σ) ≤ (Nc/η_s)c_depth(χ*)+L/η_s+log(Nc−1)
#print axioms accessible_and_favored    -- **#8 CAPSTONE**: favored ∧ reachable, no hidden bridges
#print axioms window_nonempty_iff_seed_rate -- **#3** window non-empty ⟺ λ_seed ≥ exp(c_depth·floor/η_s)/T
#print axioms prop54_log                -- **Prop 5.4** log-linearization (Kramers form as hypothesis)
#print axioms cdepth_pos_of_threshold_root -- strict barrier c_depth>0 derived from IsThresholdRoot
#print axioms ledger_hitting_time        -- eq. (8) ledger crossing time τ_Θ = (Θ−L₀)/m

/-! ### §5 Model `F_Δ` and the condition transfer (abstract → model) -/
#print axioms modelFdelta_condA         -- (A) **derived** for the model F_Δ (from σ̄ monotonicity)
#print axioms modelFdelta_condBlow_iff  -- (B-low) ⟺ u_w < B+M (explicit control inequality)
#print axioms modelFdelta_condBhigh_iff -- (B-high) explicit control inequality (symmetric partner of B-low)
#print axioms modelFdelta_one           -- F_Δ(1) = u_w + A σ̄_{G1}(1) − B(1−σ̄_{G2}(1)) − M (eq. lift-B-high)
#print axioms modelFdelta_pairsum       -- (C) reduced to the tail-shape pair-sum
#print axioms modelFdelta_continuousOn  -- F_Δ continuous on [0,1] (from tail (Q2) continuity)
#print axioms ThresholdPrior.tail_continuousOn -- (Q2) tail continuity, derived from the Lipschitz field
#print axioms hill_modelFdelta_condBlow_iff -- Hill instance: (B-low) ⟺ u_w<B+M (tail-0 hyp discharged)
#print axioms g2_ratio_favored_model    -- capstone over the **model** F_Δ ((A) derived, (C) the basin hyp)

/-! ### §5 End-to-end -/
#print axioms g2_ratio_favored_of_grid  -- capstone: (C)-on-grid ⇒ G2 ratio-favored (abstract F_Δ)

/-! ## §6 — Hill-prior specialization -/

/-! ### §6 Prior-shape abstraction (Q1)/(Q2); feeds §5 condition (A) -/
#print axioms sigmabar_monotone         -- σ̄_g non-decreasing (source of condition (A))

/-! ### §6 Hill tail and regimes -/
#print axioms hillTail_zero             -- h(0) = 1
#print axioms hillTail_one              -- h(1) = σ
#print axioms hillTail_nonneg
#print axioms hillTail_le_one
#print axioms hillTail_antitoneOn       -- (Q2a) tail monotone non-increasing
#print axioms regimeIII_interior_critical -- Regime III interior critical point (IVT)
#print axioms frontier_T1_iff           -- frontier (T1) algebra
#print axioms frontier_T2_iff           -- frontier (T2) algebra
#print axioms frontier_T3_iff           -- frontier (T3) algebra
#print axioms piBind_nonneg_T1          -- π_bind≥0 ⟺ (T1), at the small-K corner W_max
#print axioms piBind_nonneg_T2          -- π_bind≥0 ⟺ (T2), at the K_{G2}→∞,K_{G1}→0 corner W_max
#print axioms piBind_nonneg_T3          -- π_bind≥0 ⟺ (T3), at the K_{G1}→∞,K_{G2}→0 corner W_max
#print axioms hillTail_hasDeriv         -- (Q1) h' = −f  [rpow const-power + quotient rule]
#print axioms hillTail_lipschitz        -- (Q2b) Lipschitz constant n/Kⁿ  [MVT, proved]
#print axioms hillPrior                 -- Hill `ThresholdPrior` instance (fully certified)
#print axioms hillDensity_two           -- φ at n=2 in elementary form
#print axioms right_skew_two            -- **Lemma B.1, n=2 case** (operative cooperativity), proved

/-! ### §6/§5 — (Q1): every prior density integrates to 1 (improper FTC, all families) -/
#print axioms prior_density_integral    -- uniform: ∫ density = F̄(left endpoint) = 1
#print axioms hill_integral_eq_one      -- **(Q1) Hill**: ∫₀^∞ φ = 1
#print axioms lomax_integral_eq_one     -- **(Q1) Lomax**: ∫₀^∞ φ = 1
#print axioms pareto_integral_eq_one    -- **(Q1) Pareto**: ∫_{xm}^∞ φ = 1
#print axioms frechet_integral_eq_one   -- **(Q1) Fréchet**: ∫₀^∞ φ = 1

/-! ### §6 Robustness — a menu of alternative long-tailed `ThresholdPrior` instances

Beyond Hill, four further long-tailed priors are discharged so the prior-agnostic
results of §4–§5 visibly do not depend on the Hill functional form: Pareto Type I,
Lomax (Pareto Type II), Fréchet (extreme-value Type II), and log-logistic (= Hill). -/
#print axioms paretoTail_antitoneOn     -- Pareto Type I (Q2a) monotone tail
#print axioms paretoTail_lipschitz      -- Pareto Type I (Q2b) Lipschitz, constant α/xm
#print axioms paretoPrior               -- Pareto `ThresholdPrior` instance (fully certified)
#print axioms paretoTail_zero           -- Pareto (Q3) endpoint F̄(0)=1
#print axioms paretoTail_one            -- Pareto (Q4) endpoint F̄(1)=1 (xm≥1) or xmᵅ

/-! #### Lomax (Pareto Type II): heavy polynomial tail, monotone density -/
#print axioms lomaxTail_zero            -- (Q3) F̄(0)=1
#print axioms lomaxTail_one             -- (Q4) F̄(1)=(1+1/λ)^(−α)
#print axioms lomaxTail_antitoneOn      -- (Q2a) monotone tail (source of condition (A))
#print axioms lomaxTail_lipschitz       -- (Q2b) Lipschitz, constant α/λ
#print axioms lomaxPrior                -- Lomax `ThresholdPrior` instance (fully certified)
#print axioms lomaxPairSum_antitoneOn   -- (Q5) pair-sum max at X=0 (monotone-density direction)
#print axioms paretoPairSum_le_at_threshold -- (Q5) Pareto: pair-sum max at the threshold X=xm

/-! #### Fréchet (extreme-value Type II): heavy tail, unimodal density, different family -/
#print axioms rpow_mul_exp_neg_le       -- t^c·e^{−t} ≤ c^c·e^{−c} (density-mode bound, from log u ≤ u−1)
#print axioms frechetTail_zero          -- (Q3) F̄(0)=1
#print axioms frechetTail_one           -- (Q4) F̄(1)=1−e^{−sᵅ}
#print axioms frechetTail_antitoneOn    -- (Q2a) monotone tail
#print axioms frechetCore_hasDerivAt    -- density via the exp∘rpow chain rule
#print axioms frechetCore_deriv_abs_le  -- (Q2b core) density bounded by its mode value
#print axioms frechetTail_lipschitz     -- (Q2b) Lipschitz on [0,1] (interior bound + continuity at 0)
#print axioms frechetPrior              -- Fréchet `ThresholdPrior` instance (fully certified)
-- Fréchet (Q5): unimodality, right-skew, and both regimes (full §5 treatment)
#print axioms frechetDensity_strictMonoOn -- density rises on (0,χ*_F]
#print axioms frechetDensity_strictAntiOn -- density falls on [χ*_F,∞)
#print axioms frechetDensity_right_skew -- φ(χ*_F−δ) < φ(χ*_F+δ) (right-skew at the peak)
#print axioms frechetPairSum_monotoneOn -- **Regime II** (χ*_F≥½): pair-sum max at ½
#print axioms regimeIII_interior_critical_frechet -- **Regime III** (χ*_F<½): interior critical point

/-! #### Log-logistic (Fisk) = the Hill prior under its standard name -/
#print axioms hillTail_eq_logLogistic   -- Kⁿ/(Kⁿ+Xⁿ) = 1/(1+(X/K)ⁿ)
#print axioms logLogisticPrior          -- log-logistic `ThresholdPrior` (definitionally Hill)

/-! ### §8 — Lemma B.1 (right-skew of the Hill density), now fully proved -/
#print axioms hasDerivAt_Hfn            -- H'(t) = Hp(t)  (the crux derivative identity)
#print axioms Hfn_pos                   -- H(t) > 0 on (0,1)
#print axioms fp_eq                     -- f'(t) = 2(n²−1)H / [(1−t²)·A·B]
#print axioms Ffn_pos                   -- f(t) > 0 on (0,1)
#print axioms right_skew_two            -- Lemma B.1, n=2 (direct polynomial proof)
#print axioms right_skew_general        -- **Lemma B.1(a), general n>1** — no `sorry`

/-! ### §8 — Hill density unimodality, Lemma B.1 **Part (b)**, and Regime III
The density derivative and its sign give unimodality (`φ↑` on `[0,χ*]`, `φ↓` after),
from which Part (b) and the Regime III sign facts are derived (not assumed). -/
#print axioms hillDensity_hasDerivAt    -- φ'(X) = nKⁿX^{n-2}((n-1)Kⁿ-(n+1)Xⁿ)/(Kⁿ+Xⁿ)³
#print axioms hillDensity_continuousOn  -- φ continuous on any set of nonneg reals
#print axioms hillTail_continuousOn     -- h continuous on any set of nonneg reals
#print axioms hillDensity_strictMonoOn  -- **unimodality, rising**: φ strictly ↑ on [0,χ*]
#print axioms hillDensity_strictAntiOn  -- **unimodality, falling**: φ strictly ↓ on [χ*,∞)
#print axioms right_skew_centro         -- **Lemma B.1(b)**: φ(X) ≤ φ(1-X) on [0,½] under χ*≥½
#print axioms hillPairSum_monotoneOn    -- **Lemma B.1(b)**: g(X)=h(X)+h(1-X) non-decreasing on [0,½]
#print axioms regimeIII_interior_critical_hill -- **Regime III, Hill**: sign facts derived, IVT applied
#print axioms half_le_chistar_iff       -- χ* ≥ ½ ⟺ K ≥ K*(n) (the Regime II boundary in K)
