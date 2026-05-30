import TwoGenie.Priors

/-!
# Capstone: the end-to-end selection theorem

This file composes the verified pieces into the single claim the paper is built
to support, to make precise *what the formalization lets us conclude* with no
`sorry` anywhere in the chain.
-/

namespace TwoGenie

open Finset

/-- **End-to-end selection result.** For a community of `Nc` wishers under the
Moran–Fermi pairwise-comparison dynamic at any selection intensity `β = 1/η_s > 0`:
if the population payoff differential `F_Δ` satisfies the centro-symmetric
condition (C) on the interior grid — every reflected pair-sum non-negative, at
least one strictly positive — then `G2` is strictly ratio-favored over `G1`
(its fixation-probability ratio exceeds 1).

This is `Theorem 5.1 ∘ Proposition 5.2`: the structural hypothesis forces the
cumulative payoff sum positive (`favoredness_sufficient`), which the ratio
identity converts into ratio-favoredness (`ratio_favored_iff`). Nothing here
depends on the Hill specialization or on any deferred lemma. -/
theorem g2_ratio_favored_of_grid
    (Nc : ℕ) (etas : ℝ) (Fdelta : ℝ → ℝ)
    (hNc : 1 ≤ Nc) (hetas : 0 < etas)
    (hpair : ∀ j ∈ Finset.Ico 1 Nc,
        0 ≤ Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc))
    (hstrict : ∃ j ∈ Finset.Ico 1 Nc,
        0 < Fdelta ((j : ℝ) / Nc) + Fdelta (((Nc - j : ℕ) : ℝ) / Nc)) :
    rhoG2G1 Nc etas Fdelta / rhoG1G2 Nc etas Fdelta > 1 :=
  (ratio_favored_iff Nc etas Fdelta hNc hetas).mpr
    (favoredness_sufficient Nc Fdelta hpair hstrict)

/-- **End-to-end selection result over the model `F_Δ`.** Same conclusion as
`g2_ratio_favored_of_grid`, but stated for the *model-defined* differential
`modelFdelta` (eq. F-delta of §5) rather than an abstract `Fdelta`, and with the
non-negativity of every reflected grid pair (`hpair`) **discharged from condition
(C) on the model** via `condC_grid_nonneg`.

So the only remaining hypotheses are: the Moran–Fermi parameters (`Nc ≥ 1`,
`η_s > 0`); condition (C) on the model `F_Δ` (`hC`) — the prior-dependent basin
condition, characterised per family by the §6 frontiers; and a single strictly
positive interior grid pair (`hstrict`) — the mild non-knife-edge clause. Condition
(A) is *not* a hypothesis here: it holds for the model by `modelFdelta_condA`. This
is the closest the formalization comes to the manuscript's headline claim with the
differential tied to the model, not assumed abstractly. -/
theorem g2_ratio_favored_model (P₂ P₁ : ThresholdPrior)
    (Nc : ℕ) (etas uw Bcap Mcap Aa cG2 cG1 : ℝ) (hNc : 1 ≤ Nc) (hetas : 0 < etas)
    (hC : CondC (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1))
    (hstrict : ∃ j ∈ Finset.Ico 1 Nc,
        0 < modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1 ((j : ℝ) / Nc)
          + modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1 (((Nc - j : ℕ) : ℝ) / Nc)) :
    rhoG2G1 Nc etas (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1)
      / rhoG1G2 Nc etas (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1) > 1 :=
  g2_ratio_favored_of_grid Nc etas (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1) hNc hetas
    (fun j hj => condC_grid_nonneg (modelFdelta P₂ P₁ uw Bcap Mcap Aa cG2 cG1) hC j hj)
    hstrict

end TwoGenie
