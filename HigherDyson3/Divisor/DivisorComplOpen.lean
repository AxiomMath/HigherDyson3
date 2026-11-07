/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Divisor.DivisorLocallyFinite

/-!
# The complement of the divisor is open

For `0 ≤ α < 1`, the set `(ℍ × ℂ) \ D_x` is open in `ℂ × ℂ`.

## Main results

* `HigherDyson3.divisor_compl_open`: `halfPlaneProd \ divisor α` is open.
-/

public section

noncomputable section

open Complex Metric

namespace HigherDyson3

/-- The closed affine line `{(τ, w) | w = -α + a τ + b}` whose trace on `ℍ × ℂ` is the
component `divisorComponent α a b`. -/
private lemma divisorComplOpen_isClosed_line (α : ℚ) (a b : ℤ) :
    IsClosed {q : ℂ × ℂ | q.2 = -(α : ℂ) + a * q.1 + b} :=
  isClosed_eq continuous_snd (by fun_prop)

/-- **The complement of the divisor is open.** For `0 ≤ α < 1`, the set
`(ℍ × ℂ) \ D_x` is open in `ℂ × ℂ`. -/
theorem divisor_compl_open (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    IsOpen (halfPlaneProd \ divisor α) := by
  have hH : IsOpen halfPlaneProd :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)
  rw [Metric.isOpen_iff]
  rintro p ⟨hpH, hpD⟩
  obtain ⟨ε, hε, hεH⟩ := Metric.isOpen_iff.mp hH p hpH
  set r := ε / 2
  have hr : 0 < r := half_pos hε
  have hBH : closedBall p r ⊆ halfPlaneProd :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεH
  set F := {ab : ℤ × ℤ | (divisorComponent α ab.1 ab.2 ∩ closedBall p r).Nonempty}
  have hF : F.Finite :=
    divisor_locally_finite α hα0 hα1 (isCompact_closedBall p r) hBH
  set V := ball p r ∩ ⋂ ab ∈ F, {q : ℂ × ℂ | q.2 = -(α : ℂ) + ab.1 * q.1 + ab.2}ᶜ
  have hV : IsOpen V :=
    isOpen_ball.inter <| hF.isOpen_biInter fun ab _ =>
      (divisorComplOpen_isClosed_line α ab.1 ab.2).isOpen_compl
  have hpV : p ∈ V := by
    refine ⟨mem_ball_self hr, Set.mem_iInter₂.mpr fun ab _ hq => hpD ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨ab.1, ab.2, hpH, hq⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV p hpV
  refine ⟨min δ r, lt_min hδ hr, fun q hq => ?_⟩
  have hqV : q ∈ V := hδV (ball_subset_ball (min_le_left _ _) hq)
  have hqB : q ∈ closedBall p r :=
    ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hq)
  refine ⟨hBH hqB, fun hqD => ?_⟩
  obtain ⟨a, b, hqL⟩ := Set.mem_iUnion₂.mp hqD
  have hab : ((a, b) : ℤ × ℤ) ∈ F := ⟨q, hqL, hqB⟩
  exact Set.mem_iInter₂.mp hqV.2 (a, b) hab hqL.2

end HigherDyson3
