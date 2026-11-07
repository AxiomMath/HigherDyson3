/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Divisor.DivisorLocallyFinite

/-!
# The neighbourhood of one divisor component is open

For `a, b ∈ ℤ`, the set `Ω_{a,b} = (ℍ × ℂ) \ ⋃_{(c, d) ≠ (a, b)} L_{c,d}` is open in `ℂ × ℂ`.
Around a point `p ∈ Ω_{a,b}` take a closed ball `B ⊆ ℍ × ℂ`; it is compact, so by local
finiteness only finitely many components `L_{c,d}` meet it. Removing from the open ball the
finitely many closed lines `w = -α + c τ + d` through those components (none of which contains
`p`) leaves an open neighbourhood of `p` inside `Ω_{a,b}`.

## Main results

* `HigherDyson3.divisorNbhd_isOpen`: `divisorNbhd α a b` is open.
-/

public section

noncomputable section

open Complex Metric

namespace HigherDyson3

/-- The closed ball around a point `p` of `ℍ × ℂ` of radius `Im p.1 / 2` lies in `ℍ × ℂ`. -/
private lemma divisorNbhdOpen_ball_subset {p : ℂ × ℂ} (hp : 0 < p.1.im) :
    closedBall p (p.1.im / 2) ⊆ halfPlaneProd := by
  intro q hq
  have h1 : dist q.1 p.1 ≤ p.1.im / 2 := by
    have := mem_closedBall.mp hq
    rw [Prod.dist_eq] at this
    exact (le_max_left _ _).trans this
  have h2 : |(q.1 - p.1).im| ≤ dist q.1 p.1 := by
    rw [dist_eq_norm]
    exact abs_im_le_norm _
  have h3 := (abs_le.mp (h2.trans h1)).1
  change 0 < q.1.im
  simp only [sub_im] at h3
  linarith

/-- **The neighbourhood of one component is open.** For `a, b ∈ ℤ`, the set
`Ω_{a,b} = (ℍ × ℂ) \ ⋃_{(c, d) ≠ (a, b)} L_{c,d}` is open in `ℂ × ℂ`. -/
theorem divisorNbhd_isOpen (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) (a b : ℤ) :
    IsOpen (divisorNbhd α a b) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hpH : 0 < p.1.im := hp.1
  have hB := divisorNbhdOpen_ball_subset hpH
  have hfin := divisor_locally_finite α hα0 hα1 (isCompact_closedBall p (p.1.im / 2)) hB
  set F := {ab : ℤ × ℤ | (divisorComponent α ab.1 ab.2 ∩ closedBall p (p.1.im / 2)).Nonempty}
  let V : Set (ℂ × ℂ) := ball p (p.1.im / 2) ∩
    ⋂ c ∈ F \ {(a, b)}, {q | q.2 ≠ -(α : ℂ) + c.1 * q.1 + c.2}
  have hVopen : IsOpen V :=
    isOpen_ball.inter (hfin.sdiff.isOpen_biInter fun c _ =>
      isOpen_ne_fun continuous_snd (by fun_prop))
  have hpV : p ∈ V := ⟨mem_ball_self (by linarith), Set.mem_iInter₂.mpr fun c hc heq =>
    hp.2 (Set.mem_iUnion₂.mpr ⟨c, hc.2, hpH, heq⟩)⟩
  refine Filter.mem_of_superset (hVopen.mem_nhds hpV) fun q hq =>
    ⟨hB (ball_subset_closedBall hq.1), fun hq' => ?_⟩
  obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hq'
  exact Set.mem_iInter₂.mp hq.2 c ⟨⟨q, hqc, ball_subset_closedBall hq.1⟩, hc⟩ hqc.2

end HigherDyson3
