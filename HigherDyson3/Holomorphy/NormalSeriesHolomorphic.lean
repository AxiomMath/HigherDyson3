/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import HigherDyson3.Holomorphy.Osgood

/-!
# Normally convergent series of holomorphic functions on `ℂ × ℂ`

Let `U ⊆ ℂ × ℂ` be open and let `(f i)` be holomorphic on `U`, with the series of the suprema
of `‖f i‖` over every compact subset of `U` summable. Then `p ↦ ∑' i, f i p` is holomorphic on
`U`.

## Main results

* `HigherDyson3.differentiableOn_tsum_of_normal`: a normally convergent series of holomorphic
  functions on an open subset of `ℂ × ℂ` is holomorphic.

## Implementation notes

Normal convergence on compact subsets is stated as: every compact `K ⊆ U` admits a summable
majorant `u` with `‖f i p‖ ≤ u i` for `p ∈ K`. This is the summability of the suprema, and no
countability of the index set is needed. The proof works on an open ball whose closure lies in
`U`: there the series is continuous and holomorphic in each variable by the one-variable
results of Mathlib, and Osgood's lemma `HigherDyson3.osgood` gives joint holomorphy.
-/

public section

open Metric

namespace HigherDyson3

/-- The uniform case: on an open set with one summable majorant, the series is holomorphic. -/
private lemma normalSeriesHolomorphic_of_uniform {ι : Type*} {V : Set (ℂ × ℂ)}
    {f : ι → ℂ × ℂ → ℂ} {u : ι → ℝ} (hV : IsOpen V) (hf : ∀ i, DifferentiableOn ℂ (f i) V)
    (hu : Summable u) (hle : ∀ i, ∀ p ∈ V, ‖f i p‖ ≤ u i) :
    DifferentiableOn ℂ (fun p => ∑' i, f i p) V := by
  refine osgood hV (continuousOn_tsum (fun i => (hf i).continuousOn) hu hle) ?_ ?_
  · intro p _
    exact Complex.differentiableOn_tsum_of_summable_norm hu
      (fun i => (hf i).comp (by fun_prop) fun w hw => hw)
      (hV.preimage (by fun_prop)) fun i w hw => hle i _ hw
  · intro p _
    exact Complex.differentiableOn_tsum_of_summable_norm hu
      (fun i => (hf i).comp (by fun_prop) fun τ hτ => hτ)
      (hV.preimage (by fun_prop)) fun i τ hτ => hle i _ hτ

/-- **Normally convergent series of holomorphic functions** on an open subset `U` of `ℂ × ℂ`:
if every `f i` is holomorphic on `U` and on every compact `K ⊆ U` the suprema of `‖f i‖` are
dominated by a summable sequence, then `p ↦ ∑' i, f i p` is holomorphic on `U`. -/
theorem differentiableOn_tsum_of_normal {ι : Type*} {U : Set (ℂ × ℂ)} {f : ι → ℂ × ℂ → ℂ}
    (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hnormal : ∀ K ⊆ U, IsCompact K →
      ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ p ∈ K, ‖f i p‖ ≤ u i) :
    DifferentiableOn ℂ (fun p => ∑' i, f i p) U := by
  intro p hp
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.mp hU p hp
  have hK : closedBall p (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hε
  obtain ⟨u, hu, hle⟩ := hnormal _ hK (isCompact_closedBall p (ε / 2))
  have hB := normalSeriesHolomorphic_of_uniform (V := ball p (ε / 2)) isOpen_ball
    (fun i => (hf i).mono (ball_subset_closedBall.trans hK)) hu
    (fun i q hq => hle i q (ball_subset_closedBall hq))
  exact ((hB p (mem_ball_self (by linarith))).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self (by linarith)))).differentiableWithinAt

end HigherDyson3
