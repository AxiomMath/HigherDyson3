/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCHolomorphic
public import HigherDyson3.Theta.TwistedThetaHolomorphic

/-!
# The twisted theta sum is holomorphic

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, and `x = e(α)`. The function
`(τ, w) ↦ ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ, w)` is holomorphic on `ℍ × ℂ`:
each `C_{m,ℓ,x}` is holomorphic on `ℍ`, each `T^{[x]}_{m,ℓ}` is holomorphic on `ℍ × ℂ`,
and finite sums of products of holomorphic functions are holomorphic.

## Main results

* `HigherDyson3.differentiableOn_thetaSum`: the twisted theta sum is complex differentiable
  on `ℍ × ℂ`.
-/

public section

namespace HigherDyson3

/-- **The twisted theta sum is holomorphic.** For `m ≥ 2` and `α ∈ ℚ` with `0 ≤ α < 1`, the
function `(τ, w) ↦ ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ, w)` is complex differentiable
on `ℍ × ℂ`. -/
theorem differentiableOn_thetaSum {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∑ ℓ ∈ Finset.range (2 * m), coeffC m ℓ α p.1 * twistedTheta m ℓ α p.1 p.2)
      halfPlaneProd := by
  refine DifferentiableOn.fun_sum fun ℓ hℓ => ?_
  refine DifferentiableOn.mul ?_ (differentiableOn_twistedTheta (by omega) ℓ α)
  exact (differentiableOn_coeffC hm hα0 hα1 (Finset.mem_range.mp hℓ)).comp differentiableOn_fst
    fun p hp => hp

end HigherDyson3
