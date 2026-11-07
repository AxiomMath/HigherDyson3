/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.PeriodizationDecomposition

/-!
# The finite part is the twisted theta sum

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. For `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, the
finite part `ℰ^{fin}_{m,x} = ℰ_{m,x} - ρ_{m,x} 𝒦_{m,x}` is the twisted theta sum
`ℰ^{fin}_{m,x}(τ,w) = ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ,w)`.

## Main results

* `HigherDyson3.finitePart_eq_sum_twistedTheta`: the finite part equals the twisted theta
  sum off the divisor.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- **The finite part is the twisted theta sum.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and
`(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, `x = e(α)`,
`ℰ^{fin}_{m,x}(τ,w) = ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ,w)`. -/
theorem finitePart_eq_sum_twistedTheta {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor α) :
    finitePart m α τ w = ∑ ℓ ∈ range (2 * m), coeffC m ℓ α τ * twistedTheta m ℓ α τ w := by
  rw [finitePart, periodization_decomposition hm hα0 hα1 hτw, add_sub_cancel_left]

end HigherDyson3
