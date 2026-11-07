/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.FinitePart.FinitePartEqTheta
public import HigherDyson3.LocalFacts.ThetaSumHolomorphic

/-!
# The finite part is holomorphic

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. The finite part
`ℰ^{fin}_{m,x} = ℰ_{m,x} - ρ_{m,x} 𝒦_{m,x}` is a priori only defined off the divisor
`𝒟_x`, where the periodization and the kernel have their poles. It extends holomorphically
to all of `ℍ × ℂ`: off `𝒟_x` it coincides with the twisted theta sum
`F(τ,w) = ∑_{ℓ=0}^{2m-1} C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ,w)`
(`HigherDyson3.finitePart_eq_sum_twistedTheta`), and this sum is holomorphic on `ℍ × ℂ`
(`HigherDyson3.differentiableOn_thetaSum`).

## Main results

* `HigherDyson3.exists_differentiableOn_eqOn_finitePart`: there is a function holomorphic on
  `ℍ × ℂ` agreeing with the finite part on `(ℍ × ℂ) \ 𝒟_x`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

namespace HigherDyson3

/-- **The finite part is holomorphic.** For `m ≥ 2` and `α ∈ ℚ` with `0 ≤ α < 1`, there is a
function `F` complex differentiable on `ℍ × ℂ` with `F(τ,w) = ℰ^{fin}_{m,x}(τ,w)` for all
`(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, `x = e(α)`. -/
theorem exists_differentiableOn_eqOn_finitePart {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ F : ℂ × ℂ → ℂ, DifferentiableOn ℂ F halfPlaneProd ∧
      ∀ p ∈ halfPlaneProd \ divisor α, F p = finitePart m α p.1 p.2 :=
  ⟨_, differentiableOn_thetaSum hm hα0 hα1, fun _ hp =>
    (finitePart_eq_sum_twistedTheta hm hα0 hα1 hp).symm⟩

end HigherDyson3
