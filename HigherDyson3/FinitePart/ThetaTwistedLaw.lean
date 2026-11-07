/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.KernelTwistedLaw
public import HigherDyson3.Periodization.EllipticTwistedLaw

/-!
# The twisted elliptic law of the finite part

For `m ≥ 2`, `x = e(α)` and `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, the finite part
`ℰ^{fin}_{m,x} = ℰ_{m,x} - ρ_{m,x} 𝒦_{m,x}` obeys, for all `a, b ∈ ℤ`, with `q = e(τ)` and
`u = e(w)`,
`ℰ^{fin}_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} ℰ^{fin}_{m,x}(τ, w)`.

Both the periodization and the kernel obey this law with the same multiplier, and the
coefficient `ρ_{m,x}(τ)` does not depend on `w`.

## Main results

* `HigherDyson3.finitePart_twisted_law`: the twisted elliptic law of the finite part.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

noncomputable section

namespace HigherDyson3

/-- **Twisted elliptic law** of the finite part: for `a, b ∈ ℤ`,
`ℰ^{fin}_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} ℰ^{fin}_{m,x}(τ, w)`, where
`x = e(α)`, `q = e(τ)` and `u = e(w)`. -/
theorem finitePart_twisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    finitePart m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ w := by
  unfold finitePart
  rw [periodization_twisted_law hm hα0 hα1 hτw a b,
    kernel_add_mul_add m hm α hα0 hα1 τ w hτw a b]
  ring

end HigherDyson3
