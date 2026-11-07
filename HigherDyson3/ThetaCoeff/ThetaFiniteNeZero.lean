/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.ThetaCoeff.ThetaUnique
public import HigherDyson3.ThetaCoeff.ThetaCoeffNeZero

/-!
# The finite part is not identically zero

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. Then the finite part `ℰ^{fin}_{m,x}`
does not vanish identically on `(ℍ × ℂ) \ 𝒟_x`.

If it did, the zero functions `h'_ℓ = 0` would satisfy the theta expansion
`ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_ℓ h'_ℓ(τ) ϑ_{m,ℓ}(τ, w)` off the divisor, so by uniqueness of
the theta coefficients (`HigherDyson3.thetaCoeffH_unique`) every `h_{m,ℓ,x}` would vanish on
`ℍ`. Taking `ℓ = 0` contradicts `HigherDyson3.exists_thetaCoeffH_ne_zero`.

## Main results

* `HigherDyson3.exists_finitePart_ne_zero`: some value of `ℰ^{fin}_{m,x}` off the divisor is
  nonzero.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- **The finite part is not identically zero.** For `m ≥ 2` and `α ∈ ℚ` with `0 ≤ α < 1`
there is `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x` with `ℰ^{fin}_{m,x}(τ, w) ≠ 0`, where `x = e(α)`. -/
theorem exists_finitePart_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ p ∈ halfPlaneProd \ divisor α, finitePart m α p.1 p.2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero := thetaCoeffH_unique hm hα0 hα1 (fun _ _ => 0) fun τ hτ w hw => by
    simp only [zero_mul, sum_const_zero]
    exact hcon (τ, w + (α : ℂ) / m) ⟨hτ, hw⟩
  obtain ⟨τ, hτ, hne⟩ := exists_thetaCoeffH_ne_zero hm hα0 hα1 (ℓ := 0) (by omega)
  exact hne (hzero 0 (by omega) τ hτ).symm

end HigherDyson3
