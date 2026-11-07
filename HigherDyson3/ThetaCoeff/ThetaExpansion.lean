/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.FinitePart.FinitePartEqTheta
public import HigherDyson3.Theta.TwistedThetaTranslation
public import HigherDyson3.ThetaCoeff.HEqC

/-!
# Theta expansion of the translated finite part

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. For `(τ, w) ∈ ℍ × ℂ` with
`(τ, w + α/m) ∉ 𝒟_x`, the translated finite part expands in the standard theta series with
the theta coefficients as coefficients:
`ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h_{m,ℓ,x}(τ) ϑ_{m,ℓ}(τ, w)`.

## Main results

* `HigherDyson3.finitePart_add_div_eq_sum_theta`: the theta expansion of the translated
  finite part.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- **Theta expansion of the translated finite part.** For `m ≥ 2`, `α ∈ ℚ` with
`0 ≤ α < 1`, `τ ∈ ℍ` and `w ∈ ℂ` with `(τ, w + α/m) ∉ 𝒟_x`, `x = e(α)`,
`ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h_{m,ℓ,x}(τ) ϑ_{m,ℓ}(τ, w)`. -/
theorem finitePart_add_div_eq_sum_theta {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {τ w : ℂ} (hτ : τ ∈ upperHalfPlaneSet)
    (hw : (τ, w + (α : ℂ) / m) ∉ divisor α) :
    finitePart m α τ (w + (α : ℂ) / m) =
      ∑ ℓ ∈ range (2 * m), thetaCoeffH m ℓ α τ * theta m ℓ τ w := by
  rw [finitePart_eq_sum_twistedTheta hm hα0 hα1 ⟨hτ, hw⟩]
  refine sum_congr rfl fun ℓ hℓ => ?_
  have hℓ' : ℓ < 2 * m := mem_range.mp hℓ
  rw [twistedTheta_add_div m ℓ hm hℓ' α hα0 hα1 τ w hτ,
    thetaCoeffH_eq_coeffC hm hα0 hα1 hℓ' hτ]
  ring

end HigherDyson3
