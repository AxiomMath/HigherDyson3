/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCHolomorphic
public import HigherDyson3.ThetaCoeff.HEqC

/-!
# Holomorphy of the theta coefficients `h_{m,ℓ,x}`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ` and `0 ≤ α < 1`, and `0 ≤ ℓ < 2m`. The theta
coefficient `h_{m,ℓ,x}` is holomorphic on the upper half-plane `ℍ`: on `ℍ` it equals
`e(ℓα/m) e(-ℓ²τ/(4m)) C_{m,ℓ,x}(τ)`, a constant times an entire function times the
holomorphic function `C_{m,ℓ,x}`.

## Main results

* `HigherDyson3.differentiableOn_thetaCoeffH`: `h_{m,ℓ,x}` is complex differentiable on `ℍ`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

namespace HigherDyson3

/-- **Holomorphy of the theta coefficients.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and
`0 ≤ ℓ < 2m`, the theta coefficient `h_{m,ℓ,x}` is complex differentiable on the upper
half-plane. -/
theorem differentiableOn_thetaCoeffH {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    DifferentiableOn ℂ (thetaCoeffH m ℓ α) upperHalfPlaneSet := by
  have hE : DifferentiableOn ℂ (fun τ : ℂ => e (ℓ * α / m) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
      coeffC m ℓ α τ) upperHalfPlaneSet := by
    refine DifferentiableOn.mul ?_ (differentiableOn_coeffC hm hα0 hα1 hℓ)
    exact (differentiableOn_const _).mul
      ((coeffCHolomorphic_differentiable_e.comp (by fun_prop)).differentiableOn)
  exact hE.congr fun τ hτ => thetaCoeffH_eq_coeffC hm hα0 hα1 hℓ hτ

end HigherDyson3
