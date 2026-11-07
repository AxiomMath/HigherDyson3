/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# The theta coefficients in terms of `C_{m,ℓ,x}`

For `m ≥ 2`, `x = e(α)` with `α ∈ ℚ ∩ [0, 1)`, `0 ≤ ℓ < 2m` and `τ ∈ ℍ`, the theta
coefficient factors through the coefficient `C_{m,ℓ,x}`:
`h_{m,ℓ,x}(τ) = e(ℓα/m) e(-ℓ²τ/(4m)) C_{m,ℓ,x}(τ)`.
Both sides carry the same series `x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k …`, so the identity
is a regrouping of the prefactors.

## Main results

* `HigherDyson3.thetaCoeffH_eq_coeffC`: `h_{m,ℓ,x} = e(ℓα/m) e(-ℓ²τ/(4m)) C_{m,ℓ,x}`.

## Implementation notes

The identity holds for every `m`, `ℓ`, `α` and `τ`; the hypotheses of the source statement
are kept so that the statement matches it, and are not used by the proof.

## References

* Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher Dyson
  ranks*.
-/

public section

namespace HigherDyson3

/-- The theta coefficient `h_{m,ℓ,x}(τ)` equals `e(ℓα/m) e(-ℓ²τ/(4m)) C_{m,ℓ,x}(τ)`. -/
theorem thetaCoeffH_eq_coeffC {m : ℕ} (_hm : 2 ≤ m) {α : ℚ} (_hα0 : 0 ≤ α) (_hα1 : α < 1)
    {ℓ : ℕ} (_hℓ : ℓ < 2 * m) {τ : ℂ} (_hτ : τ ∈ upperHalfPlaneSet) :
    thetaCoeffH m ℓ α τ = e (ℓ * α / m) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * coeffC m ℓ α τ := by
  unfold thetaCoeffH coeffC
  ring

end HigherDyson3
