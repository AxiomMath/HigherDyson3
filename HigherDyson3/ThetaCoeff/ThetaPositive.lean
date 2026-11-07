/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCPos
public import HigherDyson3.ThetaCoeff.HEqC

/-!
# Positivity of the theta coefficients at `x = 1`

Let `m ≥ 2`, `d = 2m + 1`, `α = 0` (so `x = e(0) = 1`), `0 ≤ ℓ < 2m` and `t > 0`. Then the
theta coefficient `h_{m,ℓ,1}(it)` is a positive real number.

By `HigherDyson3.thetaCoeffH_eq_coeffC`,
`h_{m,ℓ,1}(it) = e(0) e(-ℓ²it/(4m)) C_{m,ℓ,1}(it)`. Here `e(0) = 1`, the factor
`e(-ℓ²it/(4m)) = exp(2πℓ²t/(4m))` is a positive real, and `C_{m,ℓ,1}(it)` is a positive real by
`HigherDyson3.coeffC_pos`.

## Main results

* `HigherDyson3.thetaCoeffH_pos`: `0 < h_{m,ℓ,1}(it)` for real `t > 0`.

## Implementation notes

Positivity is stated with the partial order on `ℂ`, in which `0 < z` means that `z` is real
and positive.

## References

* Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher Dyson
  ranks*.
-/

public section

open Complex

open scoped ComplexOrder

namespace HigherDyson3

/-- On the imaginary axis, `e(-ℓ²it/(4m))` is the positive real `exp(2πℓ²t/(4m))`. -/
private lemma thetaPositive_e_pos (m ℓ : ℕ) (t : ℝ) :
    0 < e (-((ℓ : ℂ) ^ 2) * (I * t) / (4 * m)) := by
  have h : e (-((ℓ : ℂ) ^ 2) * (I * t) / (4 * m)) =
      ((Real.exp (2 * Real.pi * ℓ ^ 2 * t / (4 * m)) : ℝ) : ℂ) := by
    unfold e
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [h, Complex.zero_lt_real]
  exact Real.exp_pos _

/-- **Positivity for `x = 1`.** For `m ≥ 2`, `0 ≤ ℓ < 2m` and real `t > 0`, the theta
coefficient `h_{m,ℓ,1}(it)` is a positive real number. -/
theorem thetaCoeffH_pos {m : ℕ} (hm : 2 ≤ m) {ℓ : ℕ} (hℓ : ℓ < 2 * m) {t : ℝ} (ht : 0 < t) :
    0 < thetaCoeffH m ℓ 0 (I * t) := by
  have hτ : I * (t : ℂ) ∈ upperHalfPlaneSet := by
    change 0 < (I * (t : ℂ)).im
    simpa using ht
  rw [thetaCoeffH_eq_coeffC hm le_rfl (by norm_num) hℓ hτ]
  have h0 : e ((ℓ : ℂ) * ((0 : ℚ) : ℂ) / m) = 1 := by simp [e]
  rw [h0, one_mul]
  exact mul_pos (thetaPositive_e_pos m ℓ t) (coeffC_pos hm hℓ ht)

end HigherDyson3
