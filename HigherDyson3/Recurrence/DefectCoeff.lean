/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Coefficients of the defect polynomial

Let `m ≥ 2` and `d = 2m + 1`. For `0 ≤ a ≤ d - 2`, the coefficient of `U^a` in the defect
polynomial `R_{d,x}(U;q)` is
`δ_{a,d-3} q⁻¹ x⁻² X₀ + δ_{a,d-2} x⁻¹ X₁ - ∑_{k=0}^{a} x^k X_k`.
The two monomials contribute the Kronecker deltas, and the inner sum `∑_{a'=k}^{d-2} U^{a'}`
of the double sum contains `U^a`, with coefficient `1`, exactly when `k ≤ a`.

## Main results

* `HigherDyson3.defectPoly_coeff`: the coefficient formula for `defectPoly`.

## Implementation notes

The hypotheses `2 ≤ m`, `x ≠ 0` and `0 < ‖q‖ < 1` are those of the source and are kept in
the statement; the computation is purely formal and uses only `a ≤ d - 2`.

## References

* [Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher Dyson
  ranks*]
-/

public section

open Finset Polynomial

namespace HigherDyson3

/-- For `a ≤ d - 2`, the coefficient of `U^a` in `R_{d,x}(U;q)` is
`δ_{a,d-3} q⁻¹x⁻²X₀ + δ_{a,d-2} x⁻¹X₁ - ∑_{k=0}^{a} x^k X_k`. -/
theorem defectPoly_coeff {m : ℕ} (_hm : 2 ≤ m) {x q : ℂ} (_hx : x ≠ 0) (_hq0 : 0 < ‖q‖)
    (_hq1 : ‖q‖ < 1) {a : ℕ} (ha : a ≤ 2 * m + 1 - 2) :
    (defectPoly m x q).coeff a =
      (if a = 2 * m + 1 - 3 then q⁻¹ * (x ^ 2)⁻¹ * XSeries m x 0 q else 0) +
      (if a = 2 * m + 1 - 2 then x⁻¹ * XSeries m x 1 q else 0) -
      ∑ k ∈ range (a + 1), x ^ k * XSeries m x k q := by
  have hinner (k : ℕ) : (∑ a' ∈ Icc k (2 * m + 1 - 2), (X : ℂ[X]) ^ a').coeff a =
      if k ≤ a then 1 else 0 := by
    simp only [finsetSum_coeff, coeff_X_pow, sum_ite_eq, mem_Icc]
    by_cases hk : k ≤ a
    · simp only [hk, ha, and_self, ite_true]
    · simp [hk]
  simp only [defectPoly, coeff_add, coeff_sub, finsetSum_coeff,
    coeff_C_mul, hinner, mul_ite, mul_one, mul_zero]
  congr 1
  · congr 1 <;> split_ifs <;> simp_all [eq_comm]
  · rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter, mem_range]
    omega

end HigherDyson3
