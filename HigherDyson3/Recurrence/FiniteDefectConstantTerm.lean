/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.DefectCoeff

/-!
# The constant term of the defect polynomial

Let `m ≥ 2` and `d = 2m + 1`. The constant term of the defect polynomial `R_{d,x}(U;q)` is
`-X₀^{(m)}(x;q)`. This is the case `a = 0` of the coefficient formula for `defectPoly`: since
`d - 3 ≥ 2` and `d - 2 ≥ 3`, both Kronecker deltas vanish, and the remaining sum
`∑_{k=0}^{0} x^k X_k` is `X₀`.

## Main results

* `HigherDyson3.defectPoly_coeff_zero`: `[U⁰] R_{d,x}(U;q) = -X₀^{(m)}(x;q)`.

## References

* [Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher Dyson
  ranks*]
-/

public section

open Finset Polynomial

namespace HigherDyson3

/-- The constant term of `R_{d,x}(U;q)` is `-X₀^{(m)}(x;q)`. -/
theorem defectPoly_coeff_zero {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0) (hq0 : 0 < ‖q‖)
    (hq1 : ‖q‖ < 1) :
    (defectPoly m x q).coeff 0 = -XSeries m x 0 q := by
  rw [defectPoly_coeff hm hx hq0 hq1 (Nat.zero_le _)]
  have h3 : (0 : ℕ) ≠ 2 * m + 1 - 3 := by omega
  have h2 : (0 : ℕ) ≠ 2 * m + 1 - 2 := by omega
  simp only [h3, h2, ↓reduceIte]
  simp

end HigherDyson3
