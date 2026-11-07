/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Values.XHolomorphicDisk
public import HigherDyson3.Recurrence.DefectCoeff

/-!
# The coefficients of the defect polynomial have at most a simple pole at `q = 0`

Let `m ≥ 2`, `d = 2m + 1`, `x ∈ ℂˣ` and `0 ≤ a ≤ d - 2`. Then `q [U^a] R_{d,x}(U;q)` agrees,
for `0 < |q| < 1`, with a function holomorphic on the open unit disk.

By the coefficient formula, `q [U^a] R_{d,x}` is
`δ_{a,d-3} x⁻² X₀ + q (δ_{a,d-2} x⁻¹ X₁ - ∑_{k ≤ a} x^k X_k)`, and each `X_k` extends
holomorphically to the disk.

## Main results

* `HigherDyson3.exists_differentiableOn_eq_mul_defectPoly_coeff`: the holomorphic extension.
-/

public section

open Finset

namespace HigherDyson3

/-- **The coefficients have at most a simple pole at `q = 0`.** For `m ≥ 2`, `x ≠ 0` and
`a ≤ d - 2` with `d = 2m + 1`, there is `h`, complex differentiable on the open unit disk, with
`h q = q [U^a] R_{d,x}(U;q)` whenever `0 < ‖q‖ < 1`. -/
theorem exists_differentiableOn_eq_mul_defectPoly_coeff {m : ℕ} (hm : 2 ≤ m) {x : ℂ}
    (hx : x ≠ 0) {a : ℕ} (ha : a ≤ 2 * m + 1 - 2) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * (defectPoly m x q).coeff a := by
  choose f hfd hf using fun k : ℕ => exists_differentiableOn_eq_XSeries hm x k
  refine ⟨fun q => (if a = 2 * m + 1 - 3 then (x ^ 2)⁻¹ * f 0 q else 0) +
      q * ((if a = 2 * m + 1 - 2 then x⁻¹ * f 1 q else 0) -
        ∑ k ∈ range (a + 1), x ^ k * f k q), ?_, ?_⟩
  · refine DifferentiableOn.add ?_ (differentiableOn_id.mul (DifferentiableOn.sub ?_ ?_))
    · split_ifs
      · exact (hfd 0).const_mul _
      · exact differentiableOn_const _
    · split_ifs
      · exact (hfd 1).const_mul _
      · exact differentiableOn_const _
    · exact DifferentiableOn.fun_sum fun k _ => (hfd k).const_mul _
  · intro q hq0 hq1
    have hq : q ≠ 0 := norm_pos_iff.mp hq0
    rw [defectPoly_coeff hm hx hq0 hq1 ha]
    simp only [hf _ q hq hq1]
    split_ifs <;> field_simp <;> push_cast <;> ring

end HigherDyson3
