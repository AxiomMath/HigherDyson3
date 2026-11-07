/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# The degree of the defect polynomial

Let `m ≥ 2`, `d = 2m + 1`, `x ∈ ℂˣ` and `0 < |q| < 1`. The defect polynomial `R_{d,x}(U;q)`
is a linear combination of the monomials `U^{d-3}`, `U^{d-2}` and `U^a` with `0 ≤ a ≤ d - 2`,
so its degree is at most `d - 2`.

## Main results

* `HigherDyson3.defectPoly_degree_le`: `deg R_{d,x}(U;q) ≤ d - 2`.

## Implementation notes

The argument only uses the shape of `R_{d,x}`: every monomial occurring in it has exponent
at most `d - 2`, so `R_{d,x}` lies in the submodule `Polynomial.degreeLE ℂ (d - 2)`. The
hypotheses `2 ≤ m`, `x ≠ 0` and `0 < |q| < 1` are those of the source and are kept in the
statement, although the bound holds for all `m`, `x` and `q`.

## References

* [Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher Dyson
  ranks*]
-/

public section

namespace HigherDyson3

open Polynomial Finset

/-- For `m ≥ 2`, `x ≠ 0` and `0 < ‖q‖ < 1`, the defect polynomial `R_{d,x}(U;q)`, with
`d = 2m + 1`, has degree at most `d - 2`. -/
@[nolint unusedArguments]
theorem defectPoly_degree_le {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (_hx : x ≠ 0) (_hq0 : 0 < ‖q‖)
    (_hq1 : ‖q‖ < 1) :
    (defectPoly m x q).degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ) := by
  rw [← Polynomial.mem_degreeLE]
  have hX : ∀ a ≤ 2 * m + 1 - 2, ∀ c : ℂ,
      C c * X ^ a ∈ degreeLE ℂ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ) := fun a ha c => by
    rw [Polynomial.mem_degreeLE]
    exact (degree_C_mul_X_pow_le a c).trans (by exact_mod_cast ha)
  unfold defectPoly
  refine Submodule.sub_mem _ (Submodule.add_mem _ (hX _ (by omega) _) (hX _ le_rfl _))
    (Submodule.sum_mem _ fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Submodule.sum_mem _ fun a ha => hX a (Finset.mem_Icc.1 ha).2 _

end HigherDyson3
