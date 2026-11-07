/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Recurrence.FiniteFunctionalEquation

/-!
# Uniqueness of the defect polynomial

Let `m ≥ 2`, `d = 2m + 1`, `x ≠ 0` and `0 < |q| < 1`. If a polynomial `R'` of degree at most
`d - 2` satisfies the functional equation of the seed in place of `R_{d,x}(U; q)` at every point
of a nonempty open set `V ⊆ ℂ` avoiding `0` and the points `x⁻¹ q^{-k}`, then
`R' = R_{d,x}(U; q)`.

Subtracting the functional equation of the seed gives `q u^{3-d} (R'(u) - R_{d,x}(u; q)) = 0`
on `V`, so the two polynomials agree on the infinite set `V`.

## Main results

* `HigherDyson3.eq_defectPoly_of_functionalEquation`: uniqueness of the defect polynomial.

## Implementation notes

The degree bound on `R'` is the source's hypothesis and is kept in the statement, although
agreement on an infinite set determines a polynomial of any degree.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- **Uniqueness of the defect polynomial.** Let `m ≥ 2`, `d = 2m + 1`, `x ≠ 0` and
`0 < ‖q‖ < 1`. Let `R'` be a polynomial of degree at most `d - 2` and `V ⊆ ℂ` a nonempty open
set such that every `u ∈ V` satisfies `u ≠ 0`, `x u q^k ≠ 1` for all `k ∈ ℕ`, and
`𝒢_{d,x}(q u; q) = x² q (∑_{r=0}^{d-1} u^{2-r}) 𝒢_{d,x}(u; q) + q u^{3-d} R'(u)
  - C_x q u² / (1 - x u) G_d(x; q)`. Then `R' = R_{d,x}(U; q)`. -/
@[nolint unusedArguments]
theorem eq_defectPoly_of_functionalEquation {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {R' : Polynomial ℂ}
    (_hdeg : R'.degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ)) {V : Set ℂ} (hVo : IsOpen V)
    (hVne : V.Nonempty)
    (hV : ∀ u ∈ V, u ≠ 0 ∧ (∀ k : ℕ, x * u * q ^ k ≠ 1) ∧
      seed m x (q * u) q =
        x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
          q * u ^ (3 - (2 * m + 1 : ℤ)) * R'.eval u -
          Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q) :
    R' = defectPoly m x q := by
  have hq : q ≠ 0 := norm_pos_iff.mp hq0
  obtain ⟨z, hz⟩ := hVne
  refine Polynomial.eq_of_infinite_eval_eq _ _
    ((infinite_of_mem_nhds z (hVo.mem_nhds hz)).mono fun u hu => ?_)
  obtain ⟨hu0, hxu, heq⟩ := hV u hu
  have hfe := seed_mul_eq_defectPoly hm hx hq0 hq1 hu0 hxu
  have hdiff : q * u ^ (3 - (2 * m + 1 : ℤ)) * (R'.eval u - (defectPoly m x q).eval u) = 0 := by
    linear_combination hfe - heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left
    (mul_ne_zero hq (zpow_ne_zero _ hu0)))

end HigherDyson3
