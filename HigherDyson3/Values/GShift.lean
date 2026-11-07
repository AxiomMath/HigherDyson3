/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GMultipliable

/-!
# The product shift for `G_d`

Let `m ≥ 2`, `d = 2m + 1` and `P_d(z) = 1 + z + ⋯ + z^{d-1}`. For `|q| < 1` and any `y`,
the product `G_d(y; q) = ∏_{r ≥ 1} P_d(y q^r)` satisfies the shift relation
`G_d(y; q) = P_d(y q) G_d(y q; q)`: splitting off the factor `r = 1` leaves
`∏_{r ≥ 2} P_d(y q^r) = ∏_{r ≥ 1} P_d((y q) q^r)`, which is `G_d(y q; q)`.

## Main results

* `HigherDyson3.GProduct_eq_cyclotomicSum_mul_GProduct`: the product shift
  `G_d(y; q) = P_d(y q) G_d(y q; q)`.

## Implementation notes

The identity is obtained by peeling off the first factor of the unconditional product,
using that the shifted factors `P_d((y q) q^r)` are multipliable, rather than by passing to
the limit in the partial products.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset

namespace HigherDyson3

/-- **Product shift.** For `m ≥ 2` and `‖q‖ < 1`, `G_d(y; q) = P_d(y q) G_d(y q; q)`. -/
theorem GProduct_eq_cyclotomicSum_mul_GProduct {m : ℕ} (hm : 2 ≤ m) {q : ℂ} (hq : ‖q‖ < 1)
    (y : ℂ) : GProduct m y q = cyclotomicSum m (y * q) * GProduct m (y * q) q := by
  have hshift : (fun r : ℕ => cyclotomicSum m (y * q ^ (r + 1 + 1))) =
      fun r : ℕ => cyclotomicSum m (y * q * q ^ (r + 1)) := by
    funext r; congr 1; ring
  have hmul := multipliable_cyclotomicSum hm hq (y * q)
  rw [← hshift] at hmul
  unfold GProduct
  rw [tprod_eq_zero_mul' (f := fun r : ℕ => cyclotomicSum m (y * q ^ (r + 1))) hmul, hshift,
    zero_add, pow_one]

end HigherDyson3
