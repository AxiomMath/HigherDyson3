/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GFactorBound

/-!
# Absolute convergence of the product `G_d`

Let `m ≥ 2`, `d = 2m + 1` and `P_d(z) = 1 + z + ⋯ + z^{d-1}`. For `|q| < 1` and any `y`,
the product `G_d(y; q) = ∏_{r ≥ 1} P_d(y q^r)` converges absolutely: the series
`∑_{r ≥ 1} |P_d(y q^r) - 1|` converges, by comparison with the summable bound of
`HigherDyson3.exists_summable_bound_cyclotomicSum_sub_one` taken with `Q = |q|` and `B = |y|`.
Writing `P_d(y q^r) = 1 + a_r` with `∑ |a_r| < ∞`, the product is multipliable, and its
partial products converge to `G_d(y; q)`.

## Main results

* `HigherDyson3.multipliable_cyclotomicSum`: the factors of `G_d(y; q)` are multipliable.
* `HigherDyson3.summable_norm_cyclotomicSum_sub_one_and_tendsto_GProduct`: absolute
  convergence of the product, and convergence of its partial products to
  `HigherDyson3.GProduct`.

## Implementation notes

The factors are indexed by `r : ℕ` standing for the exponent `r + 1 ≥ 1`, matching
`HigherDyson3.GProduct`; so the partial product over `Finset.range n` is the paper's
`∏_{r=1}^{n} P_d(y q^r)`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset

namespace HigherDyson3

/-- The series `∑_{r ≥ 1} ‖P_d(y q^r) - 1‖` converges for `‖q‖ < 1`. -/
theorem summable_norm_cyclotomicSum_sub_one {m : ℕ} (hm : 2 ≤ m) {q : ℂ} (hq : ‖q‖ < 1)
    (y : ℂ) : Summable fun r : ℕ => ‖cyclotomicSum m (y * q ^ (r + 1)) - 1‖ := by
  obtain ⟨M, -, hMs, hMb⟩ :=
    exists_summable_bound_cyclotomicSum_sub_one hm (norm_nonneg q) hq (norm_nonneg y)
  exact hMs.of_nonneg_of_le (fun _ => norm_nonneg _) fun r => hMb r q le_rfl y le_rfl

/-- The factors `P_d(y q^r)`, `r ≥ 1`, of `G_d(y; q)` are multipliable for `‖q‖ < 1`. -/
theorem multipliable_cyclotomicSum {m : ℕ} (hm : 2 ≤ m) {q : ℂ} (hq : ‖q‖ < 1) (y : ℂ) :
    Multipliable fun r : ℕ => cyclotomicSum m (y * q ^ (r + 1)) := by
  have h := multipliable_one_add_of_summable (summable_norm_cyclotomicSum_sub_one hm hq y)
  simpa using h

/-- **Absolute convergence of the product.** For `m ≥ 2` and `‖q‖ < 1`, the series
`∑_{r ≥ 1} ‖P_d(y q^r) - 1‖` converges and the partial products `∏_{r=1}^{n} P_d(y q^r)`
tend to `G_d(y; q)`. -/
theorem summable_norm_cyclotomicSum_sub_one_and_tendsto_GProduct {m : ℕ} (hm : 2 ≤ m)
    {q : ℂ} (hq : ‖q‖ < 1) (y : ℂ) :
    (Summable fun r : ℕ => ‖cyclotomicSum m (y * q ^ (r + 1)) - 1‖) ∧
      Filter.Tendsto (fun n => ∏ r ∈ range n, cyclotomicSum m (y * q ^ (r + 1)))
        Filter.atTop (nhds (GProduct m y q)) :=
  ⟨summable_norm_cyclotomicSum_sub_one hm hq y,
    (multipliable_cyclotomicSum hm hq y).hasProd.tendsto_prod_nat⟩

end HigherDyson3

end
