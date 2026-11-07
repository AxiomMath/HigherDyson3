/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Values.XSummable

/-!
# Absolute convergence of the seed series

Let `m ≥ 2`, `d = 2m + 1`, and let `g_{k,x}(q) = G_d(x q^k; q)` be the tails of the product
`G_d`. For `x, u ∈ ℂ` and `0 < |q| < 1` the series
`∑_{k ≥ 0} q^{k²} g_{k,x}(q) / (1 - x u q^k)` defining `seed m x u q` converges absolutely.

Since `|q| < 1`, the denominators `1 - x u q^k` tend to `1`, so their inverses form a bounded
sequence; the summands are therefore dominated by a constant multiple of the absolutely
summable terms `q^{k²} g_{k,x}(q)` of `X_0(x; q)`.

## Main results

* `HigherDyson3.summable_norm_seed_term`: the summands of `seed` are absolutely summable.

## Implementation notes

The hypothesis `x u q^k ≠ 1` for all `k` is not needed: division by zero is zero in Lean, so a
vanishing denominator only replaces a summand by `0`, and the inverses `(1 - x u q^k)⁻¹` remain a
bounded sequence regardless.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

namespace HigherDyson3

open Filter Topology

/-- **Absolute convergence of the seed series.** For `m ≥ 2`, `x, u ∈ ℂ` and `0 < ‖q‖ < 1`, the
summands `q^{k²} g_{k,x}(q) / (1 - x u q^k)` of `seed m x u q` are absolutely summable. -/
theorem summable_norm_seed_term {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (u : ℂ) :
    Summable (fun k : ℕ => ‖q ^ (k ^ 2) * gTail m x k q / (1 - x * u * q ^ k)‖) := by
  have hX := summable_norm_XSeries_term hm x 0 hq0 hq1
  have ht : Tendsto (fun k : ℕ => (1 - x * u * q ^ k)⁻¹) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ => x * u * q ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq1).const_mul (x * u)
    simpa using (tendsto_const_nhds.sub h0).inv₀ (by simp : (1 : ℂ) - 0 ≠ 0)
  obtain ⟨A, hA⟩ := ht.norm.bddAbove_range
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hX.mul_right A)
  have hk : ((k : ℤ) ^ 2 + (0 : ℤ) * k) = ((k ^ 2 : ℕ) : ℤ) := by push_cast; ring
  rw [hk, zpow_natCast, div_eq_mul_inv, norm_mul]
  exact mul_le_mul_of_nonneg_left (hA ⟨k, rfl⟩) (norm_nonneg _)

end HigherDyson3
