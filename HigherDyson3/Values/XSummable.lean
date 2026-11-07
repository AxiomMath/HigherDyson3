/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GBound

/-!
# Absolute convergence of the series `X_j(x; q)`

Let `m ≥ 2`, `d = 2m + 1`, and let `g_{k,x}(q) = G_d(x q^k; q)` be the tails of the product
`G_d`. For `x ∈ ℂ`, `j ∈ ℤ` and `0 < |q| < 1` the series
`∑_{k ≥ 0} q^{k² + jk} g_{k,x}(q)` converges absolutely.

Indeed, the tails are bounded uniformly in `k` by `exists_bound_norm_gTail`, and the elementary
inequality `k² + jk ≥ k - (j - 1)²` (equivalently `k² + (j - 1)k + (j - 1)² ≥ 0`) dominates
`|q|^{k² + jk}` by a constant multiple of the geometric sequence `|q|^k`.

## Main results

* `HigherDyson3.summable_norm_XSeries_term`: the summands of `XSeries` are absolutely summable.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

namespace HigherDyson3

/-- **Absolute convergence of `X_j`.** For `m ≥ 2`, `x ∈ ℂ`, `j ∈ ℤ` and `0 < ‖q‖ < 1`, the
summands `q^{k² + jk} g_{k,x}(q)` of `XSeries m x j q` are absolutely summable. -/
theorem summable_norm_XSeries_term {m : ℕ} (hm : 2 ≤ m) (x : ℂ) (j : ℤ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) :
    Summable (fun k : ℕ => ‖q ^ ((k : ℤ) ^ 2 + j * k) * gTail m x k q‖) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_norm_gTail hm (norm_nonneg q) hq1 (norm_nonneg x)
  have hr0 : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0.le hq1).mul_left (C * ‖q‖ ^ (-(j - 1) ^ 2)))
  rw [norm_mul, norm_zpow]
  have h1 : ‖q‖ ^ ((k : ℤ) ^ 2 + j * k) ≤ ‖q‖ ^ (-(j - 1) ^ 2 + (k : ℤ)) :=
    zpow_le_zpow_right_of_le_one₀ hr0 hq1.le (by nlinarith [sq_nonneg ((k : ℤ) + (j - 1))])
  rw [zpow_add₀ hr0.ne' (-(j - 1) ^ 2) (k : ℤ), zpow_natCast] at h1
  calc ‖q‖ ^ ((k : ℤ) ^ 2 + j * k) * ‖gTail m x k q‖
      ≤ (‖q‖ ^ (-(j - 1) ^ 2) * ‖q‖ ^ k) * C :=
        mul_le_mul h1 (hC k q le_rfl x le_rfl) (norm_nonneg _) (by positivity)
    _ = C * ‖q‖ ^ (-(j - 1) ^ 2) * ‖q‖ ^ k := by ring

end HigherDyson3
