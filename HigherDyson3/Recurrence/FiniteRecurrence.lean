/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Values.GShift
public import HigherDyson3.Values.XSummable

/-!
# The finite recurrence for the series `X_j(x; q)`

Let `m ≥ 2`, `d = 2m + 1`, `P_d(z) = 1 + z + ⋯ + z^{d-1}` and `g_k = G_d(x q^k; q)`. For
`0 < |q| < 1` the series `X_j(x; q) = ∑_{k ≥ 0} q^{k² + jk} g_k` satisfy
`∑_{r=0}^{d-1} x^r X_{j+r-2}(x; q) - q^{j-1} X_j(x; q) = C_x G_d(x; q)`.

The product shift gives `g_k = P_d(x q^{k+1}) g_{k+1} = ∑_r x^r q^{r(k+1)} g_{k+1}`, and with
`N = k + 1` one has `k² + jk + r(k+1) = N² + (j+r-2)N + 1 - j`. Hence
`q^{k²+jk} g_k = q^{1-j} ∑_r x^r q^{N² + (j+r-2)N} g_N`. Summing over `k ≥ 0` and using the
absolute convergence of each `X_{j+r-2}`, the right side becomes
`q^{1-j} ∑_r x^r (X_{j+r-2} - g_0)`, and `g_0 = G_d(x; q)`, `∑_r x^r = C_x`.

## Main results

* `HigherDyson3.cyclotomic_XSeries_recurrence`: the finite recurrence
  `∑_{r=0}^{d-1} x^r X_{j+r-2} - q^{j-1} X_j = C_x G_d(x; q)`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- One term of `X_j` rewritten through the product shift:
`q^{k²+jk} g_k = q^{1-j} ∑_r x^r q^{(k+1)² + (j+r-2)(k+1)} g_{k+1}`. -/
private lemma finiteRecurrence_term {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) (k : ℕ) :
    q ^ ((k : ℤ) ^ 2 + j * k) * gTail m x k q =
      q ^ (1 - j) * ∑ r ∈ range (2 * m + 1),
        x ^ r * (q ^ (((k + 1 : ℕ) : ℤ) ^ 2 + (j + r - 2) * ((k + 1 : ℕ) : ℤ)) *
          gTail m x (k + 1) q) := by
  have hg : gTail m x k q = cyclotomicSum m (x * q ^ (k + 1)) * gTail m x (k + 1) q := by
    unfold gTail
    rw [GProduct_eq_cyclotomicSum_mul_GProduct hm hq1, mul_assoc, ← pow_succ]
  rw [hg, cyclotomicSum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hexp : q ^ ((k : ℤ) ^ 2 + j * k) * q ^ (r * (k + 1)) =
      q ^ (1 - j) * q ^ (((k + 1 : ℕ) : ℤ) ^ 2 + (j + r - 2) * ((k + 1 : ℕ) : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
    congr 1
    push_cast
    ring
  rw [mul_pow, ← pow_mul]
  linear_combination x ^ r * gTail m x (k + 1) q * hexp

/-- **Finite recurrence for `X_j`.** For `m ≥ 2`, `d = 2m + 1`, `0 < ‖q‖ < 1` and `j ∈ ℤ`,
`∑_{r=0}^{d-1} x^r X_{j+r-2}(x; q) - q^{j-1} X_j(x; q) = C_x G_d(x; q)`. -/
theorem cyclotomic_XSeries_recurrence {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) :
    ∑ r ∈ range (2 * m + 1), x ^ r * XSeries m x (j + r - 2) q - q ^ (j - 1) * XSeries m x j q =
      Cx m x * GProduct m x q := by
  set T : ℤ → ℕ → ℂ := fun i k => q ^ ((k : ℤ) ^ 2 + i * k) * gTail m x k q with hT
  have hsum : ∀ i, Summable (T i) := fun i =>
    (summable_norm_XSeries_term hm x i hq0 hq1).of_norm
  have hT0 : ∀ i, T i 0 = GProduct m x q := fun i => by
    simp [hT, gTail]
  have hshift : ∀ i, ∑' k, T i (k + 1) = XSeries m x i q - GProduct m x q := fun i => by
    rw [XSeries, (hsum i).tsum_eq_zero_add, ← hT0 i]
    ring
  have hX : XSeries m x j q = q ^ (1 - j) *
      ∑ r ∈ range (2 * m + 1), x ^ r * (XSeries m x (j + r - 2) q - GProduct m x q) := by
    have h1 : XSeries m x j q = ∑' k, q ^ (1 - j) * ∑ r ∈ range (2 * m + 1),
        x ^ r * T (j + r - 2) (k + 1) := by
      unfold XSeries
      exact tsum_congr fun k => finiteRecurrence_term hm x hq0 hq1 j k
    rw [h1, tsum_mul_left, Summable.tsum_finsetSum
      (fun r _ => ((summable_nat_add_iff 1).mpr (hsum _)).mul_left _)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [tsum_mul_left, hshift]
  have hq : q ^ (j - 1) * q ^ (1 - j) = 1 := by
    rw [← zpow_add₀ hq0]; simp
  rw [hX, ← mul_assoc, hq, one_mul, Cx, cyclotomicSum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

end HigherDyson3
