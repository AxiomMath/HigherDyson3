/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.ProdOneAddBound

/-!
# Leading term of the tails `g_{k,x}`

Let `m ≥ 2`, `d = 2m + 1` and `P_d(z) = 1 + z + ⋯ + z^{d-1}`. The tail
`g_{k,x}(q) = ∏_{r ≥ 1} P_d(x q^{k+r})` satisfies `g_{k,x}(q) = 1 + O(|q|^{k+1})` as
`q → 0`: there are `C, δ > 0` with `|g_{k,x}(q) - 1| ≤ C |q|^{k+1}` for `|q| < δ`.

Writing `g_{k,x}(q) = ∏_r (1 + a_r)` with `a_r = ∑_{s=1}^{d-1} x^s q^{(k+r)s}`, one has
`|a_r| ≤ S |q|^{k+1} |q|^{r-1}` where `S = ∑_{s=1}^{d-1} |x|^s`, since
`(k+r)s ≥ (k+1) + (r-1)`. For `|q| < 1/2` this gives `∑ |a_r| ≤ 2 S |q|^{k+1} =: t`, and
the bound `|∏ (1 + a_r) - 1| ≤ e^t - 1 ≤ t e^t ≤ 2 S e^{2S} |q|^{k+1}` follows.

## Main results

* `HigherDyson3.exists_norm_gTail_sub_one_le`: the estimate `g_{k,x}(q) - 1 = O(|q|^{k+1})`.

## Implementation notes

The factors are indexed by `r : ℕ` standing for the exponent `r + 1 ≥ 1`, matching
`HigherDyson3.GProduct`. One may take `δ = 1/2` and `C = 2 S e^{2S} + 1`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset

namespace HigherDyson3

/-- `‖P_d(z) - 1‖ ≤ ∑_{s=1}^{d-1} ‖z‖^s`. -/
private theorem gLeading_norm_cyclotomicSum_sub_one_le (m : ℕ) (z : ℂ) :
    ‖cyclotomicSum m z - 1‖ ≤ ∑ s ∈ range (2 * m), ‖z‖ ^ (s + 1) := by
  rw [show cyclotomicSum m z - 1 = ∑ s ∈ range (2 * m), z ^ (s + 1) by
    simp [cyclotomicSum, sum_range_succ']]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_pow])

/-- The `r`-th factor of `g_{k,x}(q)` deviates from `1` by at most
`(∑_{s=1}^{d-1} ‖x‖^s) ‖q‖^{k+1} ‖q‖^r` when `‖q‖ ≤ 1`. -/
private theorem gLeading_norm_factor_sub_one_le (m : ℕ) (x : ℂ) (k r : ℕ) {q : ℂ}
    (hq : ‖q‖ ≤ 1) :
    ‖cyclotomicSum m (x * q ^ k * q ^ (r + 1)) - 1‖ ≤
      (∑ s ∈ range (2 * m), ‖x‖ ^ (s + 1)) * ‖q‖ ^ (k + 1) * ‖q‖ ^ r := by
  refine (gLeading_norm_cyclotomicSum_sub_one_le m _).trans ?_
  rw [sum_mul, sum_mul]
  refine sum_le_sum fun s _ => ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, mul_assoc, ← pow_add, mul_pow, ← pow_mul,
    mul_assoc, ← pow_add, show k + (r + 1) = k + 1 + r by omega]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (norm_nonneg _) hq (by nlinarith)) (by positivity)

/-- `e^t - 1 ≤ t e^t` for every real `t`. -/
theorem exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h' : Real.exp (-t) * Real.exp t = 1 := by simp [← Real.exp_add]
  nlinarith [Real.add_one_le_exp (-t), Real.exp_pos t]

/-- `∑' r, c ρ^r ≤ 2 c` for `0 ≤ c` and `0 ≤ ρ < 1/2`. -/
theorem tsum_mul_geometric_le_two_mul {c ρ : ℝ} (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) :
    ∑' r : ℕ, c * ρ ^ r ≤ 2 * c := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 (by linarith)]
  have h₂ : (1 - ρ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith

/-- **Leading term of the tails.** `g_{k,x}(q) = 1 + O(|q|^{k+1})` as `q → 0`. -/
theorem exists_norm_gTail_sub_one_le {m : ℕ} (_hm : 2 ≤ m) (x : ℂ) (k : ℕ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ q : ℂ, ‖q‖ < δ → ‖gTail m x k q - 1‖ ≤ C * ‖q‖ ^ (k + 1) := by
  set S : ℝ := ∑ s ∈ range (2 * m), ‖x‖ ^ (s + 1)
  have hS0 : 0 ≤ S := sum_nonneg fun s _ => by positivity
  refine ⟨2 * S * Real.exp (2 * S) + 1, 1 / 2, by positivity, by norm_num, fun q hq => ?_⟩
  set a : ℕ → ℂ := fun r => cyclotomicSum m (x * q ^ k * q ^ (r + 1)) - 1 with ha
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hq1 : ‖q‖ < 1 := by linarith
  have hbound : ∀ r, ‖a r‖ ≤ S * ‖q‖ ^ (k + 1) * ‖q‖ ^ r := fun r =>
    gLeading_norm_factor_sub_one_le m x k r hq1.le
  have hgeom : Summable fun r : ℕ => S * ‖q‖ ^ (k + 1) * ‖q‖ ^ r :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum : Summable fun r => ‖a r‖ :=
    hgeom.of_nonneg_of_le (fun r => norm_nonneg _) hbound
  set t : ℝ := 2 * S * ‖q‖ ^ (k + 1)
  have htsum : ∑' r, ‖a r‖ ≤ t :=
    ((hsum.tsum_le_tsum hbound hgeom).trans
      (tsum_mul_geometric_le_two_mul (by positivity) hq0 hq)).trans_eq (mul_assoc _ _ _).symm
  have hg : gTail m x k q = ∏' r, (1 + a r) := by
    simp [gTail, GProduct, ha]
  have hqk : ‖q‖ ^ (k + 1) ≤ 1 := pow_le_one₀ hq0 hq1.le
  have ht2S : t ≤ 2 * S := by nlinarith
  calc ‖gTail m x k q - 1‖ ≤ Real.exp (∑' r, ‖a r‖) - 1 :=
        hg ▸ norm_tprod_one_add_sub_one_le hsum
    _ ≤ Real.exp t - 1 := by gcongr
    _ ≤ t * Real.exp t := exp_sub_one_le_mul_exp t
    _ ≤ t * Real.exp (2 * S) := by gcongr
    _ = 2 * S * Real.exp (2 * S) * ‖q‖ ^ (k + 1) := by ring
    _ ≤ (2 * S * Real.exp (2 * S) + 1) * ‖q‖ ^ (k + 1) := by
      gcongr
      linarith

end HigherDyson3

end
