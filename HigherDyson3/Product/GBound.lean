/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GFactorBound
public import HigherDyson3.Product.ProdOneAddBound

/-!
# A uniform bound on the tails `g_{k,x}`

Let `m ≥ 2`, `d = 2m + 1`, and let `g_{k,x}(q) = G_d(x q^k; q)` be the tails of the product
`G_d(y; q) = ∏_{r ≥ 1} P_d(y q^r)`. For `0 ≤ Q < 1` and `B ≥ 0` the tails are bounded
uniformly in `k ∈ ℕ`, `|q| ≤ Q` and `|x| ≤ B`.

Indeed, with `y = x q^k` one has `|y| ≤ B Q^k ≤ B`, so the factors `1 + a_r = P_d(y q^r)`
satisfy `|a_r| ≤ M_r` for the summable sequence `M_r` of the uniform factor bound, and the
estimate `|∏ (1 + a_r) - 1| ≤ exp (∑ |a_r|) - 1` gives `|g_{k,x}(q)| ≤ exp (∑ M_r)`.

## Main results

* `HigherDyson3.exists_bound_norm_gTail`: the uniform bound on the tails.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset

namespace HigherDyson3

/-- **Uniform bound on the tails.** For `0 ≤ Q < 1` and `B ≥ 0` there is a constant `C ≥ 0`
with `‖g_{k,x}(q)‖ ≤ C` for all `k`, all `‖q‖ ≤ Q` and all `‖x‖ ≤ B`. -/
theorem exists_bound_norm_gTail {m : ℕ} (hm : 2 ≤ m) {Q B : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q → ∀ x : ℂ, ‖x‖ ≤ B → ‖gTail m x k q‖ ≤ C := by
  obtain ⟨M, hM0, hMs, hM⟩ := exists_summable_bound_cyclotomicSum_sub_one hm hQ0 hQ1 hB
  refine ⟨Real.exp (∑' r, M r), (Real.exp_pos _).le, fun k q hq x hx => ?_⟩
  set y := x * q ^ k with hy
  have hyB : ‖y‖ ≤ B := by
    rw [hy, norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (hq.trans hQ1.le))).trans hx
  set a : ℕ → ℂ := fun r => cyclotomicSum m (y * q ^ (r + 1)) - 1 with ha
  have haM : ∀ r, ‖a r‖ ≤ M r := fun r => hM r q hq y hyB
  have has : Summable fun r => ‖a r‖ :=
    Summable.of_nonneg_of_le (fun r => norm_nonneg _) haM hMs
  have hg : gTail m x k q = ∏' r, (1 + a r) := by
    simp only [gTail, GProduct, ha, add_sub_cancel, hy]
  have h1 := norm_tprod_one_add_sub_one_le has
  rw [← hg] at h1
  have h2 := Real.exp_le_exp.mpr (Summable.tsum_le_tsum haM has hMs)
  have h3 := norm_sub_norm_le (gTail m x k q) 1
  rw [norm_one] at h3
  linarith

end HigherDyson3

end
