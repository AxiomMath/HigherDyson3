/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# A uniform summable bound on the factors of `G_d`

Let `m ≥ 2`, `d = 2m + 1` and `P_d(z) = 1 + z + ⋯ + z^{d-1}`. For `0 ≤ Q < 1` and `B ≥ 0`
the factors `P_d(y q^r)` of the product `G_d(y; q)` are uniformly close to `1` on
`|q| ≤ Q`, `|y| ≤ B`: there are nonnegative `M_r` with `∑ M_r < ∞` and
`|P_d(y q^r) - 1| ≤ M_r`. One may take `M_r = ∑_{s=1}^{d-1} (B Q^r)^s`, a finite sum of
geometric sequences in `r`.

## Main results

* `HigherDyson3.exists_summable_bound_cyclotomicSum_sub_one`: the uniform summable bound.

## Implementation notes

The factors are indexed by `r : ℕ` standing for the exponent `r + 1 ≥ 1`, matching
`HigherDyson3.GProduct`; so `M r` here is the paper's `M_{r+1}`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset

namespace HigherDyson3

/-- `P_d(z) - 1 = ∑_{s=1}^{d-1} z^s`, hence `‖P_d(z) - 1‖ ≤ ∑_{s=1}^{d-1} ‖z‖^s`. -/
private theorem norm_cyclotomicSum_sub_one_le (m : ℕ) (z : ℂ) :
    ‖cyclotomicSum m z - 1‖ ≤ ∑ s ∈ range (2 * m), ‖z‖ ^ (s + 1) := by
  have h : cyclotomicSum m z - 1 = ∑ s ∈ range (2 * m), z ^ (s + 1) := by
    rw [cyclotomicSum, sum_range_succ']; simp
  rw [h]
  refine (norm_sum_le _ _).trans_eq ?_
  simp [norm_pow]

/-- **Uniform bound on the factors.** For `0 ≤ Q < 1` and `B ≥ 0` there is a summable
sequence of nonnegative reals `M r` bounding `‖P_d(y q^{r+1}) - 1‖` for all `‖q‖ ≤ Q` and
`‖y‖ ≤ B`. -/
theorem exists_summable_bound_cyclotomicSum_sub_one {m : ℕ} (_hm : 2 ≤ m) {Q B : ℝ}
    (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (hB : 0 ≤ B) :
    ∃ M : ℕ → ℝ, (∀ r, 0 ≤ M r) ∧ Summable M ∧
      ∀ r : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q → ∀ y : ℂ, ‖y‖ ≤ B →
        ‖cyclotomicSum m (y * q ^ (r + 1)) - 1‖ ≤ M r := by
  refine ⟨fun r => ∑ s ∈ range (2 * m), (B * Q ^ (r + 1)) ^ (s + 1), fun r => ?_, ?_, ?_⟩
  · exact sum_nonneg fun s _ => by positivity
  · refine summable_sum fun s _ => ?_
    have hg : Summable fun r : ℕ => (Q ^ (s + 1)) ^ r :=
      summable_geometric_of_lt_one (by positivity)
        (pow_lt_one₀ hQ0 hQ1 (Nat.succ_ne_zero s))
    convert hg.mul_left ((B * Q) ^ (s + 1)) using 1
    funext r
    ring
  · intro r q hq y hy
    refine (norm_cyclotomicSum_sub_one_le m _).trans (sum_le_sum fun s _ => ?_)
    gcongr
    rw [norm_mul, norm_pow]
    gcongr

end HigherDyson3

end
