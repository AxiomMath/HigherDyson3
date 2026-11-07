/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.DoubleSeriesNormal

/-!
# The periodization as a double series

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. Off the divisor, the
periodization `ℰ_{m,x}(τ,w)` is the sum over `ℤ × ℕ` of the double summands
`ℰ^{dbl}_{n,k}(τ,w)`, an absolutely summable family.

For fixed `n`, expanding the seed `𝒢_{d,x}(q^n u; q)` and multiplying by
`x^{-2n} q^{mn²} u^{2mn}` gives `∑_{k ≥ 0} ℰ^{dbl}_{n,k}(τ,w)`; absolute summability on `ℤ × ℕ`
(`HigherDyson3.doubleSeriesNormal_exists_majorant` on the singleton `{(τ,w)}`) turns the
iterated sum into the sum over the product.

## Main results

* `HigherDyson3.periodization_double`: `ℰ_{m,x}(τ,w) = ∑_{(n,k) ∈ ℤ × ℕ} ℰ^{dbl}_{n,k}(τ,w)`,
  with `(‖ℰ^{dbl}_{n,k}(τ,w)‖)_{(n,k)}` summable.
-/

public section

namespace HigherDyson3

/-- The `n`-th summand of the periodization is the sum over `k` of the double summands. -/
lemma periodizationDouble_summand (m : ℕ) (α : ℚ) (n : ℤ) (τ w : ℂ) :
    e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
        seed m (e α) (e τ ^ n * e w) (e τ) =
      ∑' k : ℕ, doubleSummand m α n k τ w := by
  have hq : e τ ≠ 0 := Complex.exp_ne_zero _
  unfold seed
  rw [← mul_assoc, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [doubleSummand]
  rw [zpow_add₀ hq, zpow_add₀ hq, zpow_natCast, ← zpow_natCast (e τ) (k ^ 2)]
  push_cast
  ring

/-- **The periodization as a double series.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`x = e(α)` and `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, the family `(ℰ^{dbl}_{n,k}(τ,w))_{(n,k) ∈ ℤ × ℕ}` is
absolutely summable and `ℰ_{m,x}(τ,w) = ∑_{(n,k) ∈ ℤ × ℕ} ℰ^{dbl}_{n,k}(τ,w)`. -/
theorem periodization_double {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor α) :
    Summable (fun i : ℤ × ℕ => ‖doubleSummand m α i.1 i.2 τ w‖) ∧
      periodization m α τ w = ∑' i : ℤ × ℕ, doubleSummand m α i.1 i.2 τ w := by
  obtain ⟨M, hM, -, hle⟩ := doubleSeriesNormal_exists_majorant hm α hα0 hα1 {(τ, w)}
    isCompact_singleton (Set.singleton_subset_iff.mpr hτw)
  have hnorm : Summable (fun i : ℤ × ℕ => ‖doubleSummand m α i.1 i.2 τ w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => hle i (τ, w) (Set.mem_singleton _)) hM
  refine ⟨hnorm, ?_⟩
  rw [hnorm.of_norm.tsum_prod' hnorm.of_norm.prod_factor]
  exact tsum_congr fun n => periodizationDouble_summand m α n τ w

end HigherDyson3
