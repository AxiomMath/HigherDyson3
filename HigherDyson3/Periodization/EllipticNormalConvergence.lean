/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.DoubleSeriesNormal

/-!
# Normal convergence of the periodization

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. For every compact
`S ⊆ (ℍ × ℂ) \ 𝒟_x`, with `q = e(τ)` and `u = e(w)`,
`∑_{n ∈ ℤ} sup_{(τ,w) ∈ S} |x^{-2n} q^{mn²} u^{2mn} 𝒢_{d,x}(q^n u; q)| < ∞`.

Expanding the seed, the `n`-th summand of the periodization is the sum over `k ≥ 0` of the
double summands `ℰ^{dbl}_{n,k}(τ,w)`. By the triangle inequality its supremum over `S` is at
most `∑_k sup_S |ℰ^{dbl}_{n,k}|`, and summing over `n` gives the sum over `ℤ × ℕ` of the
suprema of the double summands, which is finite by `HigherDyson3.double_series_normal`.

## Main results

* `HigherDyson3.ellipticNormalConvergence_summand_eq_tsum`: the `n`-th summand of the
  periodization is `∑_{k ≥ 0} ℰ^{dbl}_{n,k}(τ,w)`.
* `HigherDyson3.elliptic_normal_convergence`: the sum over `n ∈ ℤ` of the suprema over `S`
  of the summands of the periodization is finite.

## Implementation notes

As in `HigherDyson3.double_series_normal`, the supremum is taken in `ℝ≥0∞`, so the statement
is the literal finiteness of the sum of suprema. The expansion of the summand holds for all
`(τ, w)`: off the divisor no denominator vanishes, and on it both sides use the convention
`a / 0 = 0` termwise.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- The `n`-th summand `x^{-2n} q^{mn²} u^{2mn} 𝒢_{d,x}(q^n u; q)` of the periodization is the
sum over `k ≥ 0` of the double summands `ℰ^{dbl}_{n,k}(τ,w)`. -/
theorem ellipticNormalConvergence_summand_eq_tsum (m : ℕ) (α : ℚ) (n : ℤ) (τ w : ℂ) :
    e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
        seed m (e α) (e τ ^ n * e w) (e τ) =
      ∑' k : ℕ, doubleSummand m α n k τ w := by
  have hq : e τ ≠ 0 := by unfold e; exact Complex.exp_ne_zero _
  unfold seed
  rw [← mul_assoc, ← tsum_mul_left]
  congr 1
  funext k
  unfold doubleSummand
  rw [zpow_add₀ hq, zpow_add₀ hq, ← Nat.cast_pow, zpow_natCast, zpow_natCast]
  have : e α * (e τ ^ n * e w) * e τ ^ k = e α * e w * (e τ ^ n * e τ ^ k) := by ring
  rw [this]
  ring

/-- **Normal convergence of the periodization.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`x = e(α)` and a compact `S ⊆ (ℍ × ℂ) \ 𝒟_x`, with `q = e(τ)` and `u = e(w)`,
`∑_{n ∈ ℤ} sup_{(τ,w) ∈ S} |x^{-2n} q^{mn²} u^{2mn} 𝒢_{d,x}(q^n u; q)| < ∞`. -/
theorem elliptic_normal_convergence {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
      e p.2 ^ (2 * (m : ℤ) * n) * seed m (e α) (e p.1 ^ n * e p.2) (e p.1)‖₊ : ℝ≥0∞) < ∞ := by
  calc ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * n) * seed m (e α) (e p.1 ^ n * e p.2) (e p.1)‖₊ : ℝ≥0∞)
      ≤ ∑' n : ℤ, ∑' k : ℕ, ⨆ p ∈ S, (‖doubleSummand m α n k p.1 p.2‖₊ : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun n => iSup₂_le fun p hp => ?_
        rw [ellipticNormalConvergence_summand_eq_tsum, ← enorm_eq_nnnorm]
        refine (enorm_tsum_le_tsum_enorm).trans (ENNReal.tsum_le_tsum fun k => ?_)
        rw [enorm_eq_nnnorm]
        exact le_iSup₂_of_le (f := fun p (_ : p ∈ S) =>
          (‖doubleSummand m α n k p.1 p.2‖₊ : ℝ≥0∞)) p hp le_rfl
    _ = ∑' i : ℤ × ℕ, ⨆ p ∈ S, (‖doubleSummand m α i.1 i.2 p.1 p.2‖₊ : ℝ≥0∞) :=
        ENNReal.tsum_prod.symm
    _ < ∞ := double_series_normal hm α hα0 hα1 S hS hSD

end HigherDyson3
