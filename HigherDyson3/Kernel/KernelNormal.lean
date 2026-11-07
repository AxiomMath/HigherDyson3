/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.DenominatorBound
public import HigherDyson3.Bounds.ThetaTermMajorant

/-!
# Normal convergence of the kernel series

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. The series
`𝒦_{m,x}(τ, w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} / (1 - x u q^n)`, with `q = e(τ)` and
`u = e(w)`, converges normally on compact subsets of `(ℍ × ℂ) \ 𝒟_x`.

On a compact `S ⊆ (ℍ × ℂ) \ 𝒟_x` the reciprocals `|1 - x u q^n|⁻¹` are bounded by a constant
`A_S` uniformly in `n` (`HigherDyson3.denominator_bound`). Since `|x| = 1`, the `n`-th summand
is at most `A_S |q^{mn²} u^{2mn}|` on `S`, and these theta-type terms have summable suprema
(`HigherDyson3.thetaTermMajorant_exists` with `ℓ = 0`).

## Main results

* `HigherDyson3.kernelNormal_exists`: there is a summable `M : ℤ → ℝ` dominating the `n`-th
  summand of `HigherDyson3.kernel` uniformly on a compact subset of `(ℍ × ℂ) \ 𝒟_x`.
* `HigherDyson3.kernel_normal`: the sum over `n` of the suprema over such a set is finite.

## Implementation notes

The results are stated under the weaker hypothesis `m ≥ 1`, which is all the estimate uses.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- `‖e(α)‖ = 1` for rational `α`. -/
private lemma kernelNormal_norm_e_rat (α : ℚ) : ‖e (α : ℂ)‖ = 1 := by
  have hcast : ((α : ℝ) : ℂ) = (α : ℂ) := Complex.ofReal_ratCast α
  unfold e
  rw [← hcast, Complex.norm_exp]
  simp

/-- A summable majorant for the summands of `kernel`, uniform over a compact subset of
`(ℍ × ℂ) \ 𝒟_x`. -/
theorem kernelNormal_exists {m : ℕ} (hm : 1 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∃ M : ℤ → ℝ, Summable M ∧ (∀ n, 0 ≤ M n) ∧ ∀ n : ℤ, ∀ p ∈ S,
      ‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) /
        (1 - e α * e p.2 * e p.1 ^ n)‖ ≤ M n := by
  obtain ⟨A, hA0, hA⟩ := denominator_bound α hα0 hα1 S hS hSD
  obtain ⟨M, hMs, hM0, hM⟩ := thetaTermMajorant_exists (m := (m : ℤ)) (by omega) 0 S hS
    (hSD.trans Set.sdiff_subset)
  refine ⟨fun n => A * M n, hMs.mul_left A, fun n => mul_nonneg hA0.le (hM0 n),
    fun n p hp => ?_⟩
  have hAn := hA p hp n
  have hMn := hM n p hp
  simp only [zero_mul, add_zero, zero_add] at hMn
  have hx : ‖e (α : ℂ) ^ (-2 * n)‖ = 1 := by
    rw [norm_zpow, kernelNormal_norm_e_rat, one_zpow]
  rw [norm_div, norm_mul, norm_mul, hx, one_mul, div_eq_mul_inv, ← norm_mul]
  change _ ≤ A * M n
  rw [mul_comm A]
  exact mul_le_mul hMn hAn (by positivity) (hM0 _)

/-- **Normal convergence of the kernel.** For an integer `m ≥ 1`, `α ∈ ℚ` with `0 ≤ α < 1`
and a compact `S ⊆ (ℍ × ℂ) \ 𝒟_x`, `x = e(α)`, the sum over `n` of the suprema over `S` of
the `n`-th summand of `𝒦_{m,x}` is finite. -/
theorem kernel_normal {m : ℕ} (hm : 1 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
      e p.2 ^ (2 * (m : ℤ) * n) / (1 - e α * e p.2 * e p.1 ^ n)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ := kernelNormal_exists hm α hα0 hα1 S hS hSD
  calc ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * n) / (1 - e α * e p.2 * e p.1 ^ n)‖₊ : ℝ≥0∞)
      ≤ ∑' n : ℤ, ENNReal.ofReal (M n) := by
        refine ENNReal.tsum_le_tsum fun n => iSup₂_le fun p hp => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle n p hp)
    _ = ENNReal.ofReal (∑' n, M n) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
