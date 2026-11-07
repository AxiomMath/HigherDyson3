/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.ThetaTermMajorant

/-!
# Normal convergence of the twisted theta series

Let `m ≥ 1`, `ℓ ≥ 0` be integers and `α ∈ ℚ`. The series defining
`HigherDyson3.twistedTheta m ℓ α`, namely
`∑_{j ∈ ℤ} e(α)^{-2j} e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}`, converges normally on compact
subsets of `ℍ × ℂ`. Since `|e(α)| = 1`, the `j`-th summand has the same absolute value as
the theta-type term `e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}`, so this follows from
`HigherDyson3.thetaTermMajorant_exists`.

## Main results

* `HigherDyson3.twistedThetaNormal_exists`: there is a summable `M : ℤ → ℝ` dominating the
  `j`-th summand uniformly on a compact `S ⊆ ℍ × ℂ`.
* `HigherDyson3.twisted_theta_normal`: the sum over `j` of the suprema over `S` of the
  summands is finite.

## Implementation notes

The source assumes `m ≥ 2`, `0 ≤ ℓ < 2m` and `0 ≤ α < 1`; only `m ≥ 1` is needed, since
`|e(α)| = 1` for every real `α`.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- `|e(α)| = 1` for rational `α`. -/
private lemma twistedThetaNormal_norm_e_rat (α : ℚ) : ‖e (α : ℂ)‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- A summable majorant for the summands of the twisted theta series, uniform over a compact
subset of `ℍ × ℂ`. -/
theorem twistedThetaNormal_exists {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (α : ℚ) (S : Set (ℂ × ℂ))
    (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∃ M : ℤ → ℝ, Summable M ∧ (∀ j, 0 ≤ M j) ∧ ∀ j : ℤ, ∀ p ∈ S,
      ‖e α ^ (-2 * j) * e p.1 ^ ((m : ℤ) * j ^ 2 + ℓ * j) * e p.2 ^ ((ℓ : ℤ) + 2 * m * j)‖
        ≤ M j := by
  obtain ⟨M, hM, hM0, hle⟩ :=
    thetaTermMajorant_exists (m := (m : ℤ)) (by exact_mod_cast hm) (ℓ : ℤ) S hS hSH
  refine ⟨M, hM, hM0, fun j p hp => ?_⟩
  rw [mul_assoc, norm_mul, norm_zpow, twistedThetaNormal_norm_e_rat, one_zpow, one_mul]
  exact hle j p hp

/-- **Normal convergence of the twisted theta series.** For `m ≥ 1`, `ℓ ≥ 0`, `α ∈ ℚ` and a
compact `S ⊆ ℍ × ℂ`, the sum over `j ∈ ℤ` of the suprema over `S` of
`|e(α)^{-2j} e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}|` is finite. -/
theorem twisted_theta_normal {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (α : ℚ) (S : Set (ℂ × ℂ))
    (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∑' j : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * j) * e p.1 ^ ((m : ℤ) * j ^ 2 + ℓ * j) *
      e p.2 ^ ((ℓ : ℤ) + 2 * m * j)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ := twistedThetaNormal_exists hm ℓ α S hS hSH
  calc ∑' j : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * j) * e p.1 ^ ((m : ℤ) * j ^ 2 + ℓ * j) *
        e p.2 ^ ((ℓ : ℤ) + 2 * m * j)‖₊ : ℝ≥0∞)
      ≤ ∑' j : ℤ, ENNReal.ofReal (M j) := by
        refine ENNReal.tsum_le_tsum fun j => iSup₂_le fun p hp => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle j p hp)
    _ = ENNReal.ofReal (∑' j, M j) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
