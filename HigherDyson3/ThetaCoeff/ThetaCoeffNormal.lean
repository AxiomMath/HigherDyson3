/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCNormal

/-!
# Normal convergence of the series defining the theta coefficients `h_{m,ℓ,x}`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ ∩ [0, 1)`, `0 ≤ ℓ < 2m` and `S ⊆ ℍ` compact. With
`q = e(τ)` and `q^{-ℓ²/(4m)} = e(-ℓ²τ/(4m))`,
`∑_{k ≥ 1} sup_{τ ∈ S} |e(ℓα/m) x^{ℓ-2} q^{-ℓ²/(4m)} g_{k,x}(q) ∑_{s=1}^{k} …| < ∞`.

Since `α` and `ℓα/m` are real, `|e(ℓα/m)| = |x^{ℓ-2}| = 1`, and `τ ↦ |e(-ℓ²τ/(4m))|` is
continuous, hence bounded on `S` by some `M`. The `k`-th supremum is therefore at most `M`
times the `k`-th summand of the majorant of `HigherDyson3.coeffCNormal_exists`.

## Main results

* `HigherDyson3.thetaCoeff_normal`: the sum over `k` of the suprema over `S` is finite.

## Implementation notes

The sum runs over all `k : ℕ`; the summand for `k = 0` is an empty sum, so this is the sum
over `k ≥ 1`. The supremum is taken in `ℝ≥0∞`.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- `e` is continuous. -/
private lemma thetaCoeffNormal_continuous_e : Continuous e := by
  unfold e
  fun_prop

/-- **Normal convergence of the coefficient series of `h_{m,ℓ,x}`.** For `m ≥ 2`, `α ∈ ℚ`
with `0 ≤ α < 1`, `0 ≤ ℓ < 2m` and a compact `S ⊆ ℍ`, with `x = e(α)` and `q = e(τ)`,
`∑_{k ≥ 1} sup_{τ ∈ S} |e(ℓα/m) x^{ℓ-2} e(-ℓ²τ/(4m)) g_{k,x}(q)
∑_{s=1}^{k} x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}| < ∞`. -/
theorem thetaCoeff_normal {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) {ℓ : ℕ}
    (hℓ : ℓ < 2 * m) (S : Set ℂ) (hS : IsCompact S) (hSH : S ⊆ upperHalfPlaneSet) :
    ∑' k : ℕ, ⨆ τ ∈ S, (‖e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) *
      e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
      (gTail m (e α) k (e τ) *
        ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
          e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s))‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨u, hu, hu0, hle⟩ := coeffCNormal_exists hm hα0 hα1 hℓ S hS hSH
  have hcont : Continuous fun τ : ℂ => ‖e (-((ℓ : ℂ) ^ 2) * τ / (4 * m))‖ :=
    (thetaCoeffNormal_continuous_e.comp (by fun_prop)).norm
  obtain ⟨M, hM⟩ := (hS.image hcont).isBounded.bddAbove
  have h1 : ‖e (ℓ * α / m)‖ = 1 := by
    rw [show (ℓ * α / m : ℂ) = ((ℓ * α / m : ℝ) : ℂ) by push_cast; ring]
    exact coeffCNormal_norm_e_ofReal _
  have h2 : ‖e α ^ ((ℓ : ℤ) - 2)‖ = 1 := by
    rw [norm_zpow, show ‖e (α : ℂ)‖ = 1 by exact_mod_cast coeffCNormal_norm_e_ofReal α,
      one_zpow]
  calc _ ≤ ∑' k : ℕ, ENNReal.ofReal (max M 0 * u k) := by
        refine ENNReal.tsum_le_tsum fun k => iSup₂_le fun τ hτ => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, norm_mul, norm_mul, h1, h2, one_mul, one_mul]
        exact mul_le_mul ((hM ⟨τ, hτ, rfl⟩).trans (le_max_left _ _)) (hle k τ hτ)
          (norm_nonneg _) (le_max_right _ _)
    _ = ENNReal.ofReal (∑' k, max M 0 * u k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (le_max_right _ _) (hu0 k))
          (hu.mul_left _)).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
