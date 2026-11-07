/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.ThetaTermMajorant

/-!
# Normal convergence of the theta series

For integers `m ≥ 1` and `ℓ ≥ 0`, the series defining `ϑ_{m,ℓ}(τ, w)` converges normally on
compact subsets of `ℍ × ℂ`. Writing `r_j = ℓ + 2mj`, `q = e(τ)` and `u = e(w)`, the `j`-th
summand equals `e(ℓ²τ/(4m)) q^{mj² + ℓj} u^{r_j}`, and `‖e(ℓ²τ/(4m))‖ ≤ 1` when `Im τ > 0`, so
the summands are dominated by the theta-type terms of `HigherDyson3.thetaTermMajorant_exists`.

## Main results

* `HigherDyson3.thetaNormal_exists`: there is a summable `M : ℤ → ℝ` dominating the `j`-th
  summand of `HigherDyson3.theta` uniformly on a compact subset of `ℍ × ℂ`.
* `HigherDyson3.theta_normal`: the sum over `j` of the suprema over such a set is finite.

## Implementation notes

The hypothesis `ℓ < 2m` of the source is not needed and is dropped.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

private lemma thetaNormal_e_zpow (z : ℂ) (n : ℤ) : e z ^ n = e (n * z) := by
  unfold e
  rw [← Complex.exp_int_mul]
  ring_nf

private lemma thetaNormal_e_add (a b : ℂ) : e (a + b) = e a * e b := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

/-- The `j`-th summand of `theta` factors as `e(ℓ²τ/(4m)) q^{mj² + ℓj} u^{ℓ + 2mj}`. -/
private lemma thetaNormal_summand_eq {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (j : ℤ) (τ w : ℂ) :
    e (((ℓ : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m)) * e (((ℓ : ℂ) + 2 * m * j) * w) =
      e ((ℓ : ℂ) ^ 2 * τ / (4 * m)) *
        (e τ ^ ((m : ℤ) * j ^ 2 + (ℓ : ℤ) * j) * e w ^ ((ℓ : ℤ) + 2 * (m : ℤ) * j)) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [thetaNormal_e_zpow, ← thetaNormal_e_add]
  congr 1
  push_cast
  field_simp
  ring

/-- `‖e(ℓ²τ/(4m))‖ ≤ 1` for `Im τ ≥ 0`. -/
private lemma thetaNormal_norm_e_le_one {m ℓ : ℕ} {τ : ℂ} (hτ : 0 ≤ τ.im) :
    ‖e ((ℓ : ℂ) ^ 2 * τ / (4 * m))‖ ≤ 1 := by
  unfold e
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have h : (2 * Real.pi * Complex.I * ((ℓ : ℂ) ^ 2 * τ / (4 * m))).re =
      -(2 * Real.pi * ((ℓ : ℝ) ^ 2 / (4 * m)) * τ.im) := by
    rw [show ((ℓ : ℂ) ^ 2 * τ / (4 * m)) = (((ℓ : ℝ) ^ 2 / (4 * m) : ℝ) : ℂ) * τ by
      push_cast
      ring]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [h, neg_nonpos]
  have := Real.pi_pos
  positivity

/-- A summable majorant for the summands of `theta`, uniform over a compact subset of
`ℍ × ℂ`. -/
theorem thetaNormal_exists {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (S : Set (ℂ × ℂ))
    (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∃ M : ℤ → ℝ, Summable M ∧ (∀ j, 0 ≤ M j) ∧ ∀ j : ℤ, ∀ p ∈ S,
      ‖e (((ℓ : ℂ) + 2 * m * j) ^ 2 * p.1 / (4 * m)) * e (((ℓ : ℂ) + 2 * m * j) * p.2)‖ ≤
        M j := by
  obtain ⟨M, hM, hM0, hle⟩ :=
    thetaTermMajorant_exists (m := (m : ℤ)) (by exact_mod_cast hm) (ℓ : ℤ) S hS hSH
  refine ⟨M, hM, hM0, fun j p hp => ?_⟩
  rw [thetaNormal_summand_eq hm, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (thetaNormal_norm_e_le_one (hSH hp).le)).trans (hle j p hp)

/-- The series defining `theta` converges normally on compact subsets of `ℍ × ℂ`: the sum
over `j` of the suprema over `S` of the `j`-th summand is finite. -/
theorem theta_normal {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSH : S ⊆ halfPlaneProd) :
    ∑' j : ℤ, ⨆ p ∈ S, (‖e (((ℓ : ℂ) + 2 * m * j) ^ 2 * p.1 / (4 * m)) *
      e (((ℓ : ℂ) + 2 * m * j) * p.2)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ := thetaNormal_exists hm ℓ S hS hSH
  calc ∑' j : ℤ, ⨆ p ∈ S, (‖e (((ℓ : ℂ) + 2 * m * j) ^ 2 * p.1 / (4 * m)) *
        e (((ℓ : ℂ) + 2 * m * j) * p.2)‖₊ : ℝ≥0∞)
      ≤ ∑' j : ℤ, ENNReal.ofReal (M j) := by
        refine ENNReal.tsum_le_tsum fun j => iSup₂_le fun p hp => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle j p hp)
    _ = ENNReal.ofReal (∑' j, M j) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
