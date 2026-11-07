/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCLeading
public import HigherDyson3.ThetaCoeff.HEqC

/-!
# Leading term of the theta coefficients `h_{m,ℓ,x}`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ ∩ [0, 1)`, `0 ≤ ℓ < 2m` and `c_ℓ = 1 + ℓ - ℓ²/(4m)`.
As `Im τ → ∞`,
`h_{m,ℓ,x}(τ) = e(ℓα/m) x^{ℓ-2} e(c_ℓ τ) + O(|e((c_ℓ + 2)τ)|)`.

Writing `p = e(-ℓ²τ/(4m))` and `q = e(τ)`, one has
`h_{m,ℓ,x} = e(ℓα/m) p C_{m,ℓ,x}`, `p q^{ℓ+1} = e(c_ℓ τ)` and `|p| |q|^{ℓ+3} = |e((c_ℓ+2)τ)|`;
since `|e(ℓα/m)| = 1`, the estimate follows from the leading term of `C_{m,ℓ,x}`.

## Main results

* `HigherDyson3.exists_norm_thetaCoeffH_sub_le`: the estimate
  `|h_{m,ℓ,x}(τ) - e(ℓα/m) x^{ℓ-2} e(c_ℓ τ)| ≤ C |e((c_ℓ+2)τ)|` for `Im τ ≥ T`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

namespace HigherDyson3

/-- `e(z + w) = e(z) e(w)`. -/
private lemma e_add' (z w : ℂ) : e (z + w) = e z * e w := by
  unfold e; rw [← Complex.exp_add]; ring_nf

/-- `e(n z) = e(z)^n`. -/
private lemma e_natMul' (n : ℕ) (z : ℂ) : e (n * z) = e z ^ n := by
  unfold e; rw [← Complex.exp_nat_mul]; ring_nf

/-- **Leading term of `h_{m,ℓ,x}`.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `0 ≤ ℓ < 2m` and
`c_ℓ = 1 + ℓ - ℓ²/(4m)` there are `C, T > 0` with
`|h_{m,ℓ,x}(τ) - e(ℓα/m) x^{ℓ-2} e(c_ℓ τ)| ≤ C |e((c_ℓ + 2)τ)|` for all `τ ∈ ℍ` with
`Im τ ≥ T`, where `x = e(α)`. -/
theorem exists_norm_thetaCoeffH_sub_le {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖thetaCoeffH m ℓ α τ -
          e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) * e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m)) * τ)‖ ≤
        C * ‖e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m) + 2) * τ)‖ := by
  obtain ⟨C, T, hC, hT, hbound⟩ := exists_norm_coeffC_sub_le hm hα0 hα1 hℓ
  refine ⟨C, T, hC, hT, fun τ hτ hTτ => ?_⟩
  set p : ℂ := e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) with hp
  have h1 : e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m)) * τ) = p * e τ ^ (ℓ + 1) := by
    rw [hp, ← e_natMul', ← e_add']; congr 1; push_cast; ring
  have h2 : e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m) + 2) * τ) = p * e τ ^ (ℓ + 3) := by
    rw [hp, ← e_natMul', ← e_add']; congr 1; push_cast; ring
  have hu : ‖e (ℓ * α / m)‖ = 1 := by
    have := coeffCNormal_norm_e_ofReal ((ℓ : ℝ) * α / m)
    exact_mod_cast this
  rw [thetaCoeffH_eq_coeffC hm hα0 hα1 hℓ hτ, h1, h2, ← hp]
  have : e (ℓ * α / m) * p * coeffC m ℓ α τ - e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) *
      (p * e τ ^ (ℓ + 1)) =
      e (ℓ * α / m) * p * (coeffC m ℓ α τ - e α ^ ((ℓ : ℤ) - 2) * e τ ^ (ℓ + 1)) := by ring
  rw [this, norm_mul, norm_mul, hu, one_mul, norm_mul, norm_pow]
  calc ‖p‖ * ‖coeffC m ℓ α τ - e α ^ ((ℓ : ℤ) - 2) * e τ ^ (ℓ + 1)‖
      ≤ ‖p‖ * (C * ‖e τ‖ ^ (ℓ + 3)) :=
        mul_le_mul_of_nonneg_left (hbound τ hτ hTτ) (norm_nonneg _)
    _ = C * (‖p‖ * ‖e τ‖ ^ (ℓ + 3)) := by ring

end HigherDyson3
