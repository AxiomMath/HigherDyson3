/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.KernelResidue

/-!
# Appell–Lerch kernels

The Appell–Lerch kernel `A_{m,β}(τ,w) = -∑_{n ∈ ℤ} q^{mn²} u^{2mn} / (1 - e^{-2πiβ} q^n u)` of
[AOS, (4.5)], and its relation to the twisted kernel `𝒦_{m,x}`: with `x = e(α)` and
`β_x = -α - α/m`, `𝒦_{m,x}(τ, w + α/m) = -A_{m,β_x}(τ, w)` [AOS, Remark 4.6(2)].
-/

public section

namespace HigherDyson3

/-- The Appell–Lerch kernel `A_{m,β}(τ,w) = -∑_{n ∈ ℤ} q^{mn²} u^{2mn} / (1 - e(-β) q^n u)`,
`q = e(τ)`, `u = e(w)` [AOS, (4.5)]. -/
noncomputable def appellLerch (m : ℕ) (β : ℚ) (τ w : ℂ) : ℂ :=
  -∑' n : ℤ, e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) / (1 - e (-β) * e τ ^ n * e w)

theorem appellLerch_def (m : ℕ) (β : ℚ) (τ w : ℂ) :
    appellLerch m β τ w =
      -∑' n : ℤ, e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) /
        (1 - e (-β) * e τ ^ n * e w) := (rfl)

/-- **The twisted kernel in standard coordinates** [AOS, Remark 4.6(2)]. For `m ≥ 1`,
`x = e(α)` and `β_x = -α - α/m`, `𝒦_{m,x}(τ, w + α/m) = -A_{m,β_x}(τ, w)`. -/
theorem kernel_add_div_eq_neg_appellLerch {m : ℕ} (hm : 1 ≤ m) (α : ℚ) (τ w : ℂ) :
    kernel m α τ (w + α / m) = -appellLerch m (-α - α / m) τ w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [appellLerch, neg_neg, kernel]
  refine tsum_congr fun n => ?_
  have h1 : e (w + α / m) ^ (2 * (m : ℤ) * n) = e α ^ (2 * n) * e w ^ (2 * (m : ℤ) * n) := by
    rw [kernelResidue_e_zpow, kernelResidue_e_zpow, kernelResidue_e_zpow, kernelResidue_e_mul]
    congr 1
    push_cast
    field_simp
    ring
  have h2 : e α * e (w + α / m) = e (-((-α - α / m : ℚ) : ℂ)) * e w := by
    rw [kernelResidue_e_mul, kernelResidue_e_mul]
    congr 1
    push_cast
    ring
  have hx : e α ^ (-2 * n) * e α ^ (2 * n) = 1 := by
    rw [← zpow_add₀ (show e (α : ℂ) ≠ 0 from Complex.exp_ne_zero _)]
    simp
  rw [h1, h2]
  have : e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * (e α ^ (2 * n) * e w ^ (2 * (m : ℤ) * n)) =
      e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) := by
    linear_combination (e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n)) * hx
  rw [this]
  ring_nf

end HigherDyson3
