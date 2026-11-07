/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.KernelResidue

/-!
# Removing a constant twist

If `Y(τ, w + 1) = Y(τ, w)` and `Y(τ, w + τ) = x² q^{-m} u^{-2m} Y(τ, w)` with `x = e(α)`, then the
translate `Ỹ(τ, w) = Y(τ, w + α/m)` satisfies the untwisted index-`m` law
`Ỹ(τ, w + 1) = Ỹ(τ, w)`, `Ỹ(τ, w + τ) = q^{-m} u^{-2m} Ỹ(τ, w)` [AOS, §4.3].
-/

public section

namespace HigherDyson3

/-- **Removing a constant twist** [AOS, §4.3]. -/
theorem untwisted_law_of_twisted_law {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {Y : ℂ → ℂ → ℂ} {τ : ℂ}
    (h1 : ∀ w, Y τ (w + 1) = Y τ w)
    (hτ : ∀ w, Y τ (w + τ) = e α ^ 2 * e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * Y τ w) (w : ℂ) :
    Y τ (w + 1 + α / m) = Y τ (w + α / m) ∧
      Y τ (w + τ + α / m) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * Y τ (w + α / m) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  refine ⟨by rw [add_right_comm, h1], ?_⟩
  rw [add_right_comm, hτ]
  have h2 : e (w + α / m) ^ (-2 * (m : ℤ)) = (e α ^ 2)⁻¹ * e w ^ (-2 * (m : ℤ)) := by
    rw [kernelResidue_e_zpow, kernelResidue_e_zpow, ← zpow_natCast, ← zpow_neg,
      kernelResidue_e_zpow, kernelResidue_e_mul]
    congr 1
    push_cast
    field_simp
    ring
  rw [h2]
  have hxe : e (α : ℂ) ≠ 0 := Complex.exp_ne_zero _
  field_simp

end HigherDyson3
