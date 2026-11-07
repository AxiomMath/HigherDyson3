/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Zeros of the linear denominators

For `x = e(α)`, `q = e(τ)` and `u = e(w)`, the factor `1 - x u q^j` vanishes exactly on the
divisor components `L_{-j,b}`, `b ∈ ℤ`.
-/

public section

noncomputable section

open Complex

namespace HigherDyson3

/-- `e(α) e(w) e(τ)^j = e(α + w + jτ)`. -/
private lemma divisorChar_e_mul (α w τ : ℂ) (j : ℤ) :
    e α * e w * e τ ^ j = e (α + w + j * τ) := by
  simp only [e]
  rw [← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- **Zeros of the linear denominators.** For `0 ≤ α < 1`, `x = e(α)`, `(τ, w) ∈ ℍ × ℂ`,
`q = e(τ)`, `u = e(w)` and `j ∈ ℤ`, one has `1 - x u q^j = 0` if and only if
`(τ, w) ∈ L_{-j,b}` for some `b ∈ ℤ`. -/
theorem divisor_char (α : ℚ) (_hα0 : 0 ≤ α) (_hα1 : α < 1) {τ w : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (j : ℤ) :
    1 - e α * e w * e τ ^ j = 0 ↔ ∃ b : ℤ, (τ, w) ∈ divisorComponent α (-j) b := by
  rw [sub_eq_zero, eq_comm, divisorChar_e_mul, e, Complex.exp_eq_one_iff]
  simp only [divisorComponent, Set.mem_ofPred_eq, upperHalfPlaneSet] at hτ ⊢
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, hτ, ?_⟩, fun ⟨b, _, hb⟩ ↦ ⟨b, ?_⟩⟩
  · push_cast
    linear_combination mul_left_cancel₀ hπ (hn.trans (mul_comm _ _))
  · rw [hb]
    push_cast
    ring

end HigherDyson3
