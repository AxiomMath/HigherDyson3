/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.KernelNormal

/-!
# Splitting off the singular summand of the kernel

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)` and `a ∈ ℤ`. Off the divisor `𝒟_x`, the
kernel `𝒦_{m,x}` is its regular part `𝒦^{(a)}_{m,x}` plus the summand `n = -a`,
`x^{2a} q^{ma²} u^{-2ma} / (1 - x u q^{-a})`.

The series of `𝒦_{m,x}` converges absolutely at a point off `𝒟_x` (normal convergence on the
compact singleton, `HigherDyson3.kernelNormal_exists`), so it is the sum of its term at
`n = -a` and of the sum over `n ≠ -a`.

## Main results

* `HigherDyson3.kernel_split`:
  `𝒦_{m,x} = 𝒦^{(a)}_{m,x} + x^{2a} q^{ma²} u^{-2ma} / (1 - x u q^{-a})` on `(ℍ × ℂ) \ 𝒟_x`.
-/

public section

namespace HigherDyson3

/-- The summands of the kernel are summable at a point of `(ℍ × ℂ) \ 𝒟_x`. -/
theorem kernelSplit_summable {m : ℕ} (hm : 1 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hp : (τ, w) ∈ halfPlaneProd \ divisor α) :
    Summable fun n : ℤ => e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
      e w ^ (2 * (m : ℤ) * n) / (1 - e α * e w * e τ ^ n) := by
  obtain ⟨M, hMs, -, hM⟩ := kernelNormal_exists hm α hα0 hα1 {(τ, w)} isCompact_singleton
    (Set.singleton_subset_iff.mpr hp)
  exact Summable.of_norm_bounded hMs fun n => hM n (τ, w) rfl

/-- A summable series over `ℤ` is its sum over `n ≠ c` plus its term at `c`. -/
theorem kernelSplit_tsum_eq {f : ℤ → ℂ} (hf : Summable f) (c : ℤ) :
    ∑' n, f n = ∑' n : {n : ℤ // n ≠ c}, f n + f c := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {n : ℤ | n ≠ c}]
  congr 1
  have hc : ({n : ℤ | n ≠ c}ᶜ : Set ℤ) = {c} := by
    ext n; simp
  rw [hc]
  exact tsum_singleton c f

/-- **Splitting off the singular summand.** For an integer `m ≥ 2`, `α ∈ ℚ` with
`0 ≤ α < 1`, `x = e(α)`, `a ∈ ℤ` and `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, with `q = e(τ)` and
`u = e(w)`, one has
`𝒦_{m,x}(τ, w) = 𝒦^{(a)}_{m,x}(τ, w) + x^{2a} q^{ma²} u^{-2ma} / (1 - x u q^{-a})`. -/
theorem kernel_split (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) (a : ℤ)
    {τ w : ℂ} (hp : (τ, w) ∈ halfPlaneProd \ divisor α) :
    kernel m α τ w = kernelRegular m α a τ w +
      e α ^ (2 * a) * e τ ^ ((m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) /
        (1 - e α * e w * e τ ^ (-a)) := by
  have hs := kernelSplit_summable (m := m) (by omega) α hα0 hα1 hp
  unfold kernel kernelRegular
  rw [kernelSplit_tsum_eq hs (-a), show -2 * -a = 2 * a by ring,
    show (m : ℤ) * (-a) ^ 2 = m * a ^ 2 by ring, show 2 * (m : ℤ) * -a = -2 * m * a by ring]

end HigherDyson3
