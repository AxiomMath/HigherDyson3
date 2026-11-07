/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.FinitePart.ThetaTwistedLaw

/-!
# The untwisted elliptic law of the translated finite part

For `m ≥ 2`, `x = e(α)` and `(τ, w + α/m) ∉ 𝒟_x` with `τ ∈ ℍ`, the translate
`w ↦ ℰ^{fin}_{m,x}(τ, w + α/m)` of the finite part obeys, for all `a, b ∈ ℤ`, with
`q = e(τ)` and `u = e(w)`,
`ℰ^{fin}_{m,x}(τ, w + α/m + aτ + b) = q^{-ma²} u^{-2ma} ℰ^{fin}_{m,x}(τ, w + α/m)`.

It follows from the twisted law at `w' = w + α/m`: the factor `e(α/m)^{-2ma} = x^{-2a}`
coming from `e(w')^{-2ma}` cancels the twist `x^{2a}`.

## Main results

* `HigherDyson3.finitePart_untwisted_law`: the untwisted elliptic law of the translated
  finite part.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

noncomputable section

namespace HigherDyson3

private lemma thetaUntwistedLaw_e_add (z w : ℂ) : e (z + w) = e z * e w := by
  unfold e; rw [← Complex.exp_add]; ring_nf

private lemma thetaUntwistedLaw_e_zpow (z : ℂ) (k : ℤ) : e z ^ k = e (k * z) := by
  unfold e; rw [← Complex.exp_int_mul]; ring_nf

/-- **Untwisted elliptic law** of the translated finite part: for `a, b ∈ ℤ`,
`ℰ^{fin}_{m,x}(τ, w + α/m + aτ + b) = q^{-ma²} u^{-2ma} ℰ^{fin}_{m,x}(τ, w + α/m)`, where
`q = e(τ)` and `u = e(w)`. -/
theorem finitePart_untwisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w + (α : ℂ) / m) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    finitePart m α τ (w + (α : ℂ) / m + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ (w + (α : ℂ) / m) := by
  rw [finitePart_twisted_law hm hα0 hα1 hτw a b]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have key : e α ^ (2 * a) * e (w + (α : ℂ) / m) ^ (-2 * (m : ℤ) * a) =
      e w ^ (-2 * (m : ℤ) * a) := by
    simp only [thetaUntwistedLaw_e_zpow, ← thetaUntwistedLaw_e_add]
    congr 1
    push_cast
    field_simp
    ring
  calc e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e (w + (α : ℂ) / m) ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ (w + (α : ℂ) / m)
      = e τ ^ (-(m : ℤ) * a ^ 2) *
          (e α ^ (2 * a) * e (w + (α : ℂ) / m) ^ (-2 * (m : ℤ) * a)) *
          finitePart m α τ (w + (α : ℂ) / m) := by ring
    _ = _ := by rw [key]

end HigherDyson3
