/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.DenominatorBoundRestricted
public import HigherDyson3.Divisor.DivisorChar

/-!
# Uniform denominator bound off the divisor

Let `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. On every compact subset `S` of
`(ℍ × ℂ) \ 𝒟_x` the reciprocals `|1 - x u q^j|⁻¹`, with `q = e(τ)` and `u = e(w)`, are bounded
uniformly in `(τ, w) ∈ S` and `j ∈ ℤ`.

## Main results

* `HigherDyson3.denominator_bound`: the uniform bound above.
-/

public section

namespace HigherDyson3

/-- **Uniform denominator bound off the divisor.** Let `α ∈ ℚ` with `0 ≤ α < 1` and
`x = e(α)`. For every compact `S ⊆ (ℍ × ℂ) \ 𝒟_x` there is `A > 0` with
`|1 - x u q^j|⁻¹ ≤ A` for all `(τ, w) ∈ S`, `q = e(τ)`, `u = e(w)`, and all `j ∈ ℤ`. -/
theorem denominator_bound (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) (S : Set (ℂ × ℂ))
    (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ S, ∀ j : ℤ, ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖⁻¹ ≤ A := by
  have hcast : ((α : ℝ) : ℂ) = (α : ℂ) := Complex.ofReal_ratCast α
  obtain ⟨A, hA0, hA⟩ := denominator_bound_restricted (α : ℝ) S hS
    (hSD.trans Set.sdiff_subset) Set.univ (by
      intro p hp j _ h
      rw [hcast] at h
      obtain ⟨hpH, hpD⟩ := hSD hp
      obtain ⟨b, hb⟩ := (divisor_char α hα0 hα1 (τ := p.1) (w := p.2) hpH j).mp h
      exact hpD (Set.mem_iUnion₂.mpr ⟨-j, b, hb⟩))
  refine ⟨A, hA0, fun p hp j => ?_⟩
  simpa [hcast] using hA p hp j (Set.mem_univ j)

end HigherDyson3
