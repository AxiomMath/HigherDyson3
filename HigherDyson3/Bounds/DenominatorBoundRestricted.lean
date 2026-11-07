/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.DenominatorTail

/-!
# Denominator bound on a set of indices

Let `x = e(α)` with `α` real, let `S` be a compact subset of `ℍ × ℂ` and `I ⊆ ℤ`. Write
`q = e(τ)` and `u = e(w)`. If `1 - x u q^j ≠ 0` for all `(τ, w) ∈ S` and all `j ∈ I`, then
the reciprocals `|1 - x u q^j|⁻¹` are bounded on `S`, uniformly in `j ∈ I`.

For `|j|` large the bound `2` comes from `HigherDyson3.denominator_tail`; each of the finitely
many remaining `j ∈ I` contributes the maximum over the compact set `S` of the continuous
function `(τ, w) ↦ |1 - x u q^j|⁻¹`.

## Main results

* `HigherDyson3.denominator_bound_restricted`: the uniform bound above.

## Implementation notes

The statement is proved for every real `α`: only `|e(α)| = 1` is used, so the hypotheses
`α ∈ ℚ` and `0 ≤ α < 1` of the source are not needed.
-/

public section

namespace HigherDyson3

/-- For fixed `j`, the map `(τ, w) ↦ 1 - e(α) e(w) e(τ)^j` is continuous. -/
lemma denominatorBoundRestricted_continuous (α : ℝ) (j : ℤ) :
    Continuous fun p : ℂ × ℂ => 1 - e (α : ℂ) * e p.2 * e p.1 ^ j :=
  continuous_const.sub ((continuous_const.mul (compactQUBounds_continuous_e.comp
    continuous_snd)).mul ((compactQUBounds_continuous_e.comp continuous_fst).zpow₀ j
      fun _ => Or.inl (Complex.exp_ne_zero _)))

/-- Let `S ⊆ ℍ × ℂ` be compact and `I ⊆ ℤ`, and suppose that, with `x = e(α)`, `q = e(τ)`
and `u = e(w)`, `1 - x u q^j ≠ 0` for all `(τ, w) ∈ S` and `j ∈ I`. Then there is `A > 0`
with `|1 - x u q^j|⁻¹ ≤ A` for all `(τ, w) ∈ S` and all `j ∈ I`. -/
theorem denominator_bound_restricted (α : ℝ) (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSH : S ⊆ halfPlaneProd) (I : Set ℤ)
    (hI : ∀ p ∈ S, ∀ j ∈ I, 1 - e (α : ℂ) * e p.2 * e p.1 ^ j ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ S, ∀ j ∈ I, ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖⁻¹ ≤ A := by
  obtain ⟨J, hJ⟩ := denominator_tail α S hS hSH
  have hB : ∀ j : ℤ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ p ∈ S, j ∈ I → ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖⁻¹ ≤ B := by
    intro j
    by_cases hj : j ∈ I
    · have hcont : ContinuousOn
          (fun p : ℂ × ℂ => ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖⁻¹) S :=
        ((denominatorBoundRestricted_continuous α j).norm.continuousOn).inv₀
          fun p hp => norm_ne_zero_iff.mpr (hI p hp j hj)
      obtain ⟨B, hB⟩ := (hS.image_of_continuousOn hcont).bddAbove
      refine ⟨max B 0, le_max_right _ _, fun p hp _ => ?_⟩
      exact (hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun _ _ h => absurd h hj⟩
  choose B hB0 hB using hB
  refine ⟨2 + ∑ j ∈ Finset.Ioo (-(J : ℤ)) J, B j, by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.Ioo (-(J : ℤ)) J) => hB0 j
    linarith, fun p hp j hj => ?_⟩
  have hsum : 0 ≤ ∑ j ∈ Finset.Ioo (-(J : ℤ)) J, B j :=
    Finset.sum_nonneg fun j _ => hB0 j
  rcases le_or_gt (J : ℤ) |j| with hjJ | hjJ
  · have h := hJ p hp j hjJ
    have : ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  · have hmem : j ∈ Finset.Ioo (-(J : ℤ)) J := by
      rw [abs_lt] at hjJ
      exact Finset.mem_Ioo.mpr hjJ
    have := Finset.single_le_sum (fun i _ => hB0 i) hmem
    linarith [hB j p hp hj]

end HigherDyson3
