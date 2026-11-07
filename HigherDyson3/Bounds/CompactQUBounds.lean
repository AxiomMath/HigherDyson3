/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Uniform bounds for `q = e(τ)` and `u = e(w)` on compact sets

For `(τ, w)` ranging over a compact subset `S` of `ℍ × ℂ`, the moduli `|q| = |e(τ)|` and
`|u| = |e(w)|` are bounded away from `0` and `∞`, and moreover `|q|` is bounded away from `1`:
there are `0 < Q₀ ≤ Q < 1` and `0 < a₀ ≤ b₀` with `Q₀ ≤ |e(τ)| ≤ Q` and `a₀ ≤ |e(w)| ≤ b₀`
on `S`.

Since `|e(z)| = exp(-2π Im z)`, both moduli are continuous and positive functions on `S`,
and the first is `< 1` on `ℍ × ℂ`. On a compact set each attains its minimum and maximum,
and the maximum of `|e(τ)|`, being attained at a point of `S ⊆ ℍ × ℂ`, is `< 1`.

## Main results

* `HigherDyson3.compact_q_u_bounds`: the uniform bounds above.
-/

public section

namespace HigherDyson3

/-- `e` is continuous. -/
lemma compactQUBounds_continuous_e : Continuous e := by
  unfold e; fun_prop

/-- `|e(z)|` is positive. -/
lemma compactQUBounds_norm_e_pos (z : ℂ) : 0 < ‖e z‖ := by
  unfold e; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)

/-- `|e(z)| < 1` for `z` in the upper half-plane. -/
lemma compactQUBounds_norm_e_lt_one {z : ℂ} (hz : 0 < z.im) : ‖e z‖ < 1 := by
  unfold e
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [Real.pi_pos]

/-- On a compact subset `S` of `ℍ × ℂ`, the moduli `|e(τ)|` and `|e(w)|` are bounded above
and below by positive constants, and `|e(τ)|` is bounded above by a constant `< 1`. -/
theorem compact_q_u_bounds (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∃ Q₀ Q a₀ b₀ : ℝ, 0 < Q₀ ∧ Q₀ ≤ Q ∧ Q < 1 ∧ 0 < a₀ ∧ a₀ ≤ b₀ ∧
      ∀ p ∈ S, Q₀ ≤ ‖e p.1‖ ∧ ‖e p.1‖ ≤ Q ∧ a₀ ≤ ‖e p.2‖ ∧ ‖e p.2‖ ≤ b₀ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1 / 2, 1 / 2, 1, 1, by norm_num, le_rfl, by norm_num, one_pos, le_rfl,
      fun p hp => hp.elim⟩
  have h1 : ContinuousOn (fun p : ℂ × ℂ => ‖e p.1‖) S :=
    (continuous_norm.comp (compactQUBounds_continuous_e.comp continuous_fst)).continuousOn
  have h2 : ContinuousOn (fun p : ℂ × ℂ => ‖e p.2‖) S :=
    (continuous_norm.comp (compactQUBounds_continuous_e.comp continuous_snd)).continuousOn
  obtain ⟨p₀, hp₀, hmin₁⟩ := hS.exists_isMinOn hne h1
  obtain ⟨p₁, hp₁, hmax₁⟩ := hS.exists_isMaxOn hne h1
  obtain ⟨p₂, hp₂, hmin₂⟩ := hS.exists_isMinOn hne h2
  obtain ⟨p₃, hp₃, hmax₂⟩ := hS.exists_isMaxOn hne h2
  refine ⟨‖e p₀.1‖, ‖e p₁.1‖, ‖e p₂.2‖, ‖e p₃.2‖, compactQUBounds_norm_e_pos _,
    hmin₁ hp₁, compactQUBounds_norm_e_lt_one (hSH hp₁), compactQUBounds_norm_e_pos _,
    hmin₂ hp₃, fun p hp => ⟨hmin₁ hp, hmax₁ hp, hmin₂ hp, hmax₂ hp⟩⟩

end HigherDyson3
