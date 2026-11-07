/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Local finiteness of the divisor components

A compact subset of `ℍ × ℂ` meets only finitely many of the components `L_{a,b}`.
-/

public section

noncomputable section

open Complex

namespace HigherDyson3

/-- A set of integers bounded in absolute value by a real number is finite. -/
private lemma divisorLocallyFinite_finite_abs_le (R : ℝ) :
    {z : ℤ | |(z : ℝ)| ≤ R}.Finite := by
  refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_
  have hz' : |(z : ℝ)| ≤ R := hz
  rw [abs_le] at hz'
  constructor
  · exact_mod_cast (by linarith [Int.le_ceil R] : (-(⌈R⌉ : ℝ)) ≤ z)
  · exact_mod_cast hz'.2.trans (Int.le_ceil R)

/-- **Local finiteness of the components.** For `0 ≤ α < 1` and a compact
`S ⊆ ℍ × ℂ`, only finitely many `(a, b) ∈ ℤ²` have `L_{a,b} ∩ S ≠ ∅`. -/
theorem divisor_locally_finite (α : ℚ) (_hα0 : 0 ≤ α) (_hα1 : α < 1) {S : Set (ℂ × ℂ)}
    (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    {ab : ℤ × ℤ | (divisorComponent α ab.1 ab.2 ∩ S).Nonempty}.Finite := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨p₀, hp₀S, hmin⟩ :=
    hS.exists_isMinOn hne (Complex.continuous_im.comp continuous_fst).continuousOn
  have ht₀ : 0 < p₀.1.im := hSH hp₀S
  set t₀ := p₀.1.im
  obtain ⟨M, hM⟩ := hS.isBounded.exists_norm_le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p₀ hp₀S)
  set R : ℝ := M / t₀ + M + |(α : ℝ)| + M / t₀ * M
  refine ((divisorLocallyFinite_finite_abs_le R).prod
    (divisorLocallyFinite_finite_abs_le R)).subset ?_
  rintro ⟨a, b⟩ ⟨⟨τ, w⟩, ⟨-, hw⟩, hpS⟩
  have hτM : ‖τ‖ ≤ M := (norm_fst_le (τ, w)).trans (hM _ hpS)
  have hwM : ‖w‖ ≤ M := (norm_snd_le (τ, w)).trans (hM _ hpS)
  have htτ : t₀ ≤ τ.im := hmin hpS
  have hw' : w = -(α : ℂ) + a * τ + b := hw
  have hτre : |τ.re| ≤ M := (abs_re_le_norm τ).trans hτM
  have hwre : |w.re| ≤ M := (abs_re_le_norm w).trans hwM
  have ha : |(a : ℝ)| ≤ M / t₀ := by
    rw [le_div_iff₀ ht₀]
    calc |(a : ℝ)| * t₀ ≤ |(a : ℝ)| * τ.im := by gcongr
      _ = |w.im| := by simp [hw', abs_mul, abs_of_pos (ht₀.trans_le htτ)]
      _ ≤ M := (abs_im_le_norm w).trans hwM
  have hMt : 0 ≤ M / t₀ := div_nonneg hM0 ht₀.le
  have hb : |(b : ℝ)| ≤ M + |(α : ℝ)| + M / t₀ * M := by
    have hre : w.re = -(α : ℝ) + a * τ.re + b := by simp [hw']
    rw [show (b : ℝ) = w.re + α - a * τ.re by linarith]
    calc |w.re + α - a * τ.re| ≤ |w.re| + |(α : ℝ)| + |(a : ℝ)| * |τ.re| := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ M + |(α : ℝ)| + M / t₀ * M := by gcongr
  have := abs_nonneg (α : ℝ)
  exact ⟨show |(a : ℝ)| ≤ R by nlinarith, show |(b : ℝ)| ≤ R by linarith⟩

end HigherDyson3
