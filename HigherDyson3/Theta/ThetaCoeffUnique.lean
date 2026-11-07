/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Theta.ThetaNormal

/-!
# Uniqueness of theta coefficients

For an integer `m ≥ 1` and `τ ∈ ℍ`, the theta series `ϑ_{m,0}(τ, ·), …, ϑ_{m,2m-1}(τ, ·)` are
linearly independent: if `∑_{ℓ < 2m} c_ℓ ϑ_{m,ℓ}(τ, w) = 0` for every `w ∈ ℂ`, then every
`c_ℓ` vanishes.

The proof extracts `c_{ℓ₀}` by integrating against `e(-ℓ₀ t)` over `t ∈ [0, 1]`. Writing
`r_j = ℓ + 2mj`, the `j`-th summand of `ϑ_{m,ℓ}(τ, t) e(-ℓ₀ t)` is
`e(r_j²τ/(4m)) e((r_j - ℓ₀) t)`, whose integral is `e(ℓ₀²τ/(4m))` when `ℓ = ℓ₀` and `j = 0`
and zero otherwise. Termwise integration is justified because the summands have constant
norm `‖e(r_j²τ/(4m))‖` on the real line, and these are summable by
`HigherDyson3.thetaNormal_exists`.

## Main results

* `HigherDyson3.theta_coeff_unique`: the uniqueness statement above.

## Implementation notes

The source assumes `m ≥ 2`; the proof only needs `m ≥ 1`.
-/

public section

open MeasureTheory Set

namespace HigherDyson3

private lemma thetaCoeffUnique_e_add (a b : ℂ) : e (a + b) = e a * e b := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

private lemma thetaCoeffUnique_continuous_e : Continuous e := by
  unfold e
  fun_prop

private lemma thetaCoeffUnique_norm_e_ofReal (x : ℝ) : ‖e (x : ℂ)‖ = 1 := by
  unfold e
  rw [show 2 * (Real.pi : ℂ) * Complex.I * x = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring, Complex.norm_exp_ofReal_mul_I]

/-- `∫₀¹ e(kt) dt` is `1` for `k = 0` and `0` for every other integer `k`. -/
private lemma thetaCoeffUnique_integral_e_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, e ((k : ℂ) * t) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp [e]
  · have hc : 2 * (Real.pi : ℂ) * Complex.I * k ≠ 0 := by simp [hk, Real.pi_ne_zero]
    simp only [e]
    simp_rw [← mul_assoc]
    rw [integral_exp_mul_complex (a := 0) (b := 1) hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * k * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one]
      have : 2 * (Real.pi : ℂ) * Complex.I * k = k * (2 * Real.pi * Complex.I) := by ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [h1]
    simp

private lemma thetaCoeffUnique_summable_norm {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ : 0 < τ.im)
    (ℓ : ℕ) : Summable fun j : ℤ => ‖e (((ℓ : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m))‖ := by
  obtain ⟨M, hM, hM0, hle⟩ := thetaNormal_exists hm ℓ {(τ, 0)} isCompact_singleton
    (by simpa [halfPlaneProd] using hτ)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) hM
  simpa [e] using hle j (τ, 0) rfl

private lemma thetaCoeffUnique_norm_summand (m ℓ ℓ₀ : ℕ) (j : ℤ) (z : ℂ) (t : ℝ) :
    ‖z * e (((ℓ : ℂ) + 2 * m * j) * t) * e (-(ℓ₀ : ℂ) * t)‖ = ‖z‖ := by
  have h₁ : ((ℓ : ℂ) + 2 * m * j) * t = (((ℓ + 2 * m * j : ℝ)) * t : ℝ) := by
    push_cast
    ring
  have h₂ : -(ℓ₀ : ℂ) * t = ((-(ℓ₀ : ℝ) * t : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [norm_mul, h₁, h₂, thetaCoeffUnique_norm_e_ofReal, mul_one]

private lemma thetaCoeffUnique_integral_summand (m ℓ ℓ₀ : ℕ) (j : ℤ) (z : ℂ) :
    ∫ t in (0 : ℝ)..1, z * e (((ℓ : ℂ) + 2 * m * j) * t) * e (-(ℓ₀ : ℂ) * t) =
      z * if (ℓ : ℤ) + 2 * m * j - ℓ₀ = 0 then 1 else 0 := by
  rw [← thetaCoeffUnique_integral_e_int, ← intervalIntegral.integral_const_mul]
  congr 1
  ext t
  simp only [mul_assoc, ← thetaCoeffUnique_e_add]
  congr 2
  push_cast
  ring

private lemma thetaCoeffUnique_ne {m ℓ ℓ₀ : ℕ} {j : ℤ} (hℓ : ℓ < 2 * m) (hℓ₀ : ℓ₀ < 2 * m)
    (hj : j ≠ 0) : (ℓ : ℤ) + 2 * m * j - ℓ₀ ≠ 0 := by
  rcases lt_or_gt_of_ne hj with hj | hj
  · have : (2 * m : ℤ) * j ≤ -(2 * m) := by nlinarith
    omega
  · have : (2 * m : ℤ) ≤ 2 * m * j := by nlinarith
    omega

private lemma thetaCoeffUnique_sum_ite {m ℓ₀ : ℕ} (hℓ₀ : ℓ₀ < 2 * m) (c : ℕ → ℂ)
    (a : ℕ → ℤ → ℂ) (j : ℤ) :
    ∑ ℓ ∈ Finset.range (2 * m), c ℓ * (a ℓ j * if (ℓ : ℤ) + 2 * m * j - ℓ₀ = 0 then 1 else 0) =
      if j = 0 then c ℓ₀ * a ℓ₀ 0 else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [ite_eq_left rfl, Finset.sum_eq_single ℓ₀]
    · simp
    · intro ℓ _ hℓ
      have : (ℓ : ℤ) - ℓ₀ ≠ 0 := by omega
      simp [this]
    · simp [hℓ₀]
  · rw [ite_eq_right hj]
    refine Finset.sum_eq_zero fun ℓ hℓ => ?_
    simp [thetaCoeffUnique_ne (Finset.mem_range.mp hℓ) hℓ₀ hj]

/-- **Uniqueness of theta coefficients.** For `m ≥ 1` and `τ ∈ ℍ`, if
`∑_{ℓ=0}^{2m-1} c_ℓ ϑ_{m,ℓ}(τ, w) = 0` for all `w ∈ ℂ`, then `c_ℓ = 0` for every `ℓ < 2m`. -/
theorem theta_coeff_unique {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ : 0 < τ.im) (c : ℕ → ℂ)
    (h : ∀ w : ℂ, ∑ ℓ ∈ Finset.range (2 * m), c ℓ * theta m ℓ τ w = 0) :
    ∀ ℓ < 2 * m, c ℓ = 0 := by
  intro ℓ₀ hℓ₀
  set a : ℕ → ℤ → ℂ := fun ℓ j => e (((ℓ : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m)) with ha
  set φ : ℕ → ℤ → ℝ → ℂ := fun ℓ j t =>
    a ℓ j * e (((ℓ : ℂ) + 2 * m * j) * t) * e (-(ℓ₀ : ℂ) * t) with hφ
  have hK : ∀ ℓ, Summable fun j => ‖a ℓ j‖ := thetaCoeffUnique_summable_norm hm hτ
  have hφnorm : ∀ ℓ j t, ‖φ ℓ j t‖ = ‖a ℓ j‖ := fun ℓ j t =>
    thetaCoeffUnique_norm_summand m ℓ ℓ₀ j (a ℓ j) t
  have hφcont : ∀ ℓ j, Continuous (φ ℓ j) := fun ℓ j => by
    have := thetaCoeffUnique_continuous_e
    simp only [hφ]
    fun_prop
  set F : ℤ → ℝ → ℂ := fun j t => ∑ ℓ ∈ Finset.range (2 * m), c ℓ * φ ℓ j t with hF
  set μ : Measure ℝ := volume.restrict (Ioc 0 1) with hμ
  have hFint : ∀ j, Integrable (F j) μ := fun j =>
    (continuous_finsetSum _ fun ℓ _ => continuous_const.mul (hφcont ℓ j)).integrableOn_Ioc
  have hFnorm : Summable fun j => ∫ t, ‖F j t‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (summable_sum (s := Finset.range (2 * m)) fun ℓ _ => (hK ℓ).mul_left ‖c ℓ‖)
    calc ∫ t, ‖F j t‖ ∂μ ≤ ∫ _, ∑ ℓ ∈ Finset.range (2 * m), ‖c ℓ‖ * ‖a ℓ j‖ ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
            (ae_of_all _ fun t => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun ℓ _ => by rw [norm_mul, hφnorm]))
      _ = _ := by simp [hμ]
  have hzero : ∀ t : ℝ, ∑' j, F j t = 0 := by
    intro t
    simp only [hF]
    rw [Summable.tsum_finsetSum fun ℓ _ =>
      (Summable.of_norm (by simpa [hφnorm] using hK ℓ)).mul_left (c ℓ)]
    calc ∑ ℓ ∈ Finset.range (2 * m), ∑' j, c ℓ * φ ℓ j t
        = (∑ ℓ ∈ Finset.range (2 * m), c ℓ * theta m ℓ τ t) * e (-(ℓ₀ : ℂ) * t) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [tsum_mul_left, theta, mul_assoc, ← tsum_mul_right]
      _ = 0 := by rw [h t, zero_mul]
  have hFj : ∀ j, ∫ t, F j t ∂μ = if j = 0 then c ℓ₀ * a ℓ₀ 0 else 0 := by
    intro j
    refine Eq.trans ?_ (thetaCoeffUnique_sum_ite hℓ₀ c a j)
    simp only [hF, hμ]
    rw [integral_finsetSum (Finset.range (2 * m)) (f := fun ℓ t => c ℓ * φ ℓ j t) fun ℓ _ =>
      (continuous_const.mul (hφcont ℓ j)).integrableOn_Ioc]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
    exact congrArg (c ℓ * ·) (thetaCoeffUnique_integral_summand m ℓ ℓ₀ j (a ℓ j))
  have hj0 : ∀ j ≠ 0, ∫ t, F j t ∂μ = 0 := fun j hj => (hFj j).trans (ite_eq_right hj)
  have key : c ℓ₀ * a ℓ₀ 0 = 0 := by
    rw [← (hFj 0).trans (ite_eq_left rfl),
      ← tsum_eq_single (L := SummationFilter.unconditional ℤ) 0 hj0,
      integral_tsum_of_summable_integral_norm hFint hFnorm]
    simp [hzero]
  exact (mul_eq_zero.mp key).resolve_right (by simp [ha, e, Complex.exp_ne_zero])

end HigherDyson3
