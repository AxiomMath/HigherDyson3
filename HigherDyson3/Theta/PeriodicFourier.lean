/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.KernelResidue

/-!
# Fourier expansion of entire periodic functions

An entire function `G` with `G(w + 1) = G(w)` has the absolutely convergent expansion
`G(w) = ∑_{r ∈ ℤ} c_r e(r w)` with `c_r = ∫_0^1 G(s) e(-rs) ds`; moreover
`∫_0^1 G(s + z) e(-r(s + z)) ds = c_r` for every `z ∈ ℂ` (contour shift). This is the Fourier
expansion used in the proof of the theta decomposition [AOS, Lemma 4.1].
-/

public section

namespace HigherDyson3

open MeasureTheory intervalIntegral Complex

/-- The Fourier coefficient `c_r = ∫_0^1 G(s) e(-rs) ds` of a `1`-periodic function. -/
noncomputable def periodicCoeff (G : ℂ → ℂ) (r : ℤ) : ℂ :=
  ∫ s in (0 : ℝ)..1, G s * e (-(r * s))

theorem periodicCoeff_def (G : ℂ → ℂ) (r : ℤ) :
    periodicCoeff G r = ∫ s in (0 : ℝ)..1, G s * e (-(r * s)) := (rfl)

theorem e_intCast (n : ℤ) : e (n : ℂ) = 1 := by
  rw [e, show 2 * (Real.pi : ℂ) * I * n = n * (2 * Real.pi * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem e_add (z y : ℂ) : e (z + y) = e z * e y := (kernelResidue_e_mul z y).symm

theorem norm_e (z : ℂ) : ‖e z‖ = Real.exp (-2 * Real.pi * z.im) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem differentiable_e : Differentiable ℂ e := fun z => by unfold e; fun_prop

/-- **Contour shift.** For an entire `1`-periodic `G` and `r ∈ ℤ`,
`∫_0^1 G(s + z) e(-r(s + z)) ds = ∫_0^1 G(s) e(-rs) ds` for every `z ∈ ℂ`. -/
theorem integral_shift_eq_periodicCoeff {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hp : ∀ w, G (w + 1) = G w) (r : ℤ) (z : ℂ) :
    ∫ s in (0 : ℝ)..1, G (s + z) * e (-(r * (s + z))) = periodicCoeff G r := by
  set φ : ℂ → ℂ := fun w => G w * e (-(r * w)) with hφ
  have hφd : Differentiable ℂ φ := hG.mul (differentiable_e.comp (by fun_prop))
  have hφp : ∀ w, φ (w + 1) = φ w := by
    intro w
    simp only [hφ, hp]
    congr 1
    rw [show -((r : ℂ) * (w + 1)) = -(r * w) + ((-r : ℤ) : ℂ) by push_cast; ring, e_add,
      e_intCast, mul_one]
  -- imaginary shift
  have himag : ∀ b : ℝ, ∫ x in (0 : ℝ)..1, φ (x + b * I) = ∫ x in (0 : ℝ)..1, φ x := by
    intro b
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn φ 0 (1 + b * I)
      hφd.differentiableOn
    simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero,
      Complex.ofReal_zero, zero_mul, Complex.ofReal_one] at h
    have hcancel : ∫ y in (0 : ℝ)..b, φ (1 + y * I) = ∫ y in (0 : ℝ)..b, φ (y * I) := by
      refine integral_congr fun y _ => ?_
      rw [add_comm, hφp]
    rw [hcancel, add_sub_cancel_right] at h
    exact (sub_eq_zero.mp h).symm
  -- real shift
  have hreal : ∀ (a b : ℝ), ∫ x in (0 : ℝ)..1, φ (x + a + b * I) =
      ∫ x in (0 : ℝ)..1, φ (x + b * I) := by
    intro a b
    set ψ : ℝ → ℂ := fun x => φ (x + b * I) with hψ
    have hψp : Function.Periodic ψ 1 := by
      intro x
      simp only [hψ]
      push_cast
      rw [show (x : ℂ) + 1 + b * I = x + b * I + 1 by ring, hφp]
    have h1 : ∫ x in (0 : ℝ)..1, φ (x + a + b * I) = ∫ x in (0 : ℝ)..1, ψ (x + a) := by
      refine integral_congr fun x _ => ?_
      simp only [hψ]; push_cast; ring_nf
    rw [h1, intervalIntegral.integral_comp_add_right ψ a, zero_add, add_comm 1 a,
      hψp.intervalIntegral_add_eq a 0, zero_add]
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  calc ∫ s in (0 : ℝ)..1, G (s + z) * e (-(r * (s + z)))
      = ∫ s in (0 : ℝ)..1, φ (s + z.re + z.im * I) := by
        refine integral_congr fun s _ => ?_
        have : (s : ℂ) + z = s + z.re + z.im * I := by rw [add_assoc, Complex.re_add_im]
        simp only [hφ, this]
    _ = ∫ s in (0 : ℝ)..1, φ s := by rw [hreal, himag]
    _ = periodicCoeff G r := rfl

/-- **Exponential decay of the Fourier coefficients.** For an entire `1`-periodic `G` and every
`t ∈ ℝ` there is `M` with `‖c_r‖ ≤ M exp(2π r t)` for all `r ∈ ℤ`. -/
theorem exists_norm_periodicCoeff_le {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hp : ∀ w, G (w + 1) = G w) (t : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℤ, ‖periodicCoeff G r‖ ≤ M * Real.exp (2 * Real.pi * r * t) := by
  have hcont : Continuous fun s : ℝ => G (s + t * I) :=
    hG.continuous.comp (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun r => ?_⟩
  rw [← integral_shift_eq_periodicCoeff hG hp r (t * I)]
  have hb : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖G (s + t * I) * e (-(r * (s + t * I)))‖ ≤
      max M 0 * Real.exp (2 * Real.pi * r * t) := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le, hs.2⟩
    rw [norm_mul, norm_e]
    have him : (-((r : ℂ) * ((s : ℂ) + t * I))).im = -(r * t) := by
      simp [Complex.mul_im]
    rw [him]
    have : Real.exp (-2 * Real.pi * -(r * t)) = Real.exp (2 * Real.pi * r * t) := by ring_nf
    rw [this]
    exact mul_le_mul_of_nonneg_right ((hM s hs').trans (le_max_left _ _)) (Real.exp_pos _).le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

/-- The Fourier series of an entire `1`-periodic function converges absolutely on every
horizontal line: `∑_r ‖c_r‖ exp(-2π r t) < ∞`. -/
theorem summable_norm_periodicCoeff_mul_exp {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hp : ∀ w, G (w + 1) = G w) (t : ℝ) :
    Summable fun r : ℤ => ‖periodicCoeff G r‖ * Real.exp (-2 * Real.pi * r * t) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_norm_periodicCoeff_le hG hp (t - 1)
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_norm_periodicCoeff_le hG hp (t + 1)
  set ρ : ℝ := Real.exp (-2 * Real.pi) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρ, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hgeom : Summable fun n : ℕ => (M₁ + M₂) * ρ ^ n :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hgeom
    have h := hM₁ n
    calc ‖periodicCoeff G n‖ * Real.exp (-2 * Real.pi * ((n : ℤ) : ℝ) * t)
        ≤ M₁ * Real.exp (2 * Real.pi * ((n : ℤ) : ℝ) * (t - 1)) *
            Real.exp (-2 * Real.pi * ((n : ℤ) : ℝ) * t) := by gcongr
      _ = M₁ * ρ ^ n := by
          rw [hρ, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ (M₁ + M₂) * ρ ^ n := by gcongr; linarith
  · refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hgeom
    have h := hM₂ (-(n : ℤ))
    calc ‖periodicCoeff G (-(n : ℤ))‖ * Real.exp (-2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ) * t)
        ≤ M₂ * Real.exp (2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ) * (t + 1)) *
            Real.exp (-2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ) * t) := by gcongr
      _ = M₂ * ρ ^ n := by
          rw [hρ, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; push_cast; ring_nf
      _ ≤ (M₁ + M₂) * ρ ^ n := by gcongr; linarith

/-- **Fourier expansion of an entire periodic function.** For an entire `G` with
`G(w + 1) = G(w)`, `G(w) = ∑_{r ∈ ℤ} c_r e(r w)` for every `w ∈ ℂ`, with
`c_r = ∫_0^1 G(s) e(-rs) ds`. -/
theorem hasSum_periodicCoeff_mul_e {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hp : ∀ w, G (w + 1) = G w) (w : ℂ) :
    HasSum (fun r : ℤ => periodicCoeff G r * e (r * w)) (G w) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  set t : ℝ := w.im with ht
  set f : ℝ → ℂ := fun s => G (s + t * I) with hf
  have hfc : Continuous f := hG.continuous.comp (by fun_prop)
  have hf01 : f 0 = f (0 + 1) := by
    simp only [hf]; push_cast; rw [zero_add, zero_add, add_comm (1 : ℂ), hp]
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco 1 0 f, AddCircle.liftIco_continuous hf01 hfc.continuousOn⟩ with hF
  -- the Fourier coefficients of the horizontal slice
  have hcoeff : ∀ n : ℤ, fourierCoeff F n = periodicCoeff G n * e (n * (t * I)) := by
    intro n
    have h1 : fourierCoeff F n = fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) one_pos) f n :=
      fourierCoeff_liftIco_eq f n
    rw [h1, fourierCoeffOn_eq_integral, ← integral_shift_eq_periodicCoeff hG hp n (t * I)]
    simp only [zero_add, sub_zero, div_one, one_smul, smul_eq_mul, fourier_coe_apply,
      Complex.ofReal_one]
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hf]
    have : e (-(n * (x + t * I))) * e (n * (t * I)) =
        cexp (2 * Real.pi * I * ((-n : ℤ) : ℂ) * x) := by
      rw [← e_add, e]; congr 1; push_cast; ring
    rw [mul_assoc (G _), this, mul_comm]
  have hsum : Summable (fourierCoeff F) := by
    refine Summable.of_norm ?_
    refine (summable_norm_periodicCoeff_mul_exp hG hp t).congr fun n => ?_
    rw [hcoeff, norm_mul, norm_e]
    congr 2
    simp [Complex.mul_im]
    ring
  -- evaluate at the fractional part of `Re w`
  set s₁ : ℝ := Int.fract w.re with hs₁
  have hs₁mem : s₁ ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    rw [zero_add]; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have h := has_pointwise_sum_fourier_series_of_summable hsum (s₁ : AddCircle (1 : ℝ))
  have hFval : F (s₁ : AddCircle (1 : ℝ)) = G w := by
    simp only [hF, ContinuousMap.coe_mk]
    rw [AddCircle.liftIco_coe_apply hs₁mem]
    simp only [hf, hs₁, Int.fract]
    have hw : ((w.re - ⌊w.re⌋ : ℝ) : ℂ) + t * I = w - (⌊w.re⌋ : ℤ) * 1 := by
      apply Complex.ext <;> simp [ht]
    rw [hw]
    exact (show Function.Periodic G 1 from hp).sub_int_mul_eq _
  rw [hFval] at h
  refine h.congr_fun fun n => ?_
  rw [hcoeff, fourier_coe_apply, smul_eq_mul, mul_assoc]
  congr 1
  have : Complex.exp (2 * Real.pi * I * n * s₁ / (1 : ℝ)) = e (n * s₁) := by
    rw [e]; congr 1; push_cast; ring
  rw [this, ← e_add]
  have hs₁w : (n : ℂ) * (t * I) + n * s₁ = n * w + ((-(n * ⌊w.re⌋) : ℤ) : ℂ) := by
    rw [hs₁, ht]
    have hfr : ((Int.fract w.re : ℝ) : ℂ) = (w.re : ℂ) - ((⌊w.re⌋ : ℤ) : ℂ) := by
      have h := congrArg (fun r : ℝ => (r : ℂ)) (Int.fract_add_floor w.re)
      push_cast at h
      linear_combination h
    have hR : Int.fract w.re = w.re - ⌊w.re⌋ := (Int.self_sub_floor w.re).symm
    rw [hfr]
    apply Complex.ext
    · have h' : (n : ℝ) * Int.fract w.re = n * w.re + -(n * ⌊w.re⌋) := by rw [hR]; ring
      simpa using h'
    · simp
  rw [hs₁w, e_add, e_intCast, mul_one]

end HigherDyson3
