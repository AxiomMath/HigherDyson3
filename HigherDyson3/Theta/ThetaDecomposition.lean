/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Theta.PeriodicFourier
public import HigherDyson3.Theta.ThetaCoeffUnique
public import HigherDyson3.Holomorphy.ParametricIntegral

/-!
# The classical theta decomposition

Let `m ≥ 1` and let `F` be holomorphic on `ℍ × ℂ` with the index-`m` elliptic law
`F(τ, w + 1) = F(τ, w)` and `F(τ, w + τ) = q^{-m} u^{-2m} F(τ, w)`. Then
`F(τ, w) = ∑_{ℓ=0}^{2m-1} h_ℓ(τ) ϑ_{m,ℓ}(τ, w)` with unique holomorphic `h_ℓ` [AOS, Lemma 4.1]
(see also [EichlerZagier, Chapter 5]).

Writing `c_r(τ) = ∫_0^1 F(τ, s) e(-rs) ds` for the Fourier coefficients of `w ↦ F(τ, w)`,
the law in `τ` gives `c_{r+2m} = q^{r+m} c_r`, so `q^{-r²/(4m)} c_r` depends only on
`r mod 2m`; the coefficients are `h_ℓ = q^{-ℓ²/(4m)} c_ℓ`, holomorphic as parametric integrals.

## Main results

* `HigherDyson3.thetaDecompositionCoeff`: the coefficient `h_ℓ(τ) = q^{-ℓ²/(4m)} c_ℓ(τ)`.
* `HigherDyson3.theta_decomposition`: the expansion `F = ∑_ℓ h_ℓ ϑ_{m,ℓ}`.
* `HigherDyson3.differentiableOn_thetaDecompositionCoeff`: each `h_ℓ` is holomorphic on `ℍ`.
* `HigherDyson3.theta_decomposition_unique`: uniqueness of the coefficients.
* `HigherDyson3.exists_unique_theta_decomposition`: [AOS, Lemma 4.1] as stated.
-/

public section

open Complex Filter Topology

namespace HigherDyson3

/-- The coefficient `h_ℓ(τ) = q^{-ℓ²/(4m)} c_ℓ(τ)` of the theta decomposition of `F`, where
`c_ℓ(τ) = ∫_0^1 F(τ, s) e(-ℓs) ds` and `q^{-ℓ²/(4m)} = e(-ℓ²τ/(4m))`. -/
noncomputable def thetaDecompositionCoeff (m : ℕ) (F : ℂ × ℂ → ℂ) (ℓ : ℕ) (τ : ℂ) : ℂ :=
  e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * periodicCoeff (fun w => F (τ, w)) ℓ

theorem thetaDecompositionCoeff_def (m : ℕ) (F : ℂ × ℂ → ℂ) (ℓ : ℕ) (τ : ℂ) :
    thetaDecompositionCoeff m F ℓ τ =
      e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * periodicCoeff (fun w => F (τ, w)) ℓ := (rfl)

/-- `ℍ × ℂ` is open. -/
theorem isOpen_halfPlaneProd : IsOpen halfPlaneProd :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)

/-- `ℍ` is open. -/
theorem isOpen_upperHalfPlaneSet : IsOpen upperHalfPlaneSet :=
  isOpen_lt continuous_const Complex.continuous_im

/-- A function holomorphic on `ℍ × ℂ` is entire in `w` for fixed `τ ∈ ℍ`. -/
theorem differentiable_slice_of_differentiableOn_halfPlaneProd {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F halfPlaneProd) {τ : ℂ} (hτ : 0 < τ.im) :
    Differentiable ℂ fun w => F (τ, w) := fun w =>
  (hF.differentiableAt (isOpen_halfPlaneProd.mem_nhds (show (τ, w) ∈ halfPlaneProd from hτ))).comp
    w (differentiableAt_const _ |>.prodMk differentiableAt_id)

private lemma e_ne_zero (z : ℂ) : e z ≠ 0 := Complex.exp_ne_zero _

/-- **The coefficient recurrence** `c_{r+2m}(τ) = q^{r+m} c_r(τ)`, for an entire `1`-periodic
`G` with `G(w + τ) = q^{-m} u^{-2m} G(w)`. -/
theorem periodicCoeff_add_two_mul {m : ℕ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (h1 : ∀ w, G (w + 1) = G w) {τ : ℂ}
    (hτ : ∀ w, G (w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * G w) (r : ℤ) :
    periodicCoeff G (r + 2 * m) = e ((r + m) * τ) * periodicCoeff G r := by
  rw [← integral_shift_eq_periodicCoeff hG h1 r τ]
  have : ∀ s : ℝ, G (s + τ) * e (-(r * (s + τ))) =
      e (-((r + m) * τ)) * (G s * e (-(((r + 2 * m : ℤ) : ℂ) * s))) := by
    intro s
    rw [hτ, kernelResidue_e_zpow, kernelResidue_e_zpow]
    set A : ℂ := ((-(m : ℤ) : ℤ) : ℂ) * τ
    set B : ℂ := ((-2 * (m : ℤ) : ℤ) : ℂ) * s
    set C : ℂ := -(r * (s + τ))
    rw [show e A * e B * G s * e C = G s * (e A * e B * e C) by ring, ← e_add, ← e_add,
      mul_left_comm, ← e_add]
    congr 2
    simp only [A, B, C]
    push_cast
    ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, ← mul_assoc, ← e_add, periodicCoeff_def]
  simp [e]

/-- `q^{-r²/(4m)} c_r(τ)` is `2m`-periodic in `r`. -/
private lemma periodic_normalized_coeff {m : ℕ} (hm : 1 ≤ m) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) (h1 : ∀ w, G (w + 1) = G w) {τ : ℂ}
    (hτ : ∀ w, G (w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * G w) :
    Function.Periodic (fun r : ℤ => e (-((r : ℂ) ^ 2) * τ / (4 * m)) * periodicCoeff G r)
      (2 * m : ℤ) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  intro r
  simp only
  rw [periodicCoeff_add_two_mul hG h1 hτ, ← mul_assoc, ← e_add]
  congr 2
  push_cast
  field_simp
  ring

/-- **Holomorphy of the Fourier coefficients.** For `F` holomorphic on `ℍ × ℂ`, the coefficient
`τ ↦ c_r(τ) = ∫_0^1 F(τ, s) e(-rs) ds` is holomorphic on `ℍ`. -/
theorem differentiableOn_periodicCoeff {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F halfPlaneProd)
    (r : ℤ) : DifferentiableOn ℂ (fun τ => periodicCoeff (fun w => F (τ, w)) r)
      upperHalfPlaneSet := by
  simp only [periodicCoeff_def]
  have hmaps : Set.MapsTo (fun q : ℂ × ℝ => (q.1, (q.2 : ℂ))) (upperHalfPlaneSet ×ˢ Set.Icc 0 1)
      halfPlaneProd := fun q hq => hq.1
  refine differentiableOn_intervalIntegral isOpen_upperHalfPlaneSet zero_le_one ?_ fun s _ => ?_
  · refine ContinuousOn.mul ?_ (Continuous.continuousOn ?_)
    · exact hF.continuousOn.comp (by fun_prop) hmaps
    · exact differentiable_e.continuous.comp (by fun_prop)
  · refine DifferentiableOn.mul ?_ (differentiableOn_const _)
    exact hF.comp (by fun_prop) fun τ hτ => (show (τ, (s : ℂ)) ∈ halfPlaneProd from hτ)

/-- Each coefficient `h_ℓ` of the theta decomposition is holomorphic on `ℍ`. -/
theorem differentiableOn_thetaDecompositionCoeff (m : ℕ) {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F halfPlaneProd) (ℓ : ℕ) :
    DifferentiableOn ℂ (thetaDecompositionCoeff m F ℓ) upperHalfPlaneSet := by
  refine DifferentiableOn.mul ?_ (differentiableOn_periodicCoeff hF ℓ)
  exact (differentiable_e.comp (by fun_prop)).differentiableOn

/-- **The classical theta decomposition** [AOS, Lemma 4.1]. Let `m ≥ 1` and let `F` be
holomorphic on `ℍ × ℂ` with `F(τ, w + 1) = F(τ, w)` and `F(τ, w + τ) = q^{-m} u^{-2m} F(τ, w)`.
Then `F(τ, w) = ∑_{ℓ=0}^{2m-1} h_ℓ(τ) ϑ_{m,ℓ}(τ, w)` on `ℍ × ℂ`, with
`h_ℓ = thetaDecompositionCoeff m F ℓ`. -/
theorem theta_decomposition {m : ℕ} (hm : 1 ≤ m) {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F halfPlaneProd)
    (h1 : ∀ τ w : ℂ, 0 < τ.im → F (τ, w + 1) = F (τ, w))
    (hτ : ∀ τ w : ℂ, 0 < τ.im →
      F (τ, w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * F (τ, w))
    {τ : ℂ} (hτ0 : 0 < τ.im) (w : ℂ) :
    F (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), thetaDecompositionCoeff m F ℓ τ * theta m ℓ τ w := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  set G : ℂ → ℂ := fun w => F (τ, w) with hGdef
  have hG : Differentiable ℂ G := differentiable_slice_of_differentiableOn_halfPlaneProd hF hτ0
  have hG1 : ∀ w, G (w + 1) = G w := fun w => h1 τ w hτ0
  have hGτ : ∀ w, G (w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * G w :=
    fun w => hτ τ w hτ0
  set P : ℤ → ℂ := fun r => e (-((r : ℂ) ^ 2) * τ / (4 * m)) * periodicCoeff G r with hP
  have hper := periodic_normalized_coeff hm hG hG1 hGτ
  -- the Fourier coefficients in terms of `P`
  have hc : ∀ r : ℤ, periodicCoeff G r = e ((r : ℂ) ^ 2 * τ / (4 * m)) * P r := by
    intro r
    simp only [hP]
    rw [← mul_assoc, ← e_add,
      show (r : ℂ) ^ 2 * τ / (4 * m) + -(r : ℂ) ^ 2 * τ / (4 * m) = 0 by ring]
    simp [e]
  set f : ℤ → ℂ := fun r => periodicCoeff G r * e (r * w) with hf
  have hsum : HasSum f (G w) := hasSum_periodicCoeff_mul_e hG hG1 w
  have hsumm : Summable fun r => ‖f r‖ := by
    refine (summable_norm_periodicCoeff_mul_exp hG hG1 w.im).congr fun r => ?_
    simp only [hf, norm_mul, norm_e]
    congr 2
    simp [Complex.mul_im, mul_assoc]
  -- regroup along `ℤ ≃ ℤ × Fin (2m)`, `(j, ℓ) ↦ j·2m + ℓ`
  set E' : Fin (2 * m) × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv (2 * m)).symm
    with hE'
  have hE'apply : ∀ ℓ : Fin (2 * m), ∀ j : ℤ, E' (ℓ, j) = j * (2 * m : ℕ) + ℓ := by
    intro ℓ j
    simp [hE', Int.divModEquiv]
  have hsum' : HasSum (f ∘ E') (G w) := (E'.hasSum_iff).mpr hsum
  have hfiber : ∀ ℓ : Fin (2 * m), HasSum (fun j : ℤ => (f ∘ E') (ℓ, j))
      (thetaDecompositionCoeff m F ℓ τ * theta m ℓ τ w) := by
    intro ℓ
    have hinj : Function.Injective fun j : ℤ => E' (ℓ, j) :=
      E'.injective.comp fun j j' h => (Prod.mk.inj h).2
    have hs : Summable fun j : ℤ => f (E' (ℓ, j)) :=
      (Summable.of_norm hsumm).comp_injective hinj
    have heq : ∀ j : ℤ, f (E' (ℓ, j)) = P ℓ *
        (e ((((ℓ : ℕ) : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m)) *
          e ((((ℓ : ℕ) : ℂ) + 2 * m * j) * w)) := by
      intro j
      have hPj : P (E' (ℓ, j)) = P ((ℓ : ℕ) : ℤ) := by
        rw [hE'apply, add_comm]
        have := (hper.int_mul j) ((ℓ : ℕ) : ℤ)
        simp only [Int.cast_id] at this
        convert this using 2
        push_cast
        ring
      simp only [hf, hc, hPj]
      rw [hE'apply]
      push_cast
      ring_nf
    have hθ : Summable fun j : ℤ => e ((((ℓ : ℕ) : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m)) *
        e ((((ℓ : ℕ) : ℂ) + 2 * m * j) * w) := by
      obtain ⟨M, hM, -, hle⟩ := thetaNormal_exists hm ℓ {(τ, w)} isCompact_singleton
        (by simpa [halfPlaneProd] using hτ0)
      exact Summable.of_norm_bounded hM fun j => by simpa [e] using hle j (τ, w) rfl
    have hPℓ : P ((ℓ : ℕ) : ℤ) = thetaDecompositionCoeff m F ℓ τ := by
      simp [hP, thetaDecompositionCoeff, hGdef]
    have := hθ.hasSum.mul_left (P ((ℓ : ℕ) : ℤ))
    rw [hPℓ] at this
    simp only [Function.comp_apply]
    simp only [heq, hPℓ]
    exact this
  have hall := hsum'.prod_fiberwise hfiber
  rw [hGdef] at hall
  simp only at hall
  rw [hall.unique (hasSum_fintype _), Fin.sum_univ_eq_sum_range
    (fun ℓ => thetaDecompositionCoeff m F ℓ τ * theta m ℓ τ w) (2 * m)]

/-- **Uniqueness of theta expansions.** For `m ≥ 1` and `τ ∈ ℍ`, if
`∑_{ℓ<2m} h_ℓ ϑ_{m,ℓ}(τ, w) = ∑_{ℓ<2m} h'_ℓ ϑ_{m,ℓ}(τ, w)` for all `w`, then `h_ℓ = h'_ℓ` for
`ℓ < 2m`. -/
theorem theta_expansion_unique {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ0 : 0 < τ.im) (h h' : ℕ → ℂ)
    (heq : ∀ w : ℂ, ∑ ℓ ∈ Finset.range (2 * m), h ℓ * theta m ℓ τ w =
      ∑ ℓ ∈ Finset.range (2 * m), h' ℓ * theta m ℓ τ w) :
    ∀ ℓ < 2 * m, h ℓ = h' ℓ := by
  intro ℓ hℓ
  refine sub_eq_zero.mp (theta_coeff_unique hm hτ0 (fun ℓ => h ℓ - h' ℓ) (fun w => ?_) ℓ hℓ)
  simp only [sub_mul, Finset.sum_sub_distrib, heq w, sub_self]

/-- **Uniqueness in the theta decomposition**: any coefficients `h_ℓ(τ)` expanding `F` in the
theta basis are the coefficients `thetaDecompositionCoeff m F ℓ τ`. -/
theorem theta_decomposition_unique {m : ℕ} (hm : 1 ≤ m) {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F halfPlaneProd)
    (h1 : ∀ τ w : ℂ, 0 < τ.im → F (τ, w + 1) = F (τ, w))
    (hτ : ∀ τ w : ℂ, 0 < τ.im →
      F (τ, w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * F (τ, w))
    {τ : ℂ} (hτ0 : 0 < τ.im) (h : ℕ → ℂ)
    (hh : ∀ w : ℂ, F (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), h ℓ * theta m ℓ τ w) :
    ∀ ℓ < 2 * m, h ℓ = thetaDecompositionCoeff m F ℓ τ :=
  theta_expansion_unique hm hτ0 _ _ fun w => (hh w).symm.trans
    (theta_decomposition hm hF h1 hτ hτ0 w)

/-- **The classical theta decomposition** [AOS, Lemma 4.1], in the form stated there: for
`m ≥ 1` and `F` holomorphic on `ℍ × ℂ` with `F(τ, w + 1) = F(τ, w)` and
`F(τ, w + τ) = q^{-m} u^{-2m} F(τ, w)`, there are holomorphic `h_ℓ` on `ℍ`, `0 ≤ ℓ < 2m`, with
`F = ∑_{ℓ=0}^{2m-1} h_ℓ ϑ_{m,ℓ}` on `ℍ × ℂ`, and any other such family agrees with `h_ℓ` on `ℍ`
for `ℓ < 2m`. -/
theorem exists_unique_theta_decomposition {m : ℕ} (hm : 1 ≤ m) {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F halfPlaneProd)
    (h1 : ∀ τ w : ℂ, 0 < τ.im → F (τ, w + 1) = F (τ, w))
    (hτ : ∀ τ w : ℂ, 0 < τ.im →
      F (τ, w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * F (τ, w)) :
    ∃ h : ℕ → ℂ → ℂ, (∀ ℓ, DifferentiableOn ℂ (h ℓ) upperHalfPlaneSet) ∧
      (∀ τ w : ℂ, 0 < τ.im →
        F (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), h ℓ τ * theta m ℓ τ w) ∧
      ∀ h' : ℕ → ℂ → ℂ, (∀ τ w : ℂ, 0 < τ.im →
        F (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), h' ℓ τ * theta m ℓ τ w) →
        ∀ ℓ < 2 * m, ∀ τ : ℂ, 0 < τ.im → h' ℓ τ = h ℓ τ :=
  ⟨thetaDecompositionCoeff m F, differentiableOn_thetaDecompositionCoeff m hF,
    fun _ w hτ0 => theta_decomposition hm hF h1 hτ hτ0 w,
    fun h' hh' ℓ hℓ τ hτ0 => theta_decomposition_unique hm hF h1 hτ hτ0 (fun ℓ => h' ℓ τ)
      (fun w => hh' τ w hτ0) ℓ hℓ⟩

end HigherDyson3
