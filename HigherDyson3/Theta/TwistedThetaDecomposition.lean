/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Theta.ThetaDecomposition
public import HigherDyson3.Theta.ConstantTwist
public import HigherDyson3.Theta.TwistedThetaHolomorphic

/-!
# Theta decomposition for the twisted elliptic law

Let `m ≥ 1`, `α ∈ ℚ` and `x = e(α)`. The twisted theta series
`T^{[x]}_{m,ℓ}(τ, w) = ∑_{j ∈ ℤ} x^{-2j} q^{mj²+ℓj} u^{ℓ+2mj}` are holomorphic on `ℍ × ℂ` and
satisfy the twisted law `T(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} T(τ, w)`; every holomorphic
`Y` on `ℍ × ℂ` with this law has a unique expansion `Y = ∑_{ℓ=0}^{2m-1} C_ℓ(τ) T^{[x]}_{m,ℓ}`
with `C_ℓ` holomorphic on `ℍ`, namely the Fourier coefficients `C_ℓ = c_ℓ` of `w ↦ Y(τ, w)`
[AOS, Lemma 4.5].

The expansion is deduced from the classical theta decomposition
(`HigherDyson3.theta_decomposition`) applied to the translate `Y(τ, w + α/m)`, which satisfies
the untwisted law, and the translation formula
`T^{[x]}_{m,ℓ}(τ, w + α/m) = e(ℓα/m) q^{-ℓ²/(4m)} ϑ_{m,ℓ}(τ, w)` [AOS, Remark 4.6(1)].

## Main results

* `HigherDyson3.twistedTheta_add_mul_add`: the twisted law of `T^{[x]}_{m,ℓ}`.
* `HigherDyson3.twisted_theta_decomposition`: the expansion of `Y`.
* `HigherDyson3.twistedTheta_expansion_unique`: uniqueness of the coefficients.
* `HigherDyson3.exists_unique_twisted_theta_decomposition`: [AOS, Lemma 4.5] as stated.

## Implementation notes

The source takes `α ∈ ℚ ∩ [0, 1)`; the proofs hold for every `α ∈ ℚ`.
-/

public section

open Complex

namespace HigherDyson3

/-- **The twisted law of the twisted theta series.** For `a, b ∈ ℤ`,
`T^{[x]}_{m,ℓ}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} T^{[x]}_{m,ℓ}(τ, w)`. -/
theorem twistedTheta_add_mul_add (m ℓ : ℕ) (α : ℚ) (τ w : ℂ) (a b : ℤ) :
    twistedTheta m ℓ α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        twistedTheta m ℓ α τ w := by
  have key : ∀ j : ℤ, e α ^ (-2 * j) * e τ ^ ((m : ℤ) * j ^ 2 + ℓ * j) *
      e (w + a * τ + b) ^ ((ℓ : ℤ) + 2 * m * j) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        (e α ^ (-2 * (j + a)) * e τ ^ ((m : ℤ) * (j + a) ^ 2 + ℓ * (j + a)) *
          e w ^ ((ℓ : ℤ) + 2 * m * (j + a))) := by
    intro j
    simp only [kernelResidue_e_zpow, kernelResidue_e_mul]
    simp only [e]
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨b * (ℓ + 2 * m * j), by push_cast; ring⟩
  unfold twistedTheta
  simp_rw [key]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight a).tsum_eq
    (fun j => e α ^ (-2 * j) * e τ ^ ((m : ℤ) * j ^ 2 + ℓ * j) * e w ^ ((ℓ : ℤ) + 2 * m * j))

/-- `T^{[x]}_{m,ℓ}(τ, w + 1) = T^{[x]}_{m,ℓ}(τ, w)`. -/
theorem twistedTheta_add_one (m ℓ : ℕ) (α : ℚ) (τ w : ℂ) :
    twistedTheta m ℓ α τ (w + 1) = twistedTheta m ℓ α τ w := by
  simpa using twistedTheta_add_mul_add m ℓ α τ w 0 1

/-- `T^{[x]}_{m,ℓ}(τ, w + τ) = x² q^{-m} u^{-2m} T^{[x]}_{m,ℓ}(τ, w)`. -/
theorem twistedTheta_add_self (m ℓ : ℕ) (α : ℚ) (τ w : ℂ) :
    twistedTheta m ℓ α τ (w + τ) =
      e α ^ 2 * e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * twistedTheta m ℓ α τ w := by
  simpa using twistedTheta_add_mul_add m ℓ α τ w 1 0

/-- **Translation to the standard theta series** [AOS, Remark 4.6(1)]. For `m ≥ 1`,
`T^{[x]}_{m,ℓ}(τ, w + α/m) = e(ℓα/m) e(-ℓ²τ/(4m)) ϑ_{m,ℓ}(τ, w)`. -/
theorem twistedTheta_add_div_eq {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (α : ℚ) (τ w : ℂ) :
    twistedTheta m ℓ α τ (w + α / m) =
      e (ℓ * α / m) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * theta m ℓ τ w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold twistedTheta theta
  rw [← tsum_mul_left]
  congr 1
  funext j
  simp only [kernelResidue_e_zpow, ← e_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **Fourier coefficients of a translate.** For an entire `1`-periodic `G` and `z ∈ ℂ`,
the `r`-th Fourier coefficient of `w ↦ G(w + z)` is `e(rz) c_r(G)`. -/
theorem periodicCoeff_comp_add {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hp : ∀ w, G (w + 1) = G w)
    (r : ℤ) (z : ℂ) : periodicCoeff (fun w => G (w + z)) r = e (r * z) * periodicCoeff G r := by
  rw [← integral_shift_eq_periodicCoeff hG hp r z, periodicCoeff_def,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [mul_left_comm, ← e_add]
  congr 2
  ring

/-- The two generating cases of the twisted law. -/
private lemma twisted_law_generators {m : ℕ} {α : ℚ} {Y : ℂ × ℂ → ℂ}
    (hlaw : ∀ τ w : ℂ, 0 < τ.im → ∀ a b : ℤ, Y (τ, w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * Y (τ, w))
    {τ : ℂ} (hτ0 : 0 < τ.im) :
    (∀ w, Y (τ, w + 1) = Y (τ, w)) ∧
      ∀ w, Y (τ, w + τ) = e α ^ 2 * e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * Y (τ, w) :=
  ⟨fun w => by simpa using hlaw τ w hτ0 0 1, fun w => by simpa using hlaw τ w hτ0 1 0⟩

/-- **Twisted theta decomposition** [AOS, Lemma 4.5]. Let `m ≥ 1`, `α ∈ ℚ` and let `Y` be
holomorphic on `ℍ × ℂ` with `Y(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} Y(τ, w)` for all
`a, b ∈ ℤ`, `x = e(α)`. Then `Y(τ, w) = ∑_{ℓ=0}^{2m-1} c_ℓ(τ) T^{[x]}_{m,ℓ}(τ, w)` on `ℍ × ℂ`,
with `c_ℓ(τ) = ∫_0^1 Y(τ, s) e(-ℓs) ds`. -/
theorem twisted_theta_decomposition {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {Y : ℂ × ℂ → ℂ}
    (hY : DifferentiableOn ℂ Y halfPlaneProd)
    (hlaw : ∀ τ w : ℂ, 0 < τ.im → ∀ a b : ℤ, Y (τ, w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * Y (τ, w))
    {τ : ℂ} (hτ0 : 0 < τ.im) (w : ℂ) :
    Y (τ, w) = ∑ ℓ ∈ Finset.range (2 * m),
      periodicCoeff (fun w => Y (τ, w)) ℓ * twistedTheta m ℓ α τ w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  set c : ℂ := (α : ℂ) / m with hc
  set Yt : ℂ × ℂ → ℂ := fun p => Y (p.1, p.2 + c) with hYtdef
  have hYt : DifferentiableOn ℂ Yt halfPlaneProd :=
    hY.comp (by fun_prop) fun p hp => (show (p.1, p.2 + c) ∈ halfPlaneProd from hp)
  have hlawt : ∀ τ w : ℂ, 0 < τ.im → Yt (τ, w + 1) = Yt (τ, w) ∧
      Yt (τ, w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * Yt (τ, w) := by
    intro τ w hτ
    obtain ⟨g1, gτ⟩ := twisted_law_generators hlaw hτ
    exact untwisted_law_of_twisted_law (Y := fun τ w => Y (τ, w)) hm α g1 gτ w
  have hdec := theta_decomposition hm hYt (fun τ w hτ => (hlawt τ w hτ).1)
    (fun τ w hτ => (hlawt τ w hτ).2) hτ0 (w - c)
  have hYw : Yt (τ, w - c) = Y (τ, w) := by simp [hYtdef]
  rw [hYw] at hdec
  rw [hdec]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hG := differentiable_slice_of_differentiableOn_halfPlaneProd hY hτ0
  have hG1 : ∀ w, Y (τ, w + 1) = Y (τ, w) := (twisted_law_generators hlaw hτ0).1
  have hT := twistedTheta_add_div_eq hm ℓ α τ (w - c)
  rw [← hc, sub_add_cancel] at hT
  rw [hT, thetaDecompositionCoeff_def]
  simp only [hYtdef]
  rw [periodicCoeff_comp_add hG hG1]
  simp only [← mul_assoc]
  rw [show e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * e (((ℓ : ℤ) : ℂ) * c) *
      periodicCoeff (fun w => Y (τ, w)) ℓ * theta m ℓ τ (w - c) =
      periodicCoeff (fun w => Y (τ, w)) ℓ *
        (e (ℓ * α / m) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * theta m ℓ τ (w - c)) by
    rw [hc]; push_cast; ring_nf]
  ring

/-- **Uniqueness of twisted theta expansions.** For `m ≥ 1`, `α ∈ ℚ` and `τ ∈ ℍ`, if
`∑_{ℓ<2m} C_ℓ T^{[x]}_{m,ℓ}(τ, w) = ∑_{ℓ<2m} C'_ℓ T^{[x]}_{m,ℓ}(τ, w)` for all `w`, then
`C_ℓ = C'_ℓ` for `ℓ < 2m`. -/
theorem twistedTheta_expansion_unique {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {τ : ℂ} (hτ0 : 0 < τ.im)
    (C C' : ℕ → ℂ)
    (heq : ∀ w : ℂ, ∑ ℓ ∈ Finset.range (2 * m), C ℓ * twistedTheta m ℓ α τ w =
      ∑ ℓ ∈ Finset.range (2 * m), C' ℓ * twistedTheta m ℓ α τ w) :
    ∀ ℓ < 2 * m, C ℓ = C' ℓ := by
  set k : ℕ → ℂ := fun ℓ => e (ℓ * α / m) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) with hk
  have hk0 : ∀ ℓ, k ℓ ≠ 0 := fun ℓ => mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have h := theta_expansion_unique hm hτ0 (fun ℓ => C ℓ * k ℓ) (fun ℓ => C' ℓ * k ℓ)
    fun w => by
      have := heq (w + α / m)
      simp only [twistedTheta_add_div_eq hm] at this
      simpa only [hk, mul_assoc] using this
  intro ℓ hℓ
  exact mul_right_cancel₀ (hk0 ℓ) (h ℓ hℓ)

/-- **The twisted theta series** [AOS, Lemma 4.5, first part]: for `m ≥ 1` each
`T^{[x]}_{m,ℓ}` is holomorphic on `ℍ × ℂ` and satisfies the twisted law. -/
theorem twistedTheta_differentiableOn_and_law {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (α : ℚ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => twistedTheta m ℓ α p.1 p.2) halfPlaneProd ∧
      ∀ τ w : ℂ, ∀ a b : ℤ, twistedTheta m ℓ α τ (w + a * τ + b) =
        e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
          twistedTheta m ℓ α τ w :=
  ⟨differentiableOn_twistedTheta hm ℓ α, fun τ w a b => twistedTheta_add_mul_add m ℓ α τ w a b⟩

/-- **Twisted theta decomposition** [AOS, Lemma 4.5, second part], in the form stated there:
for `m ≥ 1`, `α ∈ ℚ` and `Y` holomorphic on `ℍ × ℂ` with the twisted law, there are holomorphic
`C_ℓ` on `ℍ`, `0 ≤ ℓ < 2m`, with `Y = ∑_{ℓ=0}^{2m-1} C_ℓ T^{[x]}_{m,ℓ}` on `ℍ × ℂ`, and any
other such family agrees with `C_ℓ` on `ℍ` for `ℓ < 2m`. -/
theorem exists_unique_twisted_theta_decomposition {m : ℕ} (hm : 1 ≤ m) (α : ℚ)
    {Y : ℂ × ℂ → ℂ} (hY : DifferentiableOn ℂ Y halfPlaneProd)
    (hlaw : ∀ τ w : ℂ, 0 < τ.im → ∀ a b : ℤ, Y (τ, w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * Y (τ, w)) :
    ∃ C : ℕ → ℂ → ℂ, (∀ ℓ, DifferentiableOn ℂ (C ℓ) upperHalfPlaneSet) ∧
      (∀ τ w : ℂ, 0 < τ.im →
        Y (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), C ℓ τ * twistedTheta m ℓ α τ w) ∧
      ∀ C' : ℕ → ℂ → ℂ, (∀ τ w : ℂ, 0 < τ.im →
        Y (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), C' ℓ τ * twistedTheta m ℓ α τ w) →
        ∀ ℓ < 2 * m, ∀ τ : ℂ, 0 < τ.im → C' ℓ τ = C ℓ τ :=
  ⟨fun ℓ τ => periodicCoeff (fun w => Y (τ, w)) ℓ,
    fun ℓ => differentiableOn_periodicCoeff hY ℓ,
    fun _ w hτ0 => twisted_theta_decomposition hm α hY hlaw hτ0 w,
    fun C' hC' ℓ hℓ τ hτ0 => twistedTheta_expansion_unique hm α hτ0 (fun ℓ => C' ℓ τ)
      (fun ℓ => periodicCoeff (fun w => Y (τ, w)) ℓ)
      (fun w => (hC' τ w hτ0).symm.trans (twisted_theta_decomposition hm α hY hlaw hτ0 w)) ℓ hℓ⟩

/-- **[AOS, Lemma 4.5]**, both parts: for `m ≥ 1` and `α ∈ ℚ`, each `T^{[x]}_{m,ℓ}` is
holomorphic on `ℍ × ℂ` with the twisted law, and every `Y` holomorphic on `ℍ × ℂ` with the
twisted law has a unique expansion `Y = ∑_{ℓ=0}^{2m-1} C_ℓ T^{[x]}_{m,ℓ}` with `C_ℓ` holomorphic
on `ℍ`. -/
theorem twistedTheta_basis {m : ℕ} (hm : 1 ≤ m) (α : ℚ) :
    (∀ ℓ : ℕ, DifferentiableOn ℂ (fun p : ℂ × ℂ => twistedTheta m ℓ α p.1 p.2) halfPlaneProd ∧
      ∀ τ w : ℂ, ∀ a b : ℤ, twistedTheta m ℓ α τ (w + a * τ + b) =
        e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
          twistedTheta m ℓ α τ w) ∧
    ∀ Y : ℂ × ℂ → ℂ, DifferentiableOn ℂ Y halfPlaneProd →
      (∀ τ w : ℂ, 0 < τ.im → ∀ a b : ℤ, Y (τ, w + a * τ + b) =
        e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * Y (τ, w)) →
      ∃ C : ℕ → ℂ → ℂ, (∀ ℓ, DifferentiableOn ℂ (C ℓ) upperHalfPlaneSet) ∧
        (∀ τ w : ℂ, 0 < τ.im →
          Y (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), C ℓ τ * twistedTheta m ℓ α τ w) ∧
        ∀ C' : ℕ → ℂ → ℂ, (∀ τ w : ℂ, 0 < τ.im →
          Y (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), C' ℓ τ * twistedTheta m ℓ α τ w) →
          ∀ ℓ < 2 * m, ∀ τ : ℂ, 0 < τ.im → C' ℓ τ = C ℓ τ :=
  ⟨fun ℓ => twistedTheta_differentiableOn_and_law hm ℓ α,
    fun _ hY hlaw => exists_unique_twisted_theta_decomposition hm α hY hlaw⟩

end HigherDyson3
