/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.ExpQuotientHolomorphic
public import HigherDyson3.Kernel.KernelRegularHolomorphic
public import HigherDyson3.Kernel.KernelSplit

/-!
# The residue of the kernel along `L_{a,b}`

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)`, `τ ∈ ℍ`, `q = e(τ)` and `a, b ∈ ℤ`, and
put `w₀ = -α + aτ + b`, so that `(τ, w₀) ∈ L_{a,b}`. Then
`ε 𝒦_{m,x}(τ, w₀ + ε) → -(2πi)⁻¹ x^{2(m+1)a} q^{-ma²}` as `ε → 0`, `ε ≠ 0`.

The point `(τ, w₀)` lies on no other component, so it is in the open set `Ω_{a,b}`, and for
small `ε ≠ 0` the point `(τ, w₀ + ε)` is off `𝒟_x`. There, splitting off the summand `n = -a`
and using `x u q^{-a} = e(ε)` gives
`ε 𝒦_{m,x}(τ, w₀ + ε) = ε 𝒦^{(a)}_{m,x}(τ, w₀ + ε) + x^{2a} q^{ma²} e(w₀ + ε)^{-2ma} Φ(ε)`.
The right-hand side is continuous at `ε = 0`, with value `x^{2a} q^{ma²} e(w₀)^{-2ma} Φ(0)`.

## Main results

* `HigherDyson3.kernel_residue`: the limit of `ε 𝒦_{m,x}(τ, -α + aτ + b + ε)` along `ε → 0`,
  `ε ≠ 0`, is `-(2πi)⁻¹ x^{2(m+1)a} q^{-ma²}`.
-/

public section

open Complex Filter Topology

namespace HigherDyson3

/-- `e(z)^k = e(kz)` for `k ∈ ℤ`. -/
theorem kernelResidue_e_zpow (z : ℂ) (k : ℤ) : e z ^ k = e (k * z) := by
  simp only [e]
  rw [← Complex.exp_int_mul]
  ring_nf

/-- `e(z) e(y) = e(z + y)`. -/
theorem kernelResidue_e_mul (z y : ℂ) : e z * e y = e (z + y) := by
  simp only [e]
  rw [← Complex.exp_add]
  ring_nf

/-- The point `(τ, -α + aτ + b)`, `τ ∈ ℍ`, lies in `Ω_{a,b}`. -/
theorem kernelResidue_mem_divisorNbhd (α : ℚ) {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet)
    (a b : ℤ) : (τ, -(α : ℂ) + a * τ + b) ∈ divisorNbhd α a b := by
  refine ⟨hτ, fun h => ?_⟩
  obtain ⟨⟨c, d⟩, hcd, -, hw⟩ := Set.mem_iUnion₂.mp h
  have hτ' : 0 < τ.im := hτ
  have him := congrArg Complex.im hw
  simp only [add_im, neg_im, ratCast_im, mul_im, intCast_re, intCast_im, zero_mul,
    add_zero, neg_zero, zero_add] at him
  have hac : a = c := by
    have : ((a : ℝ) - c) * τ.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · linarith
  subst hac
  have hbd : (b : ℂ) = d := by linear_combination hw
  exact hcd (by simp only [Prod.mk.injEq, true_and]; exact_mod_cast hbd.symm)

/-- **Residue of the kernel.** For an integer `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`x = e(α)`, `τ ∈ ℍ`, `q = e(τ)` and `a, b ∈ ℤ`,
`lim_{ε → 0, ε ≠ 0} ε 𝒦_{m,x}(τ, -α + aτ + b + ε) = -(2πi)⁻¹ x^{2(m+1)a} q^{-ma²}`. -/
theorem kernel_residue (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (a b : ℤ) :
    Tendsto (fun ε : ℂ => ε * kernel m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
      (𝓝 (-1 / (2 * Real.pi * Complex.I) * e α ^ (2 * ((m : ℤ) + 1) * a) *
        e τ ^ (-(m : ℤ) * a ^ 2))) := by
  set w₀ : ℂ := -(α : ℂ) + a * τ + b with hw₀
  set C : ℂ := e α ^ (2 * a) * e τ ^ ((m : ℤ) * a ^ 2) with hC
  set g : ℂ → ℂ := fun ε => ε * kernelRegular m α a τ (w₀ + ε) +
    C * e (w₀ + ε) ^ (-2 * (m : ℤ) * a) * expQuotient ε with hg
  have hΩ := divisorNbhd_isOpen α hα0 hα1 a b
  have hp₀ := kernelResidue_mem_divisorNbhd α hτ a b
  have hline : Continuous fun ε : ℂ => (τ, w₀ + ε) := by fun_prop
  have he : Continuous e := by unfold e; fun_prop
  -- `g` is continuous at `0`.
  have hgc : ContinuousAt g 0 := by
    have hK : ContinuousAt (fun p : ℂ × ℂ => kernelRegular m α a p.1 p.2) (τ, w₀) :=
      ((kernelRegular_differentiableOn m hm α hα0 hα1 a b).differentiableAt
        (hΩ.mem_nhds hp₀)).continuousAt
    have hK' : ContinuousAt ((fun p : ℂ × ℂ => kernelRegular m α a p.1 p.2) ∘
        fun ε : ℂ => (τ, w₀ + ε)) 0 :=
      hK.comp_of_eq hline.continuousAt (by rw [add_zero])
    have hΦ : ContinuousAt expQuotient 0 :=
      (expQuotient_differentiableOn.2.differentiableAt
        (expQuotient_differentiableOn.1.mem_nhds (by simp))).continuousAt
    have hu : ContinuousAt (fun ε : ℂ => e (w₀ + ε) ^ (-2 * (m : ℤ) * a)) 0 :=
      ((he.comp (continuous_const.add continuous_id)).continuousAt).zpow₀ _
        (Or.inl (Complex.exp_ne_zero _))
    exact (continuousAt_id.mul hK').add ((continuousAt_const.mul hu).mul hΦ)
  -- `g 0` is the claimed limit.
  have hg0 : g 0 = -1 / (2 * Real.pi * Complex.I) * e α ^ (2 * ((m : ℤ) + 1) * a) *
      e τ ^ (-(m : ℤ) * a ^ 2) := by
    have hΦ0 : expQuotient 0 = -1 / (2 * Real.pi * Complex.I) := by simp [expQuotient]
    have hCu : C * e w₀ ^ (-2 * (m : ℤ) * a) =
        e α ^ (2 * ((m : ℤ) + 1) * a) * e τ ^ (-(m : ℤ) * a ^ 2) := by
      rw [hC, hw₀]
      simp only [kernelResidue_e_zpow, kernelResidue_e_mul]
      simp only [e]
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨-2 * m * a * b, by push_cast; ring⟩
    simp only [hg, zero_mul, zero_add, add_zero]
    rw [hCu, hΦ0]
    ring
  -- Near `0`, `ε ≠ 0`, the function equals `g`.
  have hev : ∀ᶠ ε in 𝓝 (0 : ℂ), (τ, w₀ + ε) ∈ divisorNbhd α a b :=
    hline.continuousAt.preimage_mem_nhds (by simpa using hΩ.mem_nhds hp₀)
  have heq : g =ᶠ[𝓝[≠] 0] fun ε => ε * kernel m α τ (w₀ + ε) := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with ε hε hε0
    have hε0 : ε ≠ 0 := hε0
    have hoff : (τ, w₀ + ε) ∈ halfPlaneProd \ divisor α := by
      refine ⟨hε.1, fun hD => ?_⟩
      obtain ⟨c, d, hcd⟩ := Set.mem_iUnion₂.mp hD
      by_cases h : (c, d) = (a, b)
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply hε0
        have := hcd.2
        simp only at this
        linear_combination this
      · exact hε.2 (Set.mem_iUnion₂.mpr ⟨(c, d), h, hcd⟩)
    have hxu : e α * e (w₀ + ε) * e τ ^ (-a) = e ε := by
      rw [kernelResidue_e_zpow, kernelResidue_e_mul, kernelResidue_e_mul]
      simp only [e]
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨b, by rw [hw₀]; push_cast; ring⟩
    have hΦ : expQuotient ε = ε / (1 - e ε) := by
      rw [expQuotient, ite_eq_right_of_eq_false _ _ (eq_false hε0)]
    simp only [hg]
    rw [kernel_split m hm α hα0 hα1 a hoff, hxu, hΦ, hC]
    ring
  have ht : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hgc.tendsto.mono_left nhdsWithin_le_nhds
  rw [hg0] at ht
  exact ht.congr' heq

end HigherDyson3
