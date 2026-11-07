/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.AppellLerchProperties

/-!
# The poles of the Appell–Lerch kernel

Every point `w = β + aτ + b` of the orbit is a genuine simple pole of `A_{m,β}(τ, ·)`, with
residue `q^{-ma²} e(β)^{-2ma} / (2πi)` [AOS, Proposition 4.3(3)].
-/

public section

open Complex Filter Topology

namespace HigherDyson3

/-- **Genuine simple poles on the whole orbit** [AOS, Proposition 4.3(3)]. -/
theorem appellLerch_residue_orbit {m : ℕ} (hm : 1 ≤ m) (β : ℚ) {τ : ℂ} (hτ : 0 < τ.im)
    (a b : ℤ) :
    Tendsto (fun ε : ℂ => ε * appellLerch m β τ (β + a * τ + b + ε)) (𝓝[≠] 0)
      (𝓝 (e τ ^ (-(m : ℤ) * a ^ 2) * e β ^ (-2 * (m : ℤ) * a) / (2 * Real.pi * I))) ∧
      e τ ^ (-(m : ℤ) * a ^ 2) * e β ^ (-2 * (m : ℤ) * a) / (2 * Real.pi * I) ≠ 0 := by
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hres := appellLerch_residue hm β hτ
  have hcont : Tendsto (fun ε : ℂ => e (β + ε) ^ (-2 * (m : ℤ) * a)) (𝓝[≠] 0)
      (𝓝 (e β ^ (-2 * (m : ℤ) * a))) := by
    have hc : Continuous fun ε : ℂ => e (β + ε) ^ (-2 * (m : ℤ) * a) := by
      refine Continuous.zpow₀ (by unfold e; fun_prop) _ fun ε => Or.inl (Complex.exp_ne_zero _)
    have := hc.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨?_, ?_⟩
  · have hlim := ((tendsto_const_nhds (x := e τ ^ (-(m : ℤ) * a ^ 2))).mul hcont).mul
      (hres.div_const (2 * Real.pi * I))
    rw [mul_one_div] at hlim
    refine hlim.congr fun ε => ?_
    rw [show (β : ℂ) + a * τ + b + ε = (β + ε) + a * τ + b by ring, appellLerch_add_mul_add]
    field_simp
  · refine div_ne_zero (mul_ne_zero (zpow_ne_zero _ (Complex.exp_ne_zero _))
      (zpow_ne_zero _ (Complex.exp_ne_zero _))) hpi

end HigherDyson3
