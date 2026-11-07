/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Poles.EllipticPoleGenuine
public import HigherDyson3.Periodization.EllipticRhoLeading
public import HigherDyson3.LocalFacts.PuncturedOffDivisor

/-!
# The periodization is not identically zero

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. Then the periodization `ℰ_{m,x}` does
not vanish identically on `(ℍ × ℂ) \ 𝒟_x`.

Near the cusp, `ρ_{m,x}(τ) = x⁻² + O(|e(τ)|)` (`HigherDyson3.rho_leading`) and `|x⁻²| = 1`, so
`ρ_{m,x}(it) ≠ 0` for `t` large. At such `τ₀ = it` the point `w = -α` is a genuine pole of
`ℰ_{m,x}(τ₀, ·)` (`HigherDyson3.periodization_pole_genuine`): `ε ℰ_{m,x}(τ₀, -α + ε)` tends to
a nonzero limit. Since a punctured disc about `-α` avoids the divisor
(`HigherDyson3.punctured_off_divisor`), the periodization cannot vanish on all of
`(ℍ × ℂ) \ 𝒟_x`, for then that limit would be `0`.

## Main results

* `HigherDyson3.periodization_ne_zero`: some `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x` has
  `ℰ_{m,x}(τ, w) ≠ 0`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Filter Topology

namespace HigherDyson3

/-- There is `τ₀ ∈ ℍ` with `ρ_{m,x}(τ₀) ≠ 0`. -/
private lemma ellipticNeZero_exists_rho_ne_zero {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    ∃ τ : ℂ, τ ∈ upperHalfPlaneSet ∧ rho m α τ ≠ 0 := by
  obtain ⟨C, T, hC, hT, hbound⟩ := rho_leading hm α
  set t : ℝ := T + C with ht
  have ht0 : 0 < t := by positivity
  set τ : ℂ := t * Complex.I with hτdef
  have hτim : τ.im = t := by simp [hτdef]
  have hτ : τ ∈ upperHalfPlaneSet := by
    change 0 < τ.im
    rw [hτim]; exact ht0
  refine ⟨τ, hτ, fun h0 => ?_⟩
  have hb := hbound τ hτ (by rw [hτim]; linarith)
  have hx : ‖(e (α : ℂ) ^ 2)⁻¹‖ = 1 := by
    have : ‖e ((α : ℝ) : ℂ)‖ = 1 := rhoNormal_norm_e_ofReal (α : ℝ)
    rw [norm_inv, norm_pow]
    simp only [Complex.ofReal_ratCast] at this
    rw [this]; simp
  rw [h0, zero_sub, norm_neg, hx, ellipticRhoLeading_norm_e, hτim] at hb
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp : C < Real.exp (2 * Real.pi * t) := by
    have h1 := Real.add_one_le_exp (2 * Real.pi * t)
    have h2 : C < 2 * Real.pi * t := by
      have : C ≤ t := by linarith
      nlinarith [Real.pi_gt_three]
    linarith
  have hlt : C * Real.exp (-2 * Real.pi * t) < 1 := by
    rw [show -2 * Real.pi * t = -(2 * Real.pi * t) by ring, Real.exp_neg,
      ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    exact hexp
  linarith

/-- **The periodization is not identically zero.** For `m ≥ 2` and `α ∈ ℚ` with
`0 ≤ α < 1`, there is `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x` with `ℰ_{m,x}(τ, w) ≠ 0`. -/
theorem periodization_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p ∈ halfPlaneProd \ divisor α, periodization m α p.1 p.2 ≠ 0 := by
  obtain ⟨τ, hτ, hρ⟩ := ellipticNeZero_exists_rho_ne_zero hm α
  obtain ⟨L, hL, hlim⟩ := periodization_pole_genuine hm hα0 hα1 hτ hρ 0 0
  obtain ⟨δ, hδ, hoff⟩ := punctured_off_divisor α hα0 hα1 hτ (-(α : ℂ))
  by_contra hcon
  push Not at hcon
  have hev : (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + (0 : ℤ) * τ + (0 : ℤ) + ε))
      =ᶠ[𝓝[≠] 0] fun _ => 0 := by
    have hball : Metric.ball (0 : ℂ) δ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hδ
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with ε hε0 hεδ
    have hε : 0 < ‖ε‖ := norm_pos_iff.mpr hε0
    have hεδ' : ‖ε‖ < δ := by simpa using hεδ
    have := hcon _ (hoff ε hε hεδ')
    simp only [Int.cast_zero, zero_mul, add_zero] at this ⊢
    rw [this, mul_zero]
  have h0 := (tendsto_congr' hev).mp hlim
  exact hL (tendsto_nhds_unique h0 tendsto_const_nhds)

end HigherDyson3
