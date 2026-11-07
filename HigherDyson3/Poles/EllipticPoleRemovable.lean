/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.PeriodizationDecomposition
public import HigherDyson3.LocalFacts.PuncturedOffDivisor
public import HigherDyson3.LocalFacts.ThetaSumHolomorphic

/-!
# The poles of the periodization are removable where `ρ_{m,x}` vanishes

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)`, and let `τ ∈ ℍ` with `ρ_{m,x}(τ) = 0`.
For `a, b ∈ ℤ` and `w_{a,b} = -α + aτ + b`, the periodization `w ↦ ℰ_{m,x}(τ, w)` has a
limit as `w → w_{a,b}`, `w ≠ w_{a,b}`.

On a punctured disc about `w_{a,b}` the point `(τ, w)` is off the divisor
(`HigherDyson3.punctured_off_divisor`), so the decomposition
`ℰ_{m,x} = ρ_{m,x} 𝒦_{m,x} + ∑_ℓ C_{m,ℓ,x} T^{[x]}_{m,ℓ}`
(`HigherDyson3.periodization_decomposition`) reduces `ℰ_{m,x}(τ, w)` to the twisted theta
sum `S(w) = ∑_ℓ C_{m,ℓ,x}(τ) T^{[x]}_{m,ℓ}(τ, w)`. This sum is holomorphic, hence
continuous, on `ℍ × ℂ` (`HigherDyson3.differentiableOn_thetaSum`), so the limit is
`S(w_{a,b})`.

## Main results

* `HigherDyson3.periodization_pole_removable`: the poles are removable where `ρ_{m,x} = 0`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Filter Topology

namespace HigherDyson3

/-- **The poles are removable where `ρ_{m,x} = 0`.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`τ ∈ ℍ` with `ρ_{m,x}(τ) = 0` and `a, b ∈ ℤ`, the periodization `ℰ_{m,x}(τ, w)` has a limit
`L` as `w → w_{a,b} = -α + aτ + b`, `w ≠ w_{a,b}`. -/
theorem periodization_pole_removable {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : rho m α τ = 0) (a b : ℤ) :
    ∃ L : ℂ, Tendsto (fun w => periodization m α τ w)
      (𝓝[≠] (-(α : ℂ) + a * τ + b)) (𝓝 L) := by
  set w₀ : ℂ := -(α : ℂ) + a * τ + b
  set S : ℂ × ℂ → ℂ :=
    fun p => ∑ ℓ ∈ Finset.range (2 * m), coeffC m ℓ α p.1 * twistedTheta m ℓ α p.1 p.2
  refine ⟨S (τ, w₀), ?_⟩
  have hopen : IsOpen halfPlaneProd := isOpen_lt continuous_const (Complex.continuous_im.comp
    continuous_fst)
  have hcont : ContinuousAt S (τ, w₀) :=
    ((differentiableOn_thetaSum hm hα0 hα1).differentiableAt
      (hopen.mem_nhds (show (0 : ℝ) < (τ, w₀).1.im from hτ))).continuousAt
  have hS : Tendsto (fun w => S (τ, w)) (𝓝 w₀) (𝓝 (S (τ, w₀))) :=
    hcont.tendsto.comp (Continuous.prodMk_right τ).continuousAt.tendsto
  obtain ⟨δ, hδ, hoff⟩ := punctured_off_divisor α hα0 hα1 hτ w₀
  refine (hS.mono_left nhdsWithin_le_nhds).congr' ?_
  have hball : {w₀}ᶜ ∩ Metric.ball w₀ δ ∈ 𝓝[≠] w₀ :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds w₀ hδ)
  filter_upwards [hball] with w hw
  have hw0 : 0 < ‖w - w₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw.1)
  have hwδ : ‖w - w₀‖ < δ := by simpa [dist_eq_norm] using hw.2
  have hmem := hoff (w - w₀) hw0 hwδ
  rw [add_sub_cancel] at hmem
  rw [periodization_decomposition hm hα0 hα1 hmem, hρ, zero_mul, zero_add]

end HigherDyson3
