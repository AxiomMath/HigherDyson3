/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.ThetaCoeff.ThetaExpansion
public import HigherDyson3.LocalFacts.PuncturedOffDivisor
public import HigherDyson3.Theta.ThetaHolomorphic
public import HigherDyson3.Theta.ThetaCoeffUnique

/-!
# Uniqueness of the theta coefficients

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and `x = e(α)`. If functions `h'_0, …, h'_{2m-1}` on `ℍ`
satisfy `ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h'_ℓ(τ) ϑ_{m,ℓ}(τ, w)` for every
`(τ, w) ∈ ℍ × ℂ` with `(τ, w + α/m) ∉ 𝒟_x`, then `h'_ℓ = h_{m,ℓ,x}` on `ℍ` for every `ℓ < 2m`.

Fix `τ ∈ ℍ` and put `Z(w) = ∑_ℓ (h'_ℓ(τ) - h_{m,ℓ,x}(τ)) ϑ_{m,ℓ}(τ, w)`. Subtracting the theta
expansion `HigherDyson3.finitePart_add_div_eq_sum_theta` from the hypothesis, `Z` vanishes off
the divisor slice. Every point has a punctured neighbourhood avoiding the slice
(`HigherDyson3.punctured_off_divisor`), and `Z` is continuous
(`HigherDyson3.differentiableOn_theta`), so `Z` vanishes identically; the linear independence
of the theta series (`HigherDyson3.theta_coeff_unique`) then forces every coefficient to vanish.

## Main results

* `HigherDyson3.thetaCoeffH_unique`: the theta coefficients are the unique coefficients of the
  theta expansion of the translated finite part.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset Filter Topology

namespace HigherDyson3

/-- **Uniqueness of the theta coefficients.** For `m ≥ 2` and `α ∈ ℚ` with `0 ≤ α < 1`, if
functions `h'_ℓ` satisfy `ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h'_ℓ(τ) ϑ_{m,ℓ}(τ, w)` for
every `τ ∈ ℍ` and `w ∈ ℂ` with `(τ, w + α/m) ∉ 𝒟_x`, then `h'_ℓ(τ) = h_{m,ℓ,x}(τ)` for every
`ℓ < 2m` and `τ ∈ ℍ`. -/
theorem thetaCoeffH_unique {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h' : ℕ → ℂ → ℂ)
    (hh' : ∀ τ ∈ upperHalfPlaneSet, ∀ w : ℂ, (τ, w + (α : ℂ) / m) ∉ divisor α →
      finitePart m α τ (w + (α : ℂ) / m) = ∑ ℓ ∈ range (2 * m), h' ℓ τ * theta m ℓ τ w) :
    ∀ ℓ < 2 * m, ∀ τ ∈ upperHalfPlaneSet, h' ℓ τ = thetaCoeffH m ℓ α τ := by
  intro ℓ hℓ τ hτ
  set Z : ℂ → ℂ := fun w =>
    ∑ ℓ ∈ range (2 * m), (h' ℓ τ - thetaCoeffH m ℓ α τ) * theta m ℓ τ w with hZ
  have hoff : ∀ w : ℂ, (τ, w + (α : ℂ) / m) ∉ divisor α → Z w = 0 := by
    intro w hw
    have h1 := hh' τ hτ w hw
    rw [finitePart_add_div_eq_sum_theta hm hα0 hα1 hτ hw] at h1
    simp only [hZ, sub_mul, sum_sub_distrib, h1, sub_self]
  have hcont : Continuous Z := by
    refine continuous_finsetSum _ fun ℓ _ => continuous_const.mul ?_
    have hd := (differentiableOn_theta (m := m) (by omega) ℓ).continuousOn
    have hmap : Continuous fun w : ℂ => ((τ, w) : ℂ × ℂ) := by fun_prop
    exact hd.comp_continuous hmap fun w => hτ
  have hzero : ∀ w : ℂ, Z w = 0 := by
    intro w
    obtain ⟨δ, hδ, hball⟩ := punctured_off_divisor α hα0 hα1 hτ (w + (α : ℂ) / m)
    have hev : ∀ᶠ v in 𝓝[≠] w, Z v = 0 := by
      have : ∀ᶠ v in 𝓝[≠] w, v ∈ Metric.ball w δ ∧ v ≠ w :=
        (eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds w hδ)).and
          self_mem_nhdsWithin
      filter_upwards [this] with v ⟨hv, hvw⟩
      apply hoff
      have hε := hball (v - w) (norm_pos_iff.mpr (sub_ne_zero.mpr hvw))
        (by rwa [Metric.mem_ball, dist_eq_norm] at hv)
      have : w + (α : ℂ) / m + (v - w) = v + (α : ℂ) / m := by ring
      rw [this] at hε
      exact hε.2
    have ht : Tendsto Z (𝓝[≠] w) (𝓝 (Z w)) := (hcont.tendsto w).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hev.mono fun v hv => hv.symm))
  have := theta_coeff_unique (m := m) (by omega) hτ (fun ℓ => h' ℓ τ - thetaCoeffH m ℓ α τ)
    hzero ℓ hℓ
  exact sub_eq_zero.mp this

end HigherDyson3
