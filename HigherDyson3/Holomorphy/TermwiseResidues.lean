/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Holomorphy.NormalSeriesHolomorphic

/-!
# Termwise computation of residues

Let `U ⊆ ℂ²` be open with coordinates `(τ, w)`, and `h` holomorphic on `U` with `∂_w h ≠ 0` on
`D = {h = 0}`. If `f_n` are functions on `U \ D` such that `h f_n` extends to a holomorphic `g_n`
on `U` and `∑ g_n` converges normally on compact subsets of `U`, then `∑ f_n` extends
meromorphically across `D` with at most a simple pole: it equals `N/h` off `D` with
`N = ∑ g_n` holomorphic on `U`, and at `(τ₀, w₀) ∈ D` its residue in `w` is
`N(τ₀, w₀) / ∂_w h(τ₀, w₀)` [AOS, Lemma 4.2].

The manuscript also assumes that the `f_n` are holomorphic and that `∑ f_n` converges normally
on compact subsets of `U \ D`; these hypotheses are not needed for the conclusions and are
omitted.
-/

public section

namespace HigherDyson3

open Filter Topology

/-- **Termwise computation of residues** [AOS, Lemma 4.2]. -/
theorem termwise_residues {ι : Type*} {U : Set (ℂ × ℂ)} (hU : IsOpen U) {h : ℂ × ℂ → ℂ}
    (hh : DifferentiableOn ℂ h U)
    (hderiv : ∀ p ∈ U, h p = 0 → deriv (fun w => h (p.1, w)) p.2 ≠ 0)
    {f g : ι → ℂ × ℂ → ℂ} (hg : ∀ n, DifferentiableOn ℂ (g n) U)
    (hgf : ∀ n, ∀ p ∈ U, h p ≠ 0 → g n p = h p * f n p)
    (hgn : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧ ∀ n, ∀ p ∈ K, ‖g n p‖ ≤ u n) :
    DifferentiableOn ℂ (fun p => ∑' n, g n p) U ∧
      (∀ p ∈ U, h p ≠ 0 → ∑' n, f n p = (∑' n, g n p) / h p) ∧
      ∀ p ∈ U, h p = 0 →
        Tendsto (fun w => (w - p.2) * ∑' n, f n (p.1, w)) (𝓝[≠] p.2)
          (𝓝 ((∑' n, g n p) / deriv (fun w => h (p.1, w)) p.2)) := by
  set N : ℂ × ℂ → ℂ := fun p => ∑' n, g n p with hN
  have hNd : DifferentiableOn ℂ N U := differentiableOn_tsum_of_normal hU hg hgn
  have hoff : ∀ p ∈ U, h p ≠ 0 → ∑' n, f n p = N p / h p := by
    intro p hp hp0
    rw [hN, ← tsum_div_const]
    refine tsum_congr fun n => ?_
    rw [hgf n p hp hp0, mul_div_cancel_left₀ _ hp0]
  refine ⟨hNd, hoff, fun p hp hp0 => ?_⟩
  obtain ⟨τ₀, w₀⟩ := p
  simp only at hp0 ⊢
  -- the slice `φ(w) = h(τ₀, w)` and the slice of `N`
  set φ : ℂ → ℂ := fun w => h (τ₀, w) with hφ
  have hslice : ∀ᶠ w in 𝓝 w₀, (τ₀, w) ∈ U := by
    have : Continuous fun w : ℂ => (τ₀, w) := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
  have hφd : HasDerivAt φ (deriv φ w₀) w₀ := by
    have h1 : DifferentiableAt ℂ h (τ₀, w₀) := hh.differentiableAt (hU.mem_nhds hp)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (τ₀, w)) w₀ := by fun_prop
    exact (h1.comp w₀ h2).hasDerivAt
  have hd0 : deriv φ w₀ ≠ 0 := hderiv _ hp hp0
  -- `φ(w)/(w - w₀) → φ'(w₀)`
  have hslope : Tendsto (fun w => φ w / (w - w₀)) (𝓝[≠] w₀) (𝓝 (deriv φ w₀)) := by
    have := hφd.tendsto_slope_zero
    rw [hasDerivAt_iff_tendsto_slope] at hφd
    refine hφd.congr' (Eventually.of_forall fun w => ?_)
    simp only [slope_def_field, hφ, hp0, sub_zero]
  have hφne : ∀ᶠ w in 𝓝[≠] w₀, φ w ≠ 0 := by
    have hev := hslope.eventually_ne hd0
    filter_upwards [hev] with w hw h0
    exact hw (by rw [h0, zero_div])
  have hNc : Tendsto (fun w => N (τ₀, w)) (𝓝[≠] w₀) (𝓝 (N (τ₀, w₀))) := by
    have h1 : ContinuousAt N (τ₀, w₀) := (hNd.differentiableAt (hU.mem_nhds hp)).continuousAt
    have h2 : ContinuousAt (fun w : ℂ => (τ₀, w)) w₀ := by fun_prop
    exact (h1.comp h2).tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun w => (φ w / (w - w₀))⁻¹ * N (τ₀, w)) (𝓝[≠] w₀)
      (𝓝 ((deriv φ w₀)⁻¹ * N (τ₀, w₀))) := (hslope.inv₀ hd0).mul hNc
  rw [div_eq_inv_mul]
  refine hlim.congr' ?_
  have hslice' : ∀ᶠ w in 𝓝[≠] w₀, (τ₀, w) ∈ U := nhdsWithin_le_nhds hslice
  filter_upwards [hφne, hslice', self_mem_nhdsWithin] with w hw hwU hwne
  have hww : w - w₀ ≠ 0 := sub_ne_zero.mpr hwne
  have hw' : h (τ₀, w) ≠ 0 := hw
  rw [hoff (τ₀, w) hwU hw']
  simp only [hφ]
  field_simp

end HigherDyson3
