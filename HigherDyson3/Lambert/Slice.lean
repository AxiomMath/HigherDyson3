/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.Residue

/-!
# The periodization of a Lambert seed for fixed `τ`

Fix `τ ∈ ℍ`. This file restates [AOS, Lemma 7.4] for the meromorphic function
`w ↦ ℰ_Φ(τ, w)`: it is holomorphic off the orbit `-β + ℤτ + ℤ`, has at most a simple pole at each
point `w₀` (`(w - w₀) ℰ_Φ(τ, w)` agrees near `w₀` with a function analytic at `w₀`), and the
pole at an orbit point is genuine when `ρ_Φ(τ) ≠ 0`.

## Main results

* `HigherDyson3.differentiableAt_seedPeriodization_lambertSeed`: holomorphy off the orbit.
* `HigherDyson3.exists_analyticAt_sub_mul_seedPeriodization_lambertSeed`: at most simple poles.
* `HigherDyson3.exists_tendsto_sub_mul_seedPeriodization_lambertSeed`: genuine simple poles.
-/

public section

noncomputable section

open Complex Filter Topology

namespace HigherDyson3

variable {m : ℕ} {α β : ℚ} {b : ℕ → ℂ → ℂ}

/-- `w ↦ w - w₀` maps punctured neighbourhoods of `w₀` to punctured neighbourhoods of `0`. -/
lemma tendsto_sub_nhdsNE (w₀ : ℂ) : Tendsto (fun w => w - w₀) (𝓝[≠] w₀) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun w : ℂ => w - w₀) (𝓝 w₀) (𝓝 (w₀ - w₀)) :=
      (continuous_id.sub continuous_const).tendsto w₀
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact sub_ne_zero.mpr hw

/-- Near any `w₀`, off `w₀`, the point `(τ, w)` lies off `𝒟_c`. -/
lemma eventually_mem_diff_divisor (hβ0 : 0 ≤ β) (hβ1 : β < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (w₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] w₀, (τ, w) ∈ halfPlaneProd \ divisor β := by
  obtain ⟨δ, hδ, hoff⟩ := punctured_off_divisor β hβ0 hβ1 hτ w₀
  have hball : {w₀}ᶜ ∩ Metric.ball w₀ δ ∈ 𝓝[≠] w₀ :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hball] with w hw
  have hw0 : 0 < ‖w - w₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw.1)
  have hwδ : ‖w - w₀‖ < δ := by simpa [dist_eq_norm] using hw.2
  simpa using hoff _ hw0 hwδ

/-- The slice `w ↦ (τ, w)` of an open set containing `(τ, w₀)` is a neighbourhood of `w₀`. -/
lemma slice_mem_nhds {U : Set (ℂ × ℂ)} (hU : IsOpen U) {τ w₀ : ℂ} (h : (τ, w₀) ∈ U) :
    {w | (τ, w) ∈ U} ∈ 𝓝 w₀ :=
  (hU.preimage (Continuous.prodMk_right τ)).mem_nhds h

/-- **Holomorphy in `w` off the orbit.** -/
theorem differentiableAt_seedPeriodization_lambertSeed (hm : 1 ≤ m) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor β) :
    DifferentiableAt ℂ (fun w => seedPeriodization m α (lambertSeed (e α) (e β) b) τ w) w := by
  obtain ⟨hU, hD⟩ := differentiableOn_seedPeriodization_lambertSeed (m := m) hm α hβ0 hβ1 hb hB
  exact (hD.differentiableAt (hU.mem_nhds hτw)).comp w
    ((differentiableAt_const τ).prodMk differentiableAt_id)

/-- **Analyticity in `w` off the orbit.** -/
theorem analyticAt_seedPeriodization_lambertSeed (hm : 1 ≤ m) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ w₀ : ℂ} (hτw : (τ, w₀) ∈ halfPlaneProd \ divisor β) :
    AnalyticAt ℂ (fun w => seedPeriodization m α (lambertSeed (e α) (e β) b) τ w) w₀ := by
  obtain ⟨hU, -⟩ := differentiableOn_seedPeriodization_lambertSeed (m := m) hm α hβ0 hβ1 hb hB
  refine DifferentiableOn.analyticAt (s := {w | (τ, w) ∈ halfPlaneProd \ divisor β}) ?_
    (slice_mem_nhds hU hτw)
  intro w hw
  exact (differentiableAt_seedPeriodization_lambertSeed hm hβ0 hβ1 hb hB hw).differentiableWithinAt

/-- **At most a simple pole at every point.** For `τ ∈ ℍ` and `w₀ ∈ ℂ` there is `N` analytic
at `w₀` with `N(w) = (w - w₀) ℰ_Φ(τ, w)` for `w` near `w₀` off the orbit. -/
theorem exists_analyticAt_sub_mul_seedPeriodization_lambertSeed (hm : 1 ≤ m) (α : ℚ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (w₀ : ℂ) :
    ∃ N : ℂ → ℂ, AnalyticAt ℂ N w₀ ∧ ∀ᶠ w in 𝓝 w₀, (τ, w) ∈ halfPlaneProd \ divisor β →
      N w = (w - w₀) * seedPeriodization m α (lambertSeed (e α) (e β) b) τ w := by
  by_cases hD : (τ, w₀) ∈ divisor β
  · obtain ⟨a, k, -, hw₀⟩ := Set.mem_iUnion₂.mp hD
    simp only at hw₀
    obtain ⟨N, hN, hNe⟩ := seedPeriodization_lambertSeed_simple_poles hm α hβ0 hβ1 hb hB a k
    have hmem := kernelResidue_mem_divisorNbhd β hτ a k
    rw [← hw₀] at hmem
    have hnhds := slice_mem_nhds (divisorNbhd_isOpen β hβ0 hβ1 a k) hmem
    refine ⟨fun w => N (τ, w), ?_, Filter.Eventually.of_forall fun w hw => ?_⟩
    · refine DifferentiableOn.analyticAt (s := {w | (τ, w) ∈ divisorNbhd β a k}) ?_ hnhds
      intro w hw
      exact ((hN.differentiableAt ((divisorNbhd_isOpen β hβ0 hβ1 a k).mem_nhds hw)).comp w
        ((differentiableAt_const τ).prodMk differentiableAt_id)).differentiableWithinAt
    · beta_reduce
      rw [hNe (τ, w) hw, hw₀]
      ring
  · have hτw : (τ, w₀) ∈ halfPlaneProd \ divisor β := ⟨hτ, hD⟩
    exact ⟨fun w => (w - w₀) * seedPeriodization m α (lambertSeed (e α) (e β) b) τ w,
      (analyticAt_id.sub analyticAt_const).mul
        (analyticAt_seedPeriodization_lambertSeed hm hβ0 hβ1 hb hB hτw),
      Filter.Eventually.of_forall fun w _ => rfl⟩

/-- **Genuine simple poles** for fixed `τ`: if `ρ_Φ(τ) ≠ 0` and `w₀` lies on the orbit
`-β + ℤτ + ℤ`, then `(w - w₀) ℰ_Φ(τ, w)` tends to a nonzero limit as `w → w₀`, `w ≠ w₀`. -/
theorem exists_tendsto_sub_mul_seedPeriodization_lambertSeed (hm : 1 ≤ m) (α : ℚ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : lambertResidue m α (e β) b τ ≠ 0) {w₀ : ℂ}
    (hw₀ : (τ, w₀) ∈ divisor β) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun w => (w - w₀) *
      seedPeriodization m α (lambertSeed (e α) (e β) b) τ w) (𝓝[≠] w₀) (𝓝 L) := by
  obtain ⟨a, k, -, hw⟩ := Set.mem_iUnion₂.mp hw₀
  simp only at hw
  obtain ⟨L, hL, hlim⟩ := seedPeriodization_lambertSeed_pole_genuine hm α hβ0 hβ1 hb hB hτ hρ a k
  refine ⟨L, hL, (hlim.comp (tendsto_sub_nhdsNE w₀)).congr fun w => ?_⟩
  simp only [Function.comp, hw]
  ring_nf

end HigherDyson3
