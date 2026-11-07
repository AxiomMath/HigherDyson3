/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Holomorphy.Osgood

/-!
# Holomorphic dependence of integrals on parameters

Let `f(z, t)` be jointly continuous for `z` in an open set `U` and `t ∈ [a, b]`, and holomorphic
in `z` for each fixed `t`. Then `z ↦ ∫_a^b f(z, t) dt` is holomorphic on `U`. We prove this for
`U ⊆ ℂ` (differentiation under the integral sign, the derivative being bounded on small discs by
the Cauchy estimate) and for `U ⊆ ℂ × ℂ` (by Osgood's lemma `HigherDyson3.osgood`).

## Main results

* `HigherDyson3.continuousOn_intervalIntegral_of_continuousOn`: continuity of a parametric
  integral.
* `HigherDyson3.differentiableOn_intervalIntegral`: one complex parameter.
* `HigherDyson3.differentiableOn_intervalIntegral_prod`: two complex parameters.
-/

public section

open MeasureTheory Metric Filter Topology Set

namespace HigherDyson3

variable {a b : ℝ}

/-- A continuous function on `[a, b]` is a.e.-strongly measurable for the measure of
`Ι a b`. -/
private lemma aestronglyMeasurable_uIoc_of_continuousOn {g : ℝ → ℂ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) : AEStronglyMeasurable g (volume.restrict (uIoc a b)) :=
  (hg.mono (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
    measurableSet_uIoc

/-- **Continuity of parametric integrals.** If `f` is continuous on `U × [a, b]` with `U` open
in a proper metric space, then `x ↦ ∫_a^b f(x, t) dt` is continuous on `U`. -/
theorem continuousOn_intervalIntegral_of_continuousOn {X : Type*} [MetricSpace X]
    [ProperSpace X] {U : Set X} (hU : IsOpen U) {f : X → ℝ → ℂ} (hab : a ≤ b)
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..b, f x t) U := by
  intro x₀ hx₀
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hK : closedBall x₀ (ε / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hε
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedBall x₀ (ε / 2)).prod isCompact_Icc).exists_bound_of_continuousOn
      (hf.mono (prod_mono hK le_rfl))
  have hsl : ∀ x ∈ U, ContinuousOn (f x) (Icc a b) := fun x hx =>
    hf.comp (f := fun t : ℝ => (x, t)) (by fun_prop) fun t ht => ⟨hx, ht⟩
  have hev : ∀ᶠ x in 𝓝 x₀, x ∈ closedBall x₀ (ε / 2) := closedBall_mem_nhds x₀ (by linarith)
  refine (intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M) ?_ ?_
    intervalIntegrable_const ?_).continuousWithinAt
  · filter_upwards [hev] with x hx
    exact aestronglyMeasurable_uIoc_of_continuousOn hab (hsl x (hK hx))
  · filter_upwards [hev] with x hx
    refine ae_of_all _ fun t ht => hM (x, t) ⟨hx, ?_⟩
    rw [uIoc_of_le hab] at ht
    exact Ioc_subset_Icc_self ht
  · refine ae_of_all _ fun t ht => ?_
    rw [uIoc_of_le hab] at ht
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self ht
    have h1 : ContinuousWithinAt (Function.uncurry f) (U ×ˢ Icc a b) (x₀, t) := hf _ ⟨hx₀, ht'⟩
    have h2 : ContinuousWithinAt (fun x => f x t) U x₀ :=
      h1.comp (f := fun x => (x, t)) (by fun_prop) fun x hx => ⟨hx, ht'⟩
    exact h2.continuousAt (hU.mem_nhds hx₀)

/-- **Holomorphy of parametric integrals, one variable.** Let `U ⊆ ℂ` be open and let `f` be
continuous on `U × [a, b]` and holomorphic in `z ∈ U` for each `t ∈ [a, b]`. Then
`z ↦ ∫_a^b f(z, t) dt` is holomorphic on `U`. -/
theorem differentiableOn_intervalIntegral {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ → ℂ}
    (hab : a ≤ b) (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Icc a b))
    (hd : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun z => f z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, f z t) U := by
  intro z₀ hz₀
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set ρ := ε / 3 with hρ
  have ρ0 : 0 < ρ := by positivity
  have hK : closedBall z₀ (2 * ρ) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hε
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedBall z₀ (2 * ρ)).prod isCompact_Icc).exists_bound_of_continuousOn
      (hf.mono (prod_mono hK le_rfl))
  have hsl : ∀ z ∈ U, ContinuousOn (f z) (Icc a b) := fun z hz =>
    hf.comp (f := fun t : ℝ => (z, t)) (by fun_prop) fun t ht => ⟨hz, ht⟩
  have hdiffAt : ∀ t ∈ Icc a b, ∀ z ∈ U, DifferentiableAt ℂ (fun z => f z t) z :=
    fun t ht z hz => (hd t ht).differentiableAt (hU.mem_nhds hz)
  -- the Cauchy estimate for the `z`-derivative on `ball z₀ ρ`
  have hbound : ∀ t ∈ Icc a b, ∀ z ∈ ball z₀ ρ, ‖deriv (fun z => f z t) z‖ ≤ M / ρ := by
    intro t ht z hz
    have hsub : closedBall z ρ ⊆ closedBall z₀ (2 * ρ) := by
      intro y hy
      rw [mem_closedBall] at hy ⊢
      rw [mem_ball] at hz
      linarith [dist_triangle y z z₀]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ρ0
      (DifferentiableOn.diffContOnCl ?_) fun y hy =>
        hM (y, t) ⟨hsub (sphere_subset_closedBall hy), ht⟩
    rw [closure_ball _ ρ0.ne']
    exact (hd t ht).mono (hsub.trans hK)
  -- measurability of the derivative, as a limit of difference quotients
  have hmeas : AEStronglyMeasurable (fun t => deriv (fun z => f z t) z₀)
      (volume.restrict (uIoc a b)) := by
    set zn : ℕ → ℂ := fun n => z₀ + (ρ / (n + 1) : ℝ) with hzn
    have hzn_mem : ∀ n, zn n ∈ U := fun n => hK (by
      rw [mem_closedBall, hzn, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc ρ / (n + 1) ≤ ρ := div_le_self ρ0.le (by linarith [n.cast_nonneg (α := ℝ)])
        _ ≤ 2 * ρ := by linarith)
    have hzn_tend : Tendsto zn atTop (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => ρ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
        have : Tendsto (fun n : ℕ => ((ρ / (n + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
          have := (Complex.continuous_ofReal.tendsto 0).comp h0
          rw [Complex.ofReal_zero] at this
          exact this
        simpa [hzn] using tendsto_const_nhds.add this
      · simp only [hzn, mem_compl_iff, mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero]
        positivity
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => slope (fun z => f z t) z₀ (zn n)) (fun n => ?_) ?_
    · refine aestronglyMeasurable_uIoc_of_continuousOn hab ?_
      simp only [slope_def_module]
      have h1 := hsl _ (hzn_mem n)
      have h2 := hsl _ hz₀
      fun_prop
    · refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun t ht => ?_)
      rw [uIoc_of_le hab] at ht
      exact (hasDerivAt_iff_tendsto_slope.mp
        (hdiffAt t (Ioc_subset_Icc_self ht) z₀ hz₀).hasDerivAt).comp hzn_tend
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ U := hU.mem_nhds hz₀
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z t => deriv (fun z => f z t) z) (bound := fun _ => M / ρ)
    (ball_mem_nhds z₀ ρ0) ?_ ((hsl z₀ hz₀).intervalIntegrable_of_Icc hab) hmeas ?_
    intervalIntegrable_const ?_).2.differentiableAt.differentiableWithinAt
  · filter_upwards [hev] with z hz
    exact aestronglyMeasurable_uIoc_of_continuousOn hab (hsl z hz)
  · refine ae_of_all _ fun t ht z hz => ?_
    rw [uIoc_of_le hab] at ht
    exact hbound t (Ioc_subset_Icc_self ht) z hz
  · refine ae_of_all _ fun t ht z hz => ?_
    rw [uIoc_of_le hab] at ht
    have : z ∈ U := hK (ball_subset_closedBall (ball_subset_ball (by linarith) hz))
    exact (hdiffAt t (Ioc_subset_Icc_self ht) z this).hasDerivAt

/-- **Holomorphy of parametric integrals, two variables.** Let `U ⊆ ℂ × ℂ` be open and let `f`
be continuous on `U × [a, b]` and holomorphic in `p ∈ U` for each `t ∈ [a, b]`. Then
`p ↦ ∫_a^b f(p, t) dt` is holomorphic on `U`. -/
theorem differentiableOn_intervalIntegral_prod {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {f : ℂ × ℂ → ℝ → ℂ} (hab : a ≤ b) (hf : ContinuousOn (Function.uncurry f) (U ×ˢ Icc a b))
    (hd : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun p => f p t) U) :
    DifferentiableOn ℂ (fun p => ∫ t in a..b, f p t) U := by
  refine osgood hU (continuousOn_intervalIntegral_of_continuousOn hU hab hf) ?_ ?_
  · intro p _
    refine differentiableOn_intervalIntegral (f := fun w t => f (p.1, w) t)
      (hU.preimage (by fun_prop)) hab ?_ fun t ht => ?_
    · exact hf.comp (f := fun q : ℂ × ℝ => ((p.1, q.1), q.2)) (by fun_prop)
        fun q hq => ⟨hq.1, hq.2⟩
    · exact (hd t ht).comp (f := fun w => (p.1, w)) (by fun_prop) fun w hw => hw
  · intro p _
    refine differentiableOn_intervalIntegral (f := fun τ t => f (τ, p.2) t)
      (hU.preimage (by fun_prop)) hab ?_ fun t ht => ?_
    · exact hf.comp (f := fun q : ℂ × ℝ => ((q.1, p.2), q.2)) (by fun_prop)
        fun q hq => ⟨hq.1, hq.2⟩
    · exact (hd t ht).comp (f := fun τ => (τ, p.2)) (by fun_prop) fun τ hτ => hτ

end HigherDyson3
