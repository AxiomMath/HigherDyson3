/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-!
# Osgood's lemma in two variables

Let `U ⊆ ℂ × ℂ` be open and let `f : ℂ × ℂ → ℂ` be continuous on `U` and holomorphic in each
variable separately. Then `f` is jointly complex differentiable on `U`.

## Main results

* `HigherDyson3.osgood`: a continuous, separately holomorphic function on an open subset of
  `ℂ × ℂ` is complex differentiable there.

## Implementation notes

The usual proof expands `f` as a double power series through a double Cauchy integral. We argue
instead directly with the derivative. At `(τ, w) ∈ U`, with `a` and `b` the two partial
derivatives, write
`f (τ + h, w + k) - f (τ, w) - a h - b k = [ψₕ (w + k) - ψₕ w] + [f (τ, w + k) - f (τ, w) - b k]
  + [f (τ + h, w) - f (τ, w) - a h]`, where `ψₕ z = f (τ + h, z) - f (τ, z)`.
The last two brackets are `o(‖(h, k)‖)` by separate differentiability. On a closed polydisc of
radius `r` about `(τ, w)` contained in `U`, uniform continuity of `f` makes `sup ‖ψₕ‖` small with
`h`; the Cauchy estimate on discs of radius `r / 2` then bounds `‖ψₕ'‖` on the disc of radius
`r / 2` about `w`, and the mean value inequality bounds the first bracket by a small multiple
of `‖k‖`.

## References

* W. F. Osgood, *Note über analytische Functionen mehrerer Veränderlichen*, Math. Ann. 52 (1899)
-/

public section

open Metric Filter Topology

namespace HigherDyson3

/-- **Osgood's lemma** in two variables: a function on an open subset of `ℂ × ℂ` which is
continuous and holomorphic in each variable separately is jointly complex differentiable. -/
theorem osgood {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (h₁ : ∀ p ∈ U, DifferentiableOn ℂ (fun w => f (p.1, w)) {w | (p.1, w) ∈ U})
    (h₂ : ∀ p ∈ U, DifferentiableOn ℂ (fun τ => f (τ, p.2)) {τ | (τ, p.2) ∈ U}) :
    DifferentiableOn ℂ f U := by
  rintro ⟨τ, w⟩ hp
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.mp hU _ hp
  set r := ε / 2 with hr
  have r0 : 0 < r := by positivity
  have hK : closedBall τ r ×ˢ closedBall w r ⊆ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply hε
    rw [Metric.mem_closedBall] at hx hy
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (by simp only; linarith) (by simp only; linarith)
  have huc := ((isCompact_closedBall τ r).prod
    (isCompact_closedBall w r)).uniformContinuousOn_of_continuous (hf.mono hK)
  -- differentiability of a slice at a point of `U`
  have hsl₁ : ∀ x y, (x, y) ∈ U → DifferentiableAt ℂ (fun z => f (x, z)) y := fun x y hxy =>
    (h₁ _ hxy).differentiableAt ((hU.preimage (by fun_prop)).mem_nhds hxy)
  have hsl₂ : ∀ x y, (x, y) ∈ U → DifferentiableAt ℂ (fun t => f (t, y)) x := fun x y hxy =>
    (h₂ _ hxy).differentiableAt ((hU.preimage (by fun_prop)).mem_nhds hxy)
  set a := deriv (fun t => f (t, w)) τ
  set b := deriv (fun z => f (τ, z)) w
  refine ⟨a • ContinuousLinearMap.fst ℂ ℂ ℂ + b • ContinuousLinearMap.snd ℂ ℂ ℂ, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have e1 := (hasDerivAt_iff_isLittleO_nhds_zero.mp (hsl₂ τ w hp).hasDerivAt).def
    (by positivity : 0 < c / 3)
  have e2 := (hasDerivAt_iff_isLittleO_nhds_zero.mp (hsl₁ τ w hp).hasDerivAt).def
    (by positivity : 0 < c / 3)
  obtain ⟨δ, δ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc (c * r / 6) (by positivity)
  have e1' : ∀ᶠ q : ℂ × ℂ in 𝓝 0, ‖f (τ + q.1, w) - f (τ, w) - q.1 • a‖ ≤ c / 3 * ‖q.1‖ :=
    (continuous_fst.tendsto' (0 : ℂ × ℂ) 0 rfl).eventually e1
  have e2' : ∀ᶠ q : ℂ × ℂ in 𝓝 0, ‖f (τ, w + q.2) - f (τ, w) - q.2 • b‖ ≤ c / 3 * ‖q.2‖ :=
    (continuous_snd.tendsto' (0 : ℂ × ℂ) 0 rfl).eventually e2
  have e3 : ∀ᶠ q : ℂ × ℂ in 𝓝 0, ‖q‖ < min δ (r / 2) :=
    Metric.eventually_nhds_iff.mpr ⟨min δ (r / 2), by positivity, fun q hq => by simpa using hq⟩
  filter_upwards [e1', e2', e3] with q h1 h2 h3
  obtain ⟨h, k⟩ := q
  simp only at h1 h2
  have hh : ‖h‖ < min δ (r / 2) := lt_of_le_of_lt (norm_fst_le (h, k)) h3
  have hk : ‖k‖ < min δ (r / 2) := lt_of_le_of_lt (norm_snd_le (h, k)) h3
  have hhr : ‖h‖ < r := by have := min_le_right δ (r / 2); linarith
  have hτh : τ + h ∈ closedBall τ r := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hhr.le
  set ψ : ℂ → ℂ := fun z => f (τ + h, z) - f (τ, z) with hψ
  have hψb : ∀ z ∈ closedBall w r, ‖ψ z‖ ≤ c * r / 6 := by
    intro z hz
    have := hδ (τ + h, z) ⟨hτh, hz⟩ (τ, z) ⟨Metric.mem_closedBall_self r0.le, hz⟩ (by
      rw [Prod.dist_eq, dist_eq_norm, dist_self]
      simp only [add_sub_cancel_left, norm_nonneg, sup_of_le_left]
      exact lt_of_lt_of_le hh (min_le_left _ _))
    rw [dist_eq_norm] at this
    exact this.le
  have hψd : ∀ z ∈ closedBall w r, DifferentiableAt ℂ ψ z := fun z hz =>
    (hsl₁ _ _ (hK ⟨hτh, hz⟩)).sub (hsl₁ _ _ (hK ⟨Metric.mem_closedBall_self r0.le, hz⟩))
  have hψ' : ∀ z ∈ ball w (r / 2), ‖deriv ψ z‖ ≤ c / 3 := by
    intro z hz
    have hsub : closedBall z (r / 2) ⊆ closedBall w r := by
      intro y hy
      rw [Metric.mem_closedBall] at hy ⊢
      rw [Metric.mem_ball] at hz
      linarith [dist_triangle y z w]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos r0)
      (DifferentiableOn.diffContOnCl (by
        rw [closure_ball _ (half_pos r0).ne']
        exact fun y hy => (hψd y (hsub hy)).differentiableWithinAt))
      (fun y hy => hψb y (hsub (Metric.sphere_subset_closedBall hy)))
    calc ‖deriv ψ z‖ ≤ c * r / 6 / (r / 2) := this
      _ = c / 3 := by field_simp; ring
  have hmv := (convex_ball w (r / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hψd z (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith) hz))) hψ'
    (Metric.mem_ball_self (half_pos r0)) (y := w + k)
    (by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact lt_of_lt_of_le hk (min_le_right _ _))
  simp only [hψ, add_sub_cancel_left] at hmv
  have hnorm : ‖(h, k)‖ = max ‖h‖ ‖k‖ := rfl
  simp only [Prod.mk_add_mk, add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, hnorm] at h1 h2 ⊢
  calc ‖f (τ + h, w + k) - f (τ, w) - (a * h + b * k)‖
      = ‖(f (τ + h, w + k) - f (τ, w + k) - (f (τ + h, w) - f (τ, w)))
          + (f (τ, w + k) - f (τ, w) - k * b) + (f (τ + h, w) - f (τ, w) - h * a)‖ := by
        congr 1; ring
    _ ≤ c / 3 * ‖k‖ + c / 3 * ‖k‖ + c / 3 * ‖h‖ := by
        refine (norm_add₃_le).trans (add_le_add (add_le_add hmv h2) h1)
    _ ≤ c * max ‖h‖ ‖k‖ := by
        have := le_max_left ‖h‖ ‖k‖
        have := le_max_right ‖h‖ ‖k‖
        nlinarith

end HigherDyson3
