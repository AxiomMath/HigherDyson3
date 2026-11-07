/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.RhoNormal
public import HigherDyson3.Product.GHolomorphic

/-!
# Holomorphy of `ρ_{m,x}` on the upper half-plane

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` and `x = e(α)`. The function
`ρ_{m,x}(τ) = x^{-2} ∑_{k ≥ 0} x^{2(m+1)k} q^{(m+1)k²} g_{k,x}(q)`, `q = e(τ)`,
is holomorphic on `ℍ`.

Each summand is holomorphic on `ℍ`: `e` is entire and maps `ℍ` into the open unit disk, on
which `g_{k,x}` is holomorphic (`HigherDyson3.differentiableOn_gTail`). On a closed disk
around a point of `ℍ` and contained in `ℍ` the series has a summable majorant
(`HigherDyson3.rhoNormal_exists_majorant`), so by the Weierstrass `M`-test its sum is
holomorphic on the open disk, hence complex differentiable at its centre.

## Main results

* `HigherDyson3.rho_holomorphic`: `ρ_{m,x}` is complex differentiable on `ℍ`.

## Implementation notes

The source restricts to `0 ≤ α < 1`; the argument only uses `|e(α)| = 1`, valid for every
rational `α`, so no restriction on `α` is imposed.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex

namespace HigherDyson3

/-- `e` is entire. -/
lemma ellipticRhoHolomorphic_differentiable_e : Differentiable ℂ e := by
  unfold e; fun_prop

/-- **Holomorphy of `ρ_{m,x}`.** For `m ≥ 2` and `α ∈ ℚ`, the function `ρ_{m,e(α)}` is
complex differentiable on the upper half-plane. -/
theorem rho_holomorphic {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    DifferentiableOn ℂ (rho m α) upperHalfPlaneSet := by
  intro τ₀ hτ₀
  have him : 0 < τ₀.im := hτ₀
  set r : ℝ := τ₀.im / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : Metric.closedBall τ₀ r ⊆ upperHalfPlaneSet := by
    intro τ hτ
    rw [Metric.mem_closedBall, Complex.dist_eq] at hτ
    have h1 : |(τ - τ₀).im| ≤ ‖τ - τ₀‖ := Complex.abs_im_le_norm _
    have h2 : (τ - τ₀).im = τ.im - τ₀.im := Complex.sub_im _ _
    change 0 < τ.im
    rw [h2] at h1
    have := neg_abs_le (τ.im - τ₀.im)
    linarith
  obtain ⟨M, hM, -, hle⟩ := rhoNormal_exists_majorant hm α _
    (isCompact_closedBall τ₀ r) hball
  have hD : DifferentiableOn ℂ (fun τ => ∑' k : ℕ, e α ^ (2 * (m + 1) * k) *
      e τ ^ ((m + 1) * k ^ 2) * gTail m (e α) k (e τ)) (Metric.ball τ₀ r) := by
    refine differentiableOn_tsum_of_summable_norm hM (fun k => ?_) Metric.isOpen_ball
      (fun k τ hτ => hle k τ (Metric.ball_subset_closedBall hτ))
    refine (((ellipticRhoHolomorphic_differentiable_e.pow _).const_mul _).differentiableOn).mul
      ?_
    refine (differentiableOn_gTail hm (e α) k).comp
      ellipticRhoHolomorphic_differentiable_e.differentiableOn (fun τ hτ => ?_)
    rw [mem_ball_zero_iff]
    exact compactQUBounds_norm_e_lt_one
      (hball (Metric.ball_subset_closedBall hτ))
  have hDa := hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))
  exact ((differentiableAt_const _).mul hDa).differentiableWithinAt

end HigherDyson3
