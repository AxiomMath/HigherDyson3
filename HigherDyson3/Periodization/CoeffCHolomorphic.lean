/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCNormal
public import HigherDyson3.Product.GHolomorphic

/-!
# Holomorphy of the theta coefficients `C_{m,ℓ,x}`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ` and `0 ≤ α < 1`, and `0 ≤ ℓ < 2m`. The function
`C_{m,ℓ,x}(τ) = x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}`,
`q = e(τ)`, is holomorphic on the upper half-plane `ℍ`.

Each summand is holomorphic on `ℍ`: `e` is entire and maps `ℍ` into the open unit disk,
where `g_{k,x}` is holomorphic, and the inner sum is a finite sum of integer powers of the
nonvanishing entire function `e`. Around each `τ₀ ∈ ℍ` the closed disk of radius
`Im τ₀ / 2` is a compact subset of `ℍ`, on which the series has a summable majorant
(`HigherDyson3.coeffCNormal_exists`); the Weierstrass `M`-test then gives holomorphy of the
sum near `τ₀`.

## Main results

* `HigherDyson3.differentiableOn_coeffC`: `C_{m,ℓ,x}` is complex differentiable on `ℍ`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex

namespace HigherDyson3

/-- `e` is entire. -/
lemma coeffCHolomorphic_differentiable_e : Differentiable ℂ e := by
  unfold e; fun_prop

/-- `e` does not vanish. -/
lemma coeffCHolomorphic_e_ne_zero (z : ℂ) : e z ≠ 0 :=
  norm_pos_iff.mp (compactQUBounds_norm_e_pos z)

/-- **Holomorphy of `C_{m,ℓ,x}`.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and
`0 ≤ ℓ < 2m`, the function `C_{m,ℓ,x}` is complex differentiable on the upper half-plane. -/
theorem differentiableOn_coeffC {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ℓ : ℕ} (hℓ : ℓ < 2 * m) : DifferentiableOn ℂ (coeffC m ℓ α) upperHalfPlaneSet := by
  intro τ₀ hτ₀
  have hτ₀' : 0 < τ₀.im := hτ₀
  set r : ℝ := τ₀.im / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hSH : Metric.closedBall τ₀ r ⊆ upperHalfPlaneSet := by
    intro τ hτ
    rw [Metric.mem_closedBall, dist_eq_norm] at hτ
    have h := abs_im_le_norm (τ - τ₀)
    rw [sub_im] at h
    change 0 < τ.im
    have := (abs_le.mp (h.trans hτ)).1
    linarith
  obtain ⟨u, hu, -, hle⟩ := coeffCNormal_exists hm hα0 hα1 hℓ _
    (isCompact_closedBall τ₀ r) hSH
  have hD : DifferentiableOn ℂ (fun τ => ∑' k : ℕ, gTail m (e α) k (e τ) *
      ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
        e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s))
      (Metric.ball τ₀ r) := by
    refine differentiableOn_tsum_of_summable_norm hu (fun k => ?_) Metric.isOpen_ball
      (fun k τ hτ => hle k τ (Metric.ball_subset_closedBall hτ))
    refine DifferentiableOn.mul ?_ ?_
    · refine (differentiableOn_gTail hm (e α) k).comp
        coeffCHolomorphic_differentiable_e.differentiableOn fun τ hτ => ?_
      rw [mem_ball_zero_iff]
      exact compactQUBounds_norm_e_lt_one (hSH (Metric.ball_subset_closedBall hτ))
    · refine DifferentiableOn.fun_sum fun s _ => ?_
      refine (differentiableOn_const _).mul ?_
      exact (coeffCHolomorphic_differentiable_e.differentiableOn).zpow
        (Or.inl fun τ _ => coeffCHolomorphic_e_ne_zero τ)
  have hDa := hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))
  exact ((differentiableAt_const _).mul hDa).differentiableWithinAt

end HigherDyson3
