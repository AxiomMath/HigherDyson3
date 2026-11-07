/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Holomorphy.NormalSeriesHolomorphic
public import HigherDyson3.Theta.TwistedThetaNormal

/-!
# Holomorphy of the twisted theta series

Let `m ≥ 1`, `ℓ ≥ 0` be integers and `α ∈ ℚ`. The twisted theta function
`HigherDyson3.twistedTheta m ℓ α`, given by
`∑_{j ∈ ℤ} e(α)^{-2j} e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}`, is holomorphic on `ℍ × ℂ`.
Each summand is a constant times a product of integer powers of the nowhere-vanishing
functions `e(τ)` and `e(w)`, hence holomorphic on `ℂ × ℂ`; the series converges normally on
compact subsets of `ℍ × ℂ` by `HigherDyson3.twistedThetaNormal_exists`, and
`HigherDyson3.differentiableOn_tsum_of_normal` gives holomorphy of the sum.

## Main results

* `HigherDyson3.differentiableOn_twistedTheta`: `(τ, w) ↦ T^{[e(α)]}_{m,ℓ}(τ, w)` is
  holomorphic on `ℍ × ℂ`.

## Implementation notes

The source assumes `m ≥ 2`, `0 ≤ ℓ < 2m` and `0 ≤ α < 1`; only `m ≥ 1` is needed, since
`|e(α)| = 1` for every real `α` and the normal convergence holds for every `m ≥ 1`.
-/

public section

namespace HigherDyson3

/-- `ℍ × ℂ` is open in `ℂ × ℂ`. -/
private lemma twistedThetaHolomorphic_isOpen_halfPlaneProd : IsOpen halfPlaneProd :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)

/-- `e` is entire and never vanishes, so each integer power of it is entire. -/
private lemma twistedThetaHolomorphic_differentiable_e_zpow (n : ℤ) :
    Differentiable ℂ fun z : ℂ => e z ^ n := by
  intro z
  have h : DifferentiableAt ℂ e z := by unfold e; fun_prop
  exact h.zpow (Or.inl (Complex.exp_ne_zero _))

/-- **Holomorphy of the twisted theta series.** For `m ≥ 1`, `ℓ ≥ 0` and `α ∈ ℚ`, the function
`(τ, w) ↦ ∑_{j ∈ ℤ} e(α)^{-2j} e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}` is holomorphic on
`ℍ × ℂ`. -/
theorem differentiableOn_twistedTheta {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) (α : ℚ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => twistedTheta m ℓ α p.1 p.2) halfPlaneProd := by
  unfold twistedTheta
  refine differentiableOn_tsum_of_normal twistedThetaHolomorphic_isOpen_halfPlaneProd
    (fun j => ?_) (fun K hK hKc => ?_)
  · refine Differentiable.differentiableOn ?_
    refine (differentiable_const _).mul ?_ |>.mul ?_
    · exact (twistedThetaHolomorphic_differentiable_e_zpow _).comp differentiable_fst
    · exact (twistedThetaHolomorphic_differentiable_e_zpow _).comp differentiable_snd
  · obtain ⟨M, hM, -, hle⟩ := twistedThetaNormal_exists hm ℓ α K hKc hK
    exact ⟨M, hM, hle⟩

end HigherDyson3
