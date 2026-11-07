/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Holomorphy.NormalSeriesHolomorphic
public import HigherDyson3.Theta.ThetaNormal

/-!
# Holomorphy of the theta series

For integers `m ≥ 1` and `ℓ ≥ 0`, the function `ϑ_{m,ℓ}(τ, w)` is holomorphic on `ℍ × ℂ`.
Each summand `(τ, w) ↦ e(r_j²τ/(4m)) e(r_j w)`, with `r_j = ℓ + 2mj`, is the exponential of a
polynomial and hence entire, and the series converges normally on compact subsets of `ℍ × ℂ`
by `HigherDyson3.thetaNormal_exists`; a normally convergent series of holomorphic functions is
holomorphic.

## Main results

* `HigherDyson3.differentiableOn_theta`: `ϑ_{m,ℓ}` is holomorphic on `ℍ × ℂ`.

## Implementation notes

The hypothesis `ℓ < 2m` of the source is not needed and is dropped.
-/

public section

namespace HigherDyson3

/-- `ℍ × ℂ` is open in `ℂ × ℂ`. -/
private lemma thetaHolomorphic_isOpen_halfPlaneProd : IsOpen halfPlaneProd :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)

/-- **Holomorphy of the theta series.** For `m ≥ 1`, the function `(τ, w) ↦ ϑ_{m,ℓ}(τ, w)` is
holomorphic on `ℍ × ℂ`. -/
theorem differentiableOn_theta {m : ℕ} (hm : 1 ≤ m) (ℓ : ℕ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => theta m ℓ p.1 p.2) halfPlaneProd := by
  unfold theta
  refine differentiableOn_tsum_of_normal
    (f := fun (j : ℤ) (p : ℂ × ℂ) =>
      e (((ℓ : ℂ) + 2 * m * j) ^ 2 * p.1 / (4 * m)) * e (((ℓ : ℂ) + 2 * m * j) * p.2))
    thetaHolomorphic_isOpen_halfPlaneProd (fun j => ?_) fun K hK hKc => ?_
  · unfold e
    fun_prop
  · obtain ⟨M, hM, -, hle⟩ := thetaNormal_exists hm ℓ K hKc hK
    exact ⟨M, hM, hle⟩

end HigherDyson3
