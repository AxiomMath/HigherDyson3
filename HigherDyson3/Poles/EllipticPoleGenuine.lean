/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Poles.EllipticResidue

/-!
# The poles of the periodization are genuine where `ρ_{m,x}` does not vanish

Let `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, `x = e(α)`, and let `τ ∈ ℍ` with `ρ_{m,x}(τ) ≠ 0`.
For `a, b ∈ ℤ` and `w_{a,b} = -α + aτ + b`, the function `ε ↦ ε ℰ_{m,x}(τ, w_{a,b} + ε)` has
a nonzero limit as `ε → 0`, `ε ≠ 0`; so `w_{a,b}` is a genuine (simple) pole of
`ℰ_{m,x}(τ, ·)`.

The limit is the residue `-(ρ_{m,x}(τ) / 2πi) x^{2(m+1)a} q^{-ma²}` with `q = e(τ)`
(`HigherDyson3.periodization_residue`), and each of its factors is nonzero: `ρ_{m,x}(τ)` by
hypothesis, `2πi`, and the powers of `x` and `q` because the exponential never vanishes.

## Main results

* `HigherDyson3.periodization_pole_genuine`: the residue of `ℰ_{m,x}(τ, ·)` at `w_{a,b}` is
  nonzero when `ρ_{m,x}(τ) ≠ 0`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Filter Topology

namespace HigherDyson3

/-- **The poles are genuine where `ρ_{m,x} ≠ 0`.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`,
`τ ∈ ℍ` with `ρ_{m,x}(τ) ≠ 0`, `a, b ∈ ℤ` and `w_{a,b} = -α + aτ + b`, there is `L ≠ 0` with
`ε ℰ_{m,x}(τ, w_{a,b} + ε) → L` as `ε → 0`, `ε ≠ 0`. -/
theorem periodization_pole_genuine {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : rho m α τ ≠ 0) (a b : ℤ) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
        (𝓝 L) := by
  refine ⟨_, ?_, periodization_residue hm hα0 hα1 hτ a b⟩
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have he : ∀ z : ℂ, e z ≠ 0 := fun z => by unfold e; exact Complex.exp_ne_zero _
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hρ h2pi))
    (zpow_ne_zero _ (he _))) (zpow_ne_zero _ (he _))

end HigherDyson3
