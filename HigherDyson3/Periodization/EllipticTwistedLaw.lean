/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# The twisted elliptic law of the periodization

For `m ≥ 2`, `x = e(α)` and `(τ, w) ∈ (ℍ × ℂ) \ 𝒟_x`, the periodization `ℰ_{m,x}` obeys,
for all `a, b ∈ ℤ`, with `q = e(τ)` and `u = e(w)`,
`ℰ_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} ℰ_{m,x}(τ, w)`.

Since `e(w + aτ + b) = u q^a`, the shifted series is the original one reindexed by
`n ↦ n + a`, up to the constant factor above, because `m(r-a)² + 2ma(r-a) = mr² - ma²`.

## Main results

* `HigherDyson3.periodization_twisted_law`: the twisted elliptic law.

## Implementation notes

The periodization is an unconditional `tsum`; reindexing along an equivalence of `ℤ` and
pulling a constant out of a `tsum` need no summability, so the identity holds verbatim
whether or not the series converges. The hypotheses `2 ≤ m`, `0 ≤ α < 1` and
`(τ, w) ∉ 𝒟_x` of the source are kept in the statement, though the proof does not use them.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

noncomputable section

namespace HigherDyson3

private lemma ellipticTwistedLaw_e_add (z w : ℂ) : e (z + w) = e z * e w := by
  unfold e; rw [← Complex.exp_add]; ring_nf

private lemma ellipticTwistedLaw_e_zpow (z : ℂ) (k : ℤ) : e z ^ k = e (k * z) := by
  unfold e; rw [← Complex.exp_int_mul]; ring_nf

private lemma ellipticTwistedLaw_e_int (b : ℤ) : e b = 1 := by
  unfold e
  rw [show 2 * Real.pi * Complex.I * (b : ℂ) = b * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I b

/-- **Twisted elliptic law** of the periodization: for `a, b ∈ ℤ`,
`ℰ_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} ℰ_{m,x}(τ, w)`, where `x = e(α)`,
`q = e(τ)` and `u = e(w)`. -/
@[nolint unusedArguments]
theorem periodization_twisted_law {m : ℕ} (_hm : 2 ≤ m) {α : ℚ} (_hα0 : 0 ≤ α) (_hα1 : α < 1)
    {τ w : ℂ} (_hτw : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    periodization m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        periodization m α τ w := by
  have hq : e τ ≠ 0 := Complex.exp_ne_zero _
  have hu : e (w + a * τ + b) = e τ ^ a * e w := by
    rw [ellipticTwistedLaw_e_add, ellipticTwistedLaw_e_int, mul_one, ellipticTwistedLaw_e_add,
      ellipticTwistedLaw_e_zpow, mul_comm]
  set f : ℤ → ℂ := fun n => e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
    e w ^ (2 * (m : ℤ) * n) * seed m (e α) (e τ ^ n * e w) (e τ) with hf
  unfold periodization
  rw [← hf, ← (Equiv.addRight a).tsum_eq f, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [hf, Equiv.coe_addRight, hu]
  rw [show e τ ^ n * (e τ ^ a * e w) = e τ ^ (n + a) * e w by rw [zpow_add₀ hq]; ring]
  rw [← mul_assoc]
  congr 1
  rw [mul_zpow]
  simp only [ellipticTwistedLaw_e_zpow, ← ellipticTwistedLaw_e_add]
  congr 1
  push_cast
  ring

end HigherDyson3
