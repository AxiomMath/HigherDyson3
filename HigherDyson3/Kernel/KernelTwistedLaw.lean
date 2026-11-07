/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# The twisted elliptic law of the kernel

For `x = e(α)`, `q = e(τ)` and `u = e(w)`, the kernel
`𝒦_{m,x}(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} / (1 - x u qⁿ)` satisfies the twisted
elliptic transformation law
`𝒦_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} 𝒦_{m,x}(τ,w)` for all `a, b ∈ ℤ`.

The proof is a reindexing: since `e(b) = 1`, the elliptic variable at `w + aτ + b` is `u qᵃ`,
and the `n`-th summand there equals `x^{2a} q^{-ma²} u^{-2ma}` times the `(n + a)`-th summand
at `w`. Reindexing a sum over `ℤ` by a translation and pulling out a constant factor are
unconditional operations on `tsum` in `ℂ`, so no summability is needed.

## Main results

* `HigherDyson3.kernel_add_mul_add`: the twisted elliptic law of `kernel`.
-/

public section

open Complex

namespace HigherDyson3

private lemma kernelTwistedLaw_e_ne_zero (z : ℂ) : e z ≠ 0 := Complex.exp_ne_zero _

private lemma kernelTwistedLaw_e_add_mul_add (τ w : ℂ) (a b : ℤ) :
    e (w + a * τ + b) = e w * e τ ^ a := by
  have hb : e (b : ℂ) = 1 := by
    unfold e
    rw [show 2 * (Real.pi : ℂ) * I * b = b * (2 * Real.pi * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I b
  have ha : e τ ^ a = e (a * τ) := by
    unfold e
    rw [← Complex.exp_int_mul, show 2 * (Real.pi : ℂ) * I * (a * τ) = a * (2 * Real.pi * I * τ)
      by ring]
  rw [ha]
  unfold e at hb ⊢
  rw [mul_add, mul_add, Complex.exp_add, Complex.exp_add, hb, mul_one]

/-- The twisted elliptic law of the kernel: for `a, b ∈ ℤ`,
`𝒦_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} 𝒦_{m,x}(τ,w)` with `x = e(α)`, `q = e(τ)`,
`u = e(w)`.

The hypotheses `_hm`, `_hα0`, `_hα1` and `_hp` fix the range in which the law is stated; the
proof does not use them, since the identity holds termwise for the unconditional `tsum`. -/
theorem kernel_add_mul_add (m : ℕ) (_hm : 2 ≤ m) (α : ℚ) (_hα0 : 0 ≤ α) (_hα1 : α < 1)
    (τ w : ℂ) (_hp : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    kernel m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        kernel m α τ w := by
  unfold kernel
  rw [kernelTwistedLaw_e_add_mul_add, ← tsum_mul_left,
    ← (Equiv.subRight a).tsum_eq]
  congr 1
  funext r
  simp only [Equiv.subRight_apply]
  have hx := kernelTwistedLaw_e_ne_zero (α : ℂ)
  have hq := kernelTwistedLaw_e_ne_zero τ
  have hu := kernelTwistedLaw_e_ne_zero w
  have hden : e α * (e w * e τ ^ a) * e τ ^ (r - a) = e α * e w * e τ ^ r := by
    rw [mul_assoc (e α), mul_assoc (e w), ← zpow_add₀ hq, add_sub_cancel, mul_assoc]
  rw [hden, mul_zpow, ← zpow_mul, mul_div_assoc', ← mul_assoc, ← mul_assoc]
  congr 1
  have h1 : e α ^ (-2 * (r - a)) = e α ^ (2 * a) * e α ^ (-2 * r) := by
    rw [← zpow_add₀ hx]; ring_nf
  have h3 : e w ^ (2 * (m : ℤ) * (r - a)) =
      e w ^ (-2 * (m : ℤ) * a) * e w ^ (2 * (m : ℤ) * r) := by
    rw [← zpow_add₀ hu]; ring_nf
  have h2 : e τ ^ ((m : ℤ) * (r - a) ^ 2) * e τ ^ (a * (2 * (m : ℤ)) * (r - a)) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e τ ^ ((m : ℤ) * r ^ 2) := by
    rw [← zpow_add₀ hq, ← zpow_add₀ hq]; ring_nf
  rw [h1, h3]
  linear_combination (e α ^ (2 * a) * e α ^ (-2 * r) * e w ^ (-2 * (m : ℤ) * a) *
    e w ^ (2 * (m : ℤ) * r)) * h2

end HigherDyson3
