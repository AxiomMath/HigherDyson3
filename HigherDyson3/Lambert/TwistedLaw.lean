/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.DoubleSummand

/-!
# The twisted elliptic law of a seed periodization

For any seed `Φ(u; q)`, the bilateral periodization
`ℰ_Φ(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} Φ(q^n u; q)` satisfies the twisted law
`ℰ_Φ(τ, w + aτ + k) = x^{2a} q^{-ma²} u^{-2ma} ℰ_Φ(τ, w)` for all `a, k ∈ ℤ`
[AOS, Lemma 7.4(a), proof of Proposition 5.3]: since `e(w + aτ + k) = q^a u`, the shifted series
is the original one reindexed by `n ↦ n + a`, because `m(r-a)² + 2ma(r-a) = mr² - ma²`. The
reindexing only involves the weights and not the seed.

## Main results

* `HigherDyson3.seedPeriodization_twisted_law`: the twisted elliptic law.

## Implementation notes

Reindexing an unconditional `tsum` along an equivalence of `ℤ` and pulling out a constant factor
need no summability, so the identity holds for every seed and every `(τ, w)`.
-/

public section

namespace HigherDyson3

/-- **The twisted elliptic law of a seed periodization.** For every seed `Φ`, `a, k ∈ ℤ`,
`x = e(α)`, `q = e(τ)` and `u = e(w)`,
`ℰ_Φ(τ, w + aτ + k) = x^{2a} q^{-ma²} u^{-2ma} ℰ_Φ(τ, w)`. -/
theorem seedPeriodization_twisted_law (m : ℕ) (α : ℚ) (Φ : ℂ → ℂ → ℂ) (τ w : ℂ) (a k : ℤ) :
    seedPeriodization m α Φ τ (w + a * τ + k) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        seedPeriodization m α Φ τ w := by
  have hq : e τ ≠ 0 := e_ne_zero τ
  have hu : e (w + a * τ + k) = e τ ^ a * e w := by
    rw [← e_mul_e, ← e_mul_e, e_zpow, mul_comm (e (a * τ)) (e w)]
    rw [e_intCast_eq_one]
    ring
  set f : ℤ → ℂ := fun n => e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
    e w ^ (2 * (m : ℤ) * n) * Φ (e τ ^ n * e w) (e τ) with hf
  unfold seedPeriodization
  rw [← hf, ← (Equiv.addRight a).tsum_eq f, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [hf, Equiv.coe_addRight, hu]
  rw [show e τ ^ n * (e τ ^ a * e w) = e τ ^ (n + a) * e w by rw [zpow_add₀ hq]; ring]
  rw [← mul_assoc]
  congr 1
  rw [mul_zpow]
  simp only [e_zpow, e_mul_e]
  congr 1
  push_cast
  ring

end HigherDyson3
