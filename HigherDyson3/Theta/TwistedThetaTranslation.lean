/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Translation of the twisted theta series to the standard one

For integers `m ≥ 2`, `0 ≤ ℓ < 2m`, a rational `0 ≤ α < 1` and `x = e(α)`, translating the
elliptic variable of the twisted theta series by `α / m` recovers the standard theta series up
to an explicit constant:
`T^{[x]}_{m,ℓ}(τ, w + α/m) = e(ℓα/m) q^{-ℓ²/(4m)} ϑ_{m,ℓ}(τ, w)`.

## Main results

* `HigherDyson3.twistedTheta_add_div`: the translation formula above.
-/

public section

open Complex

namespace HigherDyson3

private lemma e_zpow (z : ℂ) (n : ℤ) : e z ^ n = e (n * z) := by
  unfold e
  rw [← Complex.exp_int_mul]
  ring_nf

private lemma e_add' (a b : ℂ) : e (a + b) = e a * e b := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

/-- For `m ≥ 2`, `0 ≤ ℓ < 2m`, a rational `0 ≤ α < 1` and `τ` in the upper half-plane,
`twistedTheta m ℓ α τ (w + α / m) = e(ℓα/m) e(-ℓ²τ/(4m)) theta m ℓ τ w`. -/
theorem twistedTheta_add_div (m ℓ : ℕ) (hm : 2 ≤ m) (_hℓ : ℓ < 2 * m) (α : ℚ)
    (_hα0 : 0 ≤ α) (_hα1 : α < 1) (τ w : ℂ) (_hτ : 0 < τ.im) :
    twistedTheta m ℓ α τ (w + α / m) =
      e (ℓ * α / m) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) * theta m ℓ τ w := by
  have hm0 : (m : ℂ) ≠ 0 := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this.ne'
  unfold twistedTheta theta
  rw [← tsum_mul_left]
  congr 1
  funext j
  simp only [e_zpow, ← e_add']
  congr 1
  push_cast
  field_simp
  ring

end HigherDyson3
