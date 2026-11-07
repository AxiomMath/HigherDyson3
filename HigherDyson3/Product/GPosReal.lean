/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GMultipliable

/-!
# Positivity of the untwisted tails

Let `m ≥ 2`, `d = 2m + 1` and `P_d(z) = 1 + z + ⋯ + z^{d-1}`. For real `0 ≤ q < 1` and
`k : ℕ`, the untwisted tail `g_{k,1}(q) = G_d(q^k; q) = ∏_{r ≥ 1} P_d(q^{k+r})` is a positive
real number. Indeed each factor `P_d(q^{k+r})` is a real number at least `1`, since its
constant term is `1` and its other terms are nonnegative; hence every partial product lies in
the closed set `{z : ℂ | 1 ≤ z}`, and so does their limit `G_d(q^k; q)`, by
`HigherDyson3.summable_norm_cyclotomicSum_sub_one_and_tendsto_GProduct`.

## Main results

* `HigherDyson3.one_le_gTail_one`: `1 ≤ g_{k,1}(q)` for real `0 ≤ q < 1`.
* `HigherDyson3.gTail_one_pos`: `g_{k,1}(q)` is a positive real number for real `0 ≤ q < 1`.

## Implementation notes

Positivity is stated with the partial order on `ℂ`, in which `0 < z` means that `z` is real
and positive.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Complex Finset Filter

open scoped ComplexOrder

namespace HigherDyson3

/-- For real `0 ≤ t`, `P_d(t) ≥ 1`. -/
private lemma gPosReal_one_le_cyclotomicSum (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ cyclotomicSum m (t : ℂ) := by
  have h : cyclotomicSum m (t : ℂ) = ((∑ s ∈ range (2 * m + 1), t ^ s : ℝ) : ℂ) := by
    simp [cyclotomicSum]
  rw [h, ← Complex.ofReal_one, Complex.real_le_real]
  rw [Finset.sum_range_succ']
  simp only [pow_zero]
  have : 0 ≤ ∑ s ∈ range (2 * m), t ^ (s + 1) :=
    Finset.sum_nonneg fun s _ => pow_nonneg ht _
  linarith

/-- For real `0 ≤ q < 1`, the untwisted tail satisfies `1 ≤ g_{k,1}(q)`. -/
theorem one_le_gTail_one {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    1 ≤ gTail m 1 k (q : ℂ) := by
  have hq : ‖(q : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq₀]; exact hq₁
  have hlim := (summable_norm_cyclotomicSum_sub_one_and_tendsto_GProduct hm hq
    (1 * (q : ℂ) ^ k)).2
  have hfac : ∀ r : ℕ, 1 ≤ cyclotomicSum m (1 * (q : ℂ) ^ k * (q : ℂ) ^ (r + 1)) := by
    intro r
    have : 1 * (q : ℂ) ^ k * (q : ℂ) ^ (r + 1) = ((q ^ k * q ^ (r + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    exact gPosReal_one_le_cyclotomicSum m (by positivity)
  have hpart : ∀ n : ℕ,
      1 ≤ ∏ r ∈ range n, cyclotomicSum m (1 * (q : ℂ) ^ k * (q : ℂ) ^ (r + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ]
      calc (1 : ℂ) = 1 * 1 := (one_mul 1).symm
        _ ≤ _ := mul_le_mul ih (hfac n) zero_le_one (zero_le_one.trans ih)
  exact ge_of_tendsto' hlim hpart

/-- **Positivity of the untwisted tails.** For `m ≥ 2`, `k : ℕ` and real `0 ≤ q < 1`, the tail
`g_{k,1}(q) = G_d(q^k; q)` is a positive real number. -/
theorem gTail_one_pos {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    0 < gTail m 1 k (q : ℂ) :=
  zero_lt_one.trans_le (one_le_gTail_one hm k hq₀ hq₁)

end HigherDyson3
