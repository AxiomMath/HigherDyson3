/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.CompactQUBounds

/-!
# Tail of the denominators `1 - x u q^j`

Let `x = e(α)` with `α` real, so that `|x| = 1`. For `(τ, w)` ranging over a compact subset
`S` of `ℍ × ℂ`, write `q = e(τ)` and `u = e(w)`. Then the denominators `1 - x u q^j` are
bounded away from zero uniformly for all large `|j|`: there is `J` with
`|1 - x u q^j| ≥ 1/2` for all `(τ, w) ∈ S` and all `j ∈ ℤ` with `|j| ≥ J`.

Indeed, take `0 < Q₀ ≤ Q < 1` and `0 < a₀ ≤ b₀` bounding `|q|` and `|u|` on `S`, and choose
`J` with `b₀ Q^J ≤ 1/2` and `a₀ Q^{-J} ≥ 2`. For `j ≥ J` one has `|x u q^j| ≤ 1/2`, and for
`j ≤ -J` one has `|x u q^j| ≥ 2`; in both cases `|1 - x u q^j| ≥ 1/2`.

## Main results

* `HigherDyson3.denominator_tail`: the uniform lower bound above.

## Implementation notes

The statement is proved for every real `α`: only `|e(α)| = 1` is used, so the hypotheses
`α ∈ ℚ` and `0 ≤ α < 1` of the source are not needed.
-/

public section

namespace HigherDyson3

/-- `|e(α)| = 1` for real `α`. -/
lemma denominatorTail_norm_e_ofReal (α : ℝ) : ‖e (α : ℂ)‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- On a compact subset `S` of `ℍ × ℂ`, with `x = e(α)`, `q = e(τ)`, `u = e(w)`, the
denominators satisfy `|1 - x u q^j| ≥ 1/2` for all `|j|` large enough, uniformly on `S`. -/
theorem denominator_tail (α : ℝ) (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSH : S ⊆ halfPlaneProd) :
    ∃ J : ℕ, ∀ p ∈ S, ∀ j : ℤ, (J : ℤ) ≤ |j| →
      1 / 2 ≤ ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖ := by
  obtain ⟨Q₀, Q, a₀, b₀, hQ₀, hQ₀Q, hQ1, ha₀, hab, hb⟩ := compact_q_u_bounds S hS hSH
  have hQ : 0 < Q := hQ₀.trans_le hQ₀Q
  have hb₀ : 0 < b₀ := ha₀.trans_le hab
  set c : ℝ := min (1 / (2 * b₀)) (a₀ / 2) with hc
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hcpos hQ1
  refine ⟨J, fun p hp j hj => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hb p hp
  have hq0 : 0 < ‖e p.1‖ := hQ₀.trans_le h1
  have hnorm : ‖e (α : ℂ) * e p.2 * e p.1 ^ j‖ = ‖e p.2‖ * ‖e p.1‖ ^ j := by
    rw [norm_mul, norm_mul, norm_zpow, denominatorTail_norm_e_ofReal, one_mul]
  have hQJ1 : Q ^ J * b₀ ≤ 1 / 2 := by
    have : Q ^ J < 1 / (2 * b₀) := hJ.trans_le (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hQJ2 : Q ^ J ≤ a₀ / 2 := hJ.le.trans (min_le_right _ _)
  rcases le_or_gt 0 j with hj0 | hj0
  · -- `j ≥ J`
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
    rw [abs_of_nonneg hj0] at hj
    have hn : J ≤ n := by exact_mod_cast hj
    have hsmall : ‖e (α : ℂ) * e p.2 * e p.1 ^ (n : ℤ)‖ ≤ 1 / 2 := by
      rw [hnorm, zpow_natCast]
      have h5 : ‖e p.1‖ ^ n ≤ Q ^ J :=
        (pow_le_pow_left₀ hq0.le h2 n).trans (pow_le_pow_of_le_one hQ.le hQ1.le hn)
      calc ‖e p.2‖ * ‖e p.1‖ ^ n ≤ b₀ * Q ^ J :=
            mul_le_mul h4 h5 (by positivity) hb₀.le
        _ ≤ 1 / 2 := by linarith
    have := norm_sub_norm_le (1 : ℂ) (e (α : ℂ) * e p.2 * e p.1 ^ (n : ℤ))
    rw [norm_one] at this
    linarith
  · -- `j ≤ -J`
    obtain ⟨n, hn'⟩ := Int.exists_eq_neg_ofNat hj0.le
    subst hn'
    rw [abs_of_neg hj0, neg_neg] at hj
    have hn : J ≤ n := by exact_mod_cast hj
    have hlarge : 2 ≤ ‖e (α : ℂ) * e p.2 * e p.1 ^ (-(n : ℤ))‖ := by
      rw [hnorm, zpow_neg, zpow_natCast]
      have h5 : ‖e p.1‖ ^ n ≤ Q ^ J :=
        (pow_le_pow_left₀ hq0.le h2 n).trans (pow_le_pow_of_le_one hQ.le hQ1.le hn)
      have hpos : 0 < ‖e p.1‖ ^ n := pow_pos hq0 n
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      nlinarith
    have := norm_sub_norm_le (e (α : ℂ) * e p.2 * e p.1 ^ (-(n : ℤ))) 1
    rw [norm_one, norm_sub_rev] at this
    linarith

end HigherDyson3
