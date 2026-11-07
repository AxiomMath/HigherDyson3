/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.CompactQUBounds
public import HigherDyson3.Bounds.GaussianSummable

/-!
# A Gaussian majorant for theta-type terms

Let `m ≥ 1` and `ℓ` be integers and let `S ⊆ ℍ × ℂ` be compact. Then
`∑_{j ∈ ℤ} sup_{(τ,w) ∈ S} |e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}| < ∞`.

Writing `q = e(τ)`, `u = e(w)`, on `S` we have `Q₀ ≤ |q| ≤ Q < 1` and `a₀ ≤ |u| ≤ b₀`
with positive constants. For `x > 0` and `T ≥ max(x, x⁻¹)` one has `x^k ≤ T^{|k|}` for
every integer `k`. Hence the `j`-th term is bounded on `S` by
`B^{|ℓ|} Q^{m j²} (A^{|ℓ|} B^{2m})^{|j|}` with `A = Q₀⁻¹ ≥ 1`, `B = max(1, b₀, a₀⁻¹)`,
and this majorant is summable over `ℤ` by `HigherDyson3.gaussian_summable`.

## Main results

* `HigherDyson3.thetaTermMajorant_exists`: there is a summable `M : ℤ → ℝ` dominating the
  `j`-th term uniformly on `S`.
* `HigherDyson3.theta_term_majorant`: the sum over `j` of the suprema over `S` is finite.

## Implementation notes

The supremum is taken in `ℝ≥0∞`, so the statement `∑' j, ⨆ p ∈ S, ‖·‖₊ < ∞` is the literal
finiteness of the sum of suprema, with no boundedness side conditions. Exponents are
integers, and the powers are `zpow`.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- For `x > 0` and `T` dominating both `x` and `x⁻¹`, `x ^ k ≤ T ^ |k|` for every integer
`k`. -/
lemma thetaTermMajorant_zpow_le {x T : ℝ} (hx : 0 < x) (hxT : x ≤ T) (hxT' : x⁻¹ ≤ T)
    (k : ℤ) : x ^ k ≤ T ^ k.natAbs := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [zpow_natCast, Int.natAbs_natCast]
    exact pow_le_pow_left₀ hx.le hxT n
  · simp only [zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hxT' n

/-- A summable majorant for the theta-type terms `e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}`,
uniform over a compact subset of `ℍ × ℂ`. -/
theorem thetaTermMajorant_exists {m : ℤ} (hm : 1 ≤ m) (ℓ : ℤ) (S : Set (ℂ × ℂ))
    (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∃ M : ℤ → ℝ, Summable M ∧ (∀ j, 0 ≤ M j) ∧ ∀ j : ℤ, ∀ p ∈ S,
      ‖e p.1 ^ (m * j ^ 2 + ℓ * j) * e p.2 ^ (ℓ + 2 * m * j)‖ ≤ M j := by
  obtain ⟨Q₀, Q, a₀, b₀, hQ₀, hQ₀Q, hQ1, ha₀, ha₀b₀, hb⟩ := compact_q_u_bounds S hS hSH
  set A : ℝ := Q₀⁻¹
  set B : ℝ := max 1 (max b₀ a₀⁻¹)
  have hA : 1 ≤ A := (one_le_inv₀ hQ₀).mpr (by linarith)
  have hB : 1 ≤ B := le_max_left _ _
  have hQ0 : 0 ≤ Q := by linarith
  have hm' : 1 ≤ m.toNat := by omega
  refine ⟨fun j => B ^ ℓ.natAbs *
      (Q ^ (m.toNat * j.natAbs ^ 2) * (A ^ ℓ.natAbs * B ^ (2 * m.toNat)) ^ j.natAbs),
    (gaussian_summable hm' hQ0 hQ1 (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA)
      (one_le_pow₀ hB))).mul_left _, fun j => by positivity, ?_⟩
  intro j p hp
  obtain ⟨h1, h2, h3, h4⟩ := hb p hp
  set r := ‖e p.1‖
  set s := ‖e p.2‖
  have hr : 0 < r := lt_of_lt_of_le hQ₀ h1
  have hs : 0 < s := lt_of_lt_of_le ha₀ h3
  have hrA : r ≤ A := le_trans (by linarith) hA
  have hrA' : r⁻¹ ≤ A := inv_anti₀ hQ₀ h1
  have hsB : s ≤ B := le_trans h4 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hsB' : s⁻¹ ≤ B :=
    le_trans (inv_anti₀ ha₀ h3) (le_trans (le_max_right _ _) (le_max_right _ _))
  rw [norm_mul, norm_zpow, norm_zpow, zpow_add₀ hr.ne']
  -- quadratic part
  have hq : r ^ (m * j ^ 2) ≤ Q ^ (m.toNat * j.natAbs ^ 2) := by
    have hcast : m * j ^ 2 = ((m.toNat * j.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (by omega), sq_abs]
    rw [hcast, zpow_natCast]
    exact pow_le_pow_left₀ hr.le h2 _
  -- linear part in `q`
  have hl : r ^ (ℓ * j) ≤ (A ^ ℓ.natAbs) ^ j.natAbs := by
    refine (thetaTermMajorant_zpow_le hr hrA hrA' _).trans ?_
    rw [Int.natAbs_mul, pow_mul]
  -- the `u` part
  have hu : s ^ (ℓ + 2 * m * j) ≤ B ^ ℓ.natAbs * (B ^ (2 * m.toNat)) ^ j.natAbs := by
    refine (thetaTermMajorant_zpow_le hs hsB hsB' _).trans ?_
    rw [← pow_mul, ← pow_add]
    refine pow_le_pow_right₀ hB ?_
    have : (2 * m * j).natAbs = 2 * m.toNat * j.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
      have hmm : m.natAbs = m.toNat := by omega
      simp [hmm]
    have := Int.natAbs_add_le ℓ (2 * m * j)
    omega
  have hq0 : 0 ≤ r ^ (m * j ^ 2) := zpow_nonneg hr.le _
  have hl0 : 0 ≤ r ^ (ℓ * j) := zpow_nonneg hr.le _
  have hu0 : 0 ≤ s ^ (ℓ + 2 * m * j) := zpow_nonneg hs.le _
  calc r ^ (m * j ^ 2) * r ^ (ℓ * j) * s ^ (ℓ + 2 * m * j)
      ≤ Q ^ (m.toNat * j.natAbs ^ 2) * (A ^ ℓ.natAbs) ^ j.natAbs *
          (B ^ ℓ.natAbs * (B ^ (2 * m.toNat)) ^ j.natAbs) := by
        gcongr
    _ = _ := by dsimp only; rw [mul_pow]; ring

/-- **Gaussian majorant for theta-type terms.** For integers `m ≥ 1`, `ℓ` and a compact
`S ⊆ ℍ × ℂ`, `∑_{j ∈ ℤ} sup_{(τ,w) ∈ S} |e(τ)^{m j² + ℓ j} e(w)^{ℓ + 2 m j}| < ∞`. -/
theorem theta_term_majorant {m : ℤ} (hm : 1 ≤ m) (ℓ : ℤ) (S : Set (ℂ × ℂ))
    (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∑' j : ℤ, ⨆ p ∈ S,
      (‖e p.1 ^ (m * j ^ 2 + ℓ * j) * e p.2 ^ (ℓ + 2 * m * j)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ := thetaTermMajorant_exists hm ℓ S hS hSH
  calc ∑' j : ℤ, ⨆ p ∈ S,
        (‖e p.1 ^ (m * j ^ 2 + ℓ * j) * e p.2 ^ (ℓ + 2 * m * j)‖₊ : ℝ≥0∞)
      ≤ ∑' j : ℤ, ENNReal.ofReal (M j) := by
        refine ENNReal.tsum_le_tsum fun j => iSup₂_le fun p hp => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle j p hp)
    _ = ENNReal.ofReal (∑' j, M j) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
