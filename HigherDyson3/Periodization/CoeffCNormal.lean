/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.CompactQUBounds
public import HigherDyson3.Product.GBound

/-!
# Normal convergence of the series defining the theta coefficients `C_{m,ℓ,x}`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ`, and `0 ≤ ℓ < 2m`. For a compact `S ⊆ ℍ` and
`q = e(τ)`,
`∑_{k ≥ 1} sup_{τ ∈ S} |g_{k,x}(q) ∑_{s=1}^{k} x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}| < ∞`.

For `1 ≤ s ≤ k` the exponent `(m+1)k² - ms² + ℓs = k² + m(k² - s²) + ℓs` is at least
`k² ≥ k`. By compactness there is `Q < 1` with `|q| ≤ Q` on `S`, and by
`HigherDyson3.exists_bound_norm_gTail` the tails `g_{k,x}(q)` are bounded by a constant `B`
on `S`, uniformly in `k`. Since `|x| = 1`, the `k`-th term is at most `B k Q^k` on `S`,
and `∑ k Q^k < ∞`.

## Main results

* `HigherDyson3.coeffCNormal_exists`: a summable majorant for the `k`-th summand of
  `HigherDyson3.coeffC`, uniform over `S`.
* `HigherDyson3.coeffC_normal`: the sum over `k` of the suprema over `S` is finite.

## Implementation notes

The sum runs over all `k : ℕ`; the summand for `k = 0` is an empty sum, so this is the sum
over `k ≥ 1`. The supremum is taken in `ℝ≥0∞`. The bound uses neither `0 ≤ α < 1` nor
`ℓ < 2m`; only `ℓ ≥ 0` and `α` real matter.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- `|e(α)| = 1` for real `α`. -/
lemma coeffCNormal_norm_e_ofReal (α : ℝ) : ‖e α‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- On a compact subset of `ℍ`, `|e(τ)|` is bounded by a constant `Q < 1`. -/
lemma coeffCNormal_exists_norm_e_le (S : Set ℂ) (hS : IsCompact S)
    (hSH : S ⊆ upperHalfPlaneSet) : ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧ ∀ τ ∈ S, ‖e τ‖ ≤ Q := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, zero_lt_one, by simp⟩
  obtain ⟨τ₀, hτ₀, hmax⟩ := hS.exists_isMaxOn hne
    (compactQUBounds_continuous_e.norm.continuousOn)
  exact ⟨‖e τ₀‖, norm_nonneg _, compactQUBounds_norm_e_lt_one (hSH hτ₀), fun τ hτ => hmax hτ⟩

/-- A summable majorant for the `k`-th summand of `HigherDyson3.coeffC`, uniform over a
compact subset of `ℍ`. -/
theorem coeffCNormal_exists {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (_hα0 : 0 ≤ α) (_hα1 : α < 1)
    {ℓ : ℕ} (_hℓ : ℓ < 2 * m) (S : Set ℂ) (hS : IsCompact S)
    (hSH : S ⊆ upperHalfPlaneSet) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ k, 0 ≤ u k) ∧ ∀ k : ℕ, ∀ τ ∈ S,
      ‖gTail m (e α) k (e τ) *
        ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
          e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)‖ ≤ u k := by
  obtain ⟨Q, hQ0, hQ1, hQ⟩ := coeffCNormal_exists_norm_e_le S hS hSH
  obtain ⟨B, hB0, hB⟩ := exists_bound_norm_gTail hm hQ0 hQ1 zero_le_one
  have hx : ‖e α‖ = 1 := by exact_mod_cast coeffCNormal_norm_e_ofReal α
  refine ⟨fun k => B * ((k : ℝ) ^ 1 * Q ^ k),
    (summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_of_nonneg hQ0])).mul_left B, fun k => by positivity, ?_⟩
  intro k τ hτ
  have hq := hQ τ hτ
  have hq0 : 0 ≤ ‖e τ‖ := norm_nonneg _
  rw [norm_mul]
  refine mul_le_mul (hB k _ hq _ hx.le) ?_ (norm_nonneg _) hB0
  rw [pow_one]
  calc _ ≤ ∑ s ∈ Finset.Icc 1 k, ‖e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
          e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ Finset.Icc 1 k, Q ^ k := by
        refine Finset.sum_le_sum fun s hs => ?_
        obtain ⟨hs1, hsk⟩ := Finset.mem_Icc.mp hs
        rw [norm_mul, norm_zpow, norm_zpow, hx, one_zpow, one_mul]
        set N : ℤ := ((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s
        have hN : (k : ℤ) ≤ N := by
          have hsk' : (s : ℤ) ≤ k := by exact_mod_cast hsk
          nlinarith [mul_nonneg (Int.natCast_nonneg m)
            (mul_nonneg (sub_nonneg.2 hsk') (by positivity : (0 : ℤ) ≤ k + s)),
            Int.natCast_nonneg (ℓ * s)]
        rw [← Int.toNat_of_nonneg (by omega : 0 ≤ N), zpow_natCast]
        calc ‖e τ‖ ^ N.toNat ≤ ‖e τ‖ ^ k :=
              pow_le_pow_of_le_one hq0 (hq.trans hQ1.le) (by omega)
          _ ≤ Q ^ k := pow_le_pow_left₀ hq0 hq k
    _ = k * Q ^ k := by simp

/-- **Normal convergence of the series for `C_{m,ℓ,x}`.** For `m ≥ 2`, `α ∈ ℚ` with
`0 ≤ α < 1`, `0 ≤ ℓ < 2m` and a compact `S ⊆ ℍ`,
`∑_{k ≥ 1} sup_{τ ∈ S} |g_{k,x}(q) ∑_{s=1}^{k} x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}| < ∞`
with `x = e(α)` and `q = e(τ)`. The summand for `k = 0` is an empty sum, so the sum over
`k : ℕ` is the sum over `k ≥ 1`. -/
theorem coeffC_normal {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) {ℓ : ℕ}
    (hℓ : ℓ < 2 * m) (S : Set ℂ) (hS : IsCompact S) (hSH : S ⊆ upperHalfPlaneSet) :
    ∑' k : ℕ, ⨆ τ ∈ S, (‖gTail m (e α) k (e τ) *
      ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
        e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨u, hu, hu0, hle⟩ := coeffCNormal_exists hm hα0 hα1 hℓ S hS hSH
  calc _ ≤ ∑' k : ℕ, ENNReal.ofReal (u k) := by
        refine ENNReal.tsum_le_tsum fun k => iSup₂_le fun τ hτ => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle k τ hτ)
    _ = ENNReal.ofReal (∑' k, u k) := (ENNReal.ofReal_tsum_of_nonneg hu0 hu).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
