/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Bounds.CompactQUBounds
public import HigherDyson3.Product.GBound

/-!
# Normal convergence of the series defining `ρ_{m,x}`

Let `m ≥ 2`, `d = 2m + 1`, `α ∈ ℚ` and `x = e(α)`. For every compact
`S ⊆ ℍ`, writing `q = e(τ)`,
`∑_{k ≥ 0} sup_{τ ∈ S} |x^{2(m+1)k} q^{(m+1)k²} g_{k,x}(q)| < ∞`.

On a compact subset of `ℍ` the modulus `|q| = |e(τ)|` is bounded by some `Q < 1`, so the
tails `g_{k,x}(q)` are bounded by a constant `C` uniformly in `k` and `τ ∈ S`
(`HigherDyson3.exists_bound_norm_gTail`, using `|x| = 1`). Hence the `k`-th term is at most
`C Q^{(m+1)k²} ≤ C Q^k`, a summable geometric majorant.

## Main results

* `HigherDyson3.rhoNormal_exists_majorant`: there is a summable `M : ℕ → ℝ` dominating the
  `k`-th term uniformly on `S`.
* `HigherDyson3.rho_normal`: the sum over `k` of the suprema over `S` is finite.

## Implementation notes

The supremum is taken in `ℝ≥0∞`, so the statement `∑' k, ⨆ τ ∈ S, ‖·‖₊ < ∞` is the literal
finiteness of the sum of suprema, with no boundedness side conditions.

The source restricts to `0 ≤ α < 1`; the argument only uses `|e(α)| = 1`, valid for every
rational (indeed real) `α`, so no restriction on `α` is imposed.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- `|e(t)| = 1` for real `t`. -/
lemma rhoNormal_norm_e_ofReal (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- On a compact subset of `ℍ`, `|e(τ)|` is bounded by a constant `Q` with `0 ≤ Q < 1`. -/
lemma rhoNormal_exists_norm_e_le (S : Set ℂ) (hS : IsCompact S)
    (hSH : S ⊆ upperHalfPlaneSet) :
    ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧ ∀ τ ∈ S, ‖e τ‖ ≤ Q := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, one_pos, fun τ hτ => hτ.elim⟩
  obtain ⟨τ₀, hτ₀, hmax⟩ := hS.exists_isMaxOn hne
    (continuous_norm.comp compactQUBounds_continuous_e).continuousOn
  exact ⟨‖e τ₀‖, norm_nonneg _, compactQUBounds_norm_e_lt_one (hSH hτ₀),
    fun τ hτ => hmax hτ⟩

/-- A summable majorant for the terms `x^{2(m+1)k} q^{(m+1)k²} g_{k,x}(q)` of the series
defining `ρ_{m,x}`, uniform over a compact subset of `ℍ`. -/
theorem rhoNormal_exists_majorant {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (S : Set ℂ)
    (hS : IsCompact S) (hSH : S ⊆ upperHalfPlaneSet) :
    ∃ M : ℕ → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧ ∀ k : ℕ, ∀ τ ∈ S,
      ‖e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) * gTail m (e α) k (e τ)‖ ≤ M k := by
  obtain ⟨Q, hQ0, hQ1, hQ⟩ := rhoNormal_exists_norm_e_le S hS hSH
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm hQ0 hQ1 zero_le_one
  have hx : ‖e (α : ℂ)‖ = 1 := by simpa using rhoNormal_norm_e_ofReal (α : ℝ)
  refine ⟨fun k => Q ^ k * C, (summable_geometric_of_lt_one hQ0 hQ1).mul_right C,
    fun k => by positivity, fun k τ hτ => ?_⟩
  have hk : k ≤ (m + 1) * k ^ 2 :=
    (Nat.le_self_pow two_ne_zero k).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos m))
  rw [norm_mul, norm_mul, norm_pow, norm_pow, hx, one_pow, one_mul]
  beta_reduce
  gcongr
  · exact (pow_le_pow_left₀ (norm_nonneg _) (hQ τ hτ) _).trans
      (pow_le_pow_of_le_one hQ0 hQ1.le hk)
  · exact hC k _ (hQ τ hτ) _ hx.le

/-- **Normal convergence of the series defining `ρ_{m,x}`.** For `m ≥ 2`, `α ∈ ℚ`,
`x = e(α)` and a compact `S ⊆ ℍ`,
`∑_{k ≥ 0} sup_{τ ∈ S} |x^{2(m+1)k} q^{(m+1)k²} g_{k,x}(q)| < ∞` with `q = e(τ)`. -/
theorem rho_normal {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (S : Set ℂ)
    (hS : IsCompact S) (hSH : S ⊆ upperHalfPlaneSet) :
    ∑' k : ℕ, ⨆ τ ∈ S, (‖e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) *
      gTail m (e α) k (e τ)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ := rhoNormal_exists_majorant hm α S hS hSH
  calc ∑' k : ℕ, ⨆ τ ∈ S, (‖e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) *
        gTail m (e α) k (e τ)‖₊ : ℝ≥0∞)
      ≤ ∑' k : ℕ, ENNReal.ofReal (M k) := by
        refine ENNReal.tsum_le_tsum fun k => iSup₂_le fun τ hτ => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle k τ hτ)
    _ = ENNReal.ofReal (∑' k, M k) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

end HigherDyson3
