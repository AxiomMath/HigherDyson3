/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.RhoNormal
public import HigherDyson3.Product.GLeading

/-!
# Leading term of `ρ_{m,x}` at the cusp

Let `m ≥ 2`, `α ∈ ℚ` and `x = e(α)`. There are constants `C > 0` and `T > 0` with
`|ρ_{m,x}(τ) - x⁻²| ≤ C |e(τ)|` for all `τ ∈ ℍ` with `Im τ ≥ T`.

Writing `q = e(τ)`, the series defining `ρ_{m,x}` converges absolutely, so its `k = 0` term
`g_{0,x}(q)` may be split off. By the leading-term estimate for the tails,
`|g_{0,x}(q) - 1| ≤ C₀ |q|` for small `|q|`; by the uniform bound on the tails,
`|g_{k,x}(q)| ≤ B` for `|q| ≤ 1/2`, so that, using `|x| = 1` and `(m+1)k² ≥ k`, the
remaining terms contribute at most `B ∑_{k ≥ 1} |q|^k ≤ 2B|q|`.

## Main results

* `HigherDyson3.rho_leading`: `ρ_{m,x}(τ) = x⁻² + O(|e(τ)|)` as `Im τ → ∞`.

## Implementation notes

The source restricts to `0 ≤ α < 1`; the argument only uses `|e(α)| = 1`, valid for every
rational `α`, so no restriction on `α` is imposed.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

namespace HigherDyson3

/-- `|e(τ)| = exp(-2π Im τ)`. -/
lemma ellipticRhoLeading_norm_e (τ : ℂ) : ‖e τ‖ = Real.exp (-2 * Real.pi * τ.im) := by
  unfold e
  rw [Complex.norm_exp]
  congr 1
  simp

/-- If `-log r / (2π) < Im τ` then `‖e(τ)‖ < r`. -/
lemma norm_e_lt_of_neg_log_div_lt_im {r : ℝ} (hr0 : 0 < r) {τ : ℂ}
    (hT : -Real.log r / (2 * Real.pi) < τ.im) : ‖e τ‖ < r := by
  rw [ellipticRhoLeading_norm_e, ← Real.exp_log hr0, Real.exp_lt_exp]
  have := (div_lt_iff₀ (by positivity)).mp hT
  linarith

/-- A geometric bound `‖f (k + 1)‖ ≤ B t tᵏ` with `t ≤ 1/2` gives `‖∑ f (k + 1)‖ ≤ 2 B t`. -/
lemma norm_tsum_succ_le_of_geometric {E : Type*} [SeminormedAddCommGroup E] {f : ℕ → E}
    {B t : ℝ} (hB : 0 ≤ B) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hfs : Summable fun k => ‖f k‖)
    (hfk : ∀ k, ‖f (k + 1)‖ ≤ B * t * t ^ k) : ‖∑' k, f (k + 1)‖ ≤ 2 * B * t := by
  have hs1 : Summable fun k => ‖f (k + 1)‖ := (summable_nat_add_iff 1).mpr hfs
  calc ‖∑' k, f (k + 1)‖ ≤ ∑' k, ‖f (k + 1)‖ := norm_tsum_le_tsum_norm hs1
    _ ≤ ∑' k, B * t * t ^ k :=
        hs1.tsum_le_tsum hfk ((summable_geometric_of_lt_one ht0 (by linarith)).mul_left _)
    _ = B * t * (1 - t)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 (by linarith)]
    _ ≤ B * t * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
    _ = 2 * B * t := by ring

/-- **Leading term of `ρ_{m,x}`.** For `m ≥ 2` and `α ∈ ℚ` there are `C, T > 0` with
`‖ρ_{m,x}(τ) - x⁻²‖ ≤ C ‖e(τ)‖` whenever `τ ∈ ℍ` and `Im τ ≥ T`. -/
theorem rho_leading {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ : ℂ, τ ∈ upperHalfPlaneSet → T ≤ τ.im →
      ‖rho m α τ - (e α ^ 2)⁻¹‖ ≤ C * ‖e τ‖ := by
  obtain ⟨C₀, δ, hC₀, hδ, hg0⟩ := exists_norm_gTail_sub_one_le hm (e α) 0
  obtain ⟨B, hB0, hB⟩ := exists_bound_norm_gTail hm (Q := 1 / 2) (B := 1) (by norm_num)
    (by norm_num) zero_le_one
  have hx : ‖e (α : ℂ)‖ = 1 := by
    simpa using rhoNormal_norm_e_ofReal (α : ℝ)
  set r : ℝ := min δ (1 / 2) with hr
  have hr0 : 0 < r := lt_min hδ (by norm_num)
  have hlog : Real.log r < 0 := Real.log_neg hr0 ((min_le_right _ _).trans_lt (by norm_num))
  refine ⟨C₀ + 2 * B + 1, -Real.log r / (2 * Real.pi) + 1, by positivity,
    add_pos (div_pos (by linarith) (by positivity)) one_pos, ?_⟩
  intro τ hτ hT
  set q := e τ with hq
  have hqr : ‖q‖ < r := norm_e_lt_of_neg_log_div_lt_im hr0 (by linarith)
  have hqδ : ‖q‖ < δ := hqr.trans_le (min_le_left _ _)
  have hqh : ‖q‖ ≤ 1 / 2 := hqr.le.trans (min_le_right _ _)
  set f : ℕ → ℂ := fun k => e α ^ (2 * (m + 1) * k) * q ^ ((m + 1) * k ^ 2) *
    gTail m (e α) k q with hf
  obtain ⟨M, hM, -, hMle⟩ := rhoNormal_exists_majorant hm α {τ} isCompact_singleton
    (Set.singleton_subset_iff.mpr hτ)
  have hfs : Summable fun k => ‖f k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hMle k τ rfl) hM
  have hf0 : f 0 = gTail m (e α) 0 q := by simp [hf]
  have hfk : ∀ k, ‖f (k + 1)‖ ≤ B * ‖q‖ * ‖q‖ ^ k := by
    intro k
    have hk : k + 1 ≤ (m + 1) * (k + 1) ^ 2 :=
      (Nat.le_self_pow two_ne_zero _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos m))
    simp only [hf, norm_mul, norm_pow, hx, one_pow, one_mul]
    calc ‖q‖ ^ ((m + 1) * (k + 1) ^ 2) * ‖gTail m (e α) (k + 1) q‖
        ≤ ‖q‖ ^ (k + 1) * B :=
          mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) (by linarith) hk)
            (hB _ _ hqh _ hx.le) (norm_nonneg _) (by positivity)
      _ = B * ‖q‖ * ‖q‖ ^ k := by ring
  have hrho : rho m α τ - (e α ^ 2)⁻¹ =
      (e α ^ 2)⁻¹ * ((gTail m (e α) 0 q - 1) + ∑' k, f (k + 1)) := by
    rw [rho, ← hq]
    change (e α ^ 2)⁻¹ * ∑' k, f k - _ = _
    rw [hfs.of_norm.tsum_eq_zero_add, hf0]
    ring
  rw [hrho, norm_mul, show ‖(e (α : ℂ) ^ 2)⁻¹‖ = 1 by simp [hx], one_mul]
  calc ‖gTail m (e α) 0 q - 1 + ∑' k, f (k + 1)‖
      ≤ ‖gTail m (e α) 0 q - 1‖ + ‖∑' k, f (k + 1)‖ := norm_add_le _ _
    _ ≤ C₀ * ‖q‖ + 2 * B * ‖q‖ := add_le_add (by simpa using hg0 q hqδ)
      (norm_tsum_succ_le_of_geometric hB0 (norm_nonneg q) hqh hfs hfk)
    _ ≤ (C₀ + 2 * B + 1) * ‖q‖ := by nlinarith [norm_nonneg q]

end HigherDyson3
