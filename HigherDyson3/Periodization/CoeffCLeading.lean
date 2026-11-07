/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCNormal
public import HigherDyson3.Product.GLeading

/-!
# Leading term of the theta coefficients `C_{m,ℓ,x}`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ`, `0 ≤ ℓ < 2m` and `q = e(τ)`. As `Im τ → ∞`,
`C_{m,ℓ,x}(τ) = x^{ℓ-2} q^{ℓ+1} + O(|q|^{ℓ+3})`.

The series defining `C_{m,ℓ,x}` converges absolutely, its `k = 0` summand vanishes and its
`k = 1` summand is `g_{1,x}(q) q^{ℓ+1}`. Since `g_{1,x}(q) = 1 + O(|q|²)`, the `k = 1` summand
contributes `x^{ℓ-2} q^{ℓ+1} + O(|q|^{ℓ+3})`. For `k ≥ 2` and `1 ≤ s ≤ k` the exponent
`(m+1)k² - ms² + ℓs` is at least `k² + ℓ ≥ ℓ + 3 + (k - 2)`, and the tails `g_{k,x}(q)` are
bounded uniformly for `|q| ≤ 1/2`; so for `|q| ≤ 1/2` the `k`-th summand is at most
`B k 2^{-(k-2)} |q|^{ℓ+3}`, which is summable in `k`.

## Main results

* `HigherDyson3.exists_norm_coeffC_sub_le`: the estimate
  `|C_{m,ℓ,x}(τ) - x^{ℓ-2} q^{ℓ+1}| ≤ C |q|^{ℓ+3}` for `Im τ ≥ T`.

## References

* [AOS] Alfes, Ono, Swaminathan, *Beyond mock modularity: elliptic corrections for higher
  Dyson ranks*.
-/

public section

open Finset

namespace HigherDyson3

/-- `|e(τ)| = exp(-2π Im τ)`. -/
lemma coeffCLeading_norm_e (τ : ℂ) : ‖e τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  unfold e
  rw [Complex.norm_exp]
  congr 1
  simp

/-- For `ε > 0` there is `T > 0` with `|e(τ)| < ε` whenever `Im τ ≥ T`. -/
lemma coeffCLeading_exists_im_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ τ : ℂ, T ≤ τ.im → ‖e τ‖ < ε := by
  refine ⟨|Real.log ε| / (2 * Real.pi) + 1, by positivity, fun τ hτ => ?_⟩
  rw [coeffCLeading_norm_e, ← Real.exp_log hε, Real.exp_lt_exp]
  have h1 : |Real.log ε| + 2 * Real.pi ≤ 2 * Real.pi * τ.im := by
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    rwa [mul_add, mul_div_cancel₀ _ (by positivity), mul_one] at this
  linarith [neg_abs_le (Real.log ε), Real.pi_pos]

/-- For `1 ≤ s ≤ k + 2`, the exponent `(m+1)(k+2)² - ms² + ℓs` is at least `ℓ + 3 + k`. -/
lemma coeffCLeading_exponent_ge {m ℓ k s : ℕ} (hs1 : 1 ≤ s) (hsk : s ≤ k + 2) :
    ((ℓ + 3 + k : ℕ) : ℤ) ≤
      ((m : ℤ) + 1) * ((k + 2 : ℕ) : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s := by
  have hsk' : (s : ℤ) ≤ ((k + 2 : ℕ) : ℤ) := by exact_mod_cast hsk
  have hs1' : (1 : ℤ) ≤ s := by exact_mod_cast hs1
  have h1 : (s : ℤ) ^ 2 ≤ ((k + 2 : ℕ) : ℤ) ^ 2 := by nlinarith
  have h3 : (0 : ℤ) ≤ (m : ℤ) * (((k + 2 : ℕ) : ℤ) ^ 2 - (s : ℤ) ^ 2) :=
    mul_nonneg (by positivity) (by linarith)
  have h4 : (ℓ : ℤ) ≤ (ℓ : ℤ) * s := by nlinarith
  push_cast at h1 h3 ⊢
  nlinarith

/-- `∑ₖ (k + 2) 2^{-k}` converges. -/
lemma summable_natCast_add_two_mul_half_pow :
    Summable fun k : ℕ => ((k : ℝ) + 2) * (1 / 2) ^ k := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg (by norm_num)]
    norm_num
  refine ((summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    ((summable_geometric_of_norm_lt_one hr).mul_left 2)).congr fun k => ?_
  simp only [pow_one]
  ring

/-- For `|x| = 1` and `|q| ≤ 1/2`, the inner sum of the `(k+2)`-th summand of `C_{m,ℓ,x}` is
at most `(k + 2) 2^{-k} |q|^{ℓ+3}`. -/
lemma coeffCLeading_norm_sum_le {m ℓ k : ℕ} {x q : ℂ} (hx : ‖x‖ = 1) (hq2 : ‖q‖ ≤ 1 / 2) :
    ‖∑ s ∈ Icc 1 (k + 2), x ^ (2 * ((m : ℤ) + 1) * (((k + 2 : ℕ) : ℤ) - s)) *
      q ^ (((m : ℤ) + 1) * ((k + 2 : ℕ) : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)‖ ≤
      ((k : ℝ) + 2) * (1 / 2) ^ k * ‖q‖ ^ (ℓ + 3) := by
  calc _ ≤ ∑ s ∈ Icc 1 (k + 2), ‖x ^ (2 * ((m : ℤ) + 1) * (((k + 2 : ℕ) : ℤ) - s)) *
        q ^ (((m : ℤ) + 1) * ((k + 2 : ℕ) : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _s ∈ Icc 1 (k + 2), (1 / 2 : ℝ) ^ k * ‖q‖ ^ (ℓ + 3) := by
        refine sum_le_sum fun s hs => ?_
        obtain ⟨hs1, hsk⟩ := mem_Icc.mp hs
        rw [norm_mul, norm_zpow, norm_zpow, hx, one_zpow, one_mul]
        set N : ℤ := ((m : ℤ) + 1) * ((k + 2 : ℕ) : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s
        have hN : ((ℓ + 3 + k : ℕ) : ℤ) ≤ N := coeffCLeading_exponent_ge hs1 hsk
        rw [(Int.toNat_of_nonneg (by omega) : ((N.toNat : ℕ) : ℤ) = N).symm, zpow_natCast]
        calc ‖q‖ ^ N.toNat ≤ ‖q‖ ^ (ℓ + 3 + k) :=
              pow_le_pow_of_le_one (norm_nonneg _) (hq2.trans (by norm_num)) (by omega)
          _ = ‖q‖ ^ k * ‖q‖ ^ (ℓ + 3) := by rw [pow_add, mul_comm]
          _ ≤ (1 / 2 : ℝ) ^ k * ‖q‖ ^ (ℓ + 3) := by gcongr
    _ = ((k : ℝ) + 2) * (1 / 2) ^ k * ‖q‖ ^ (ℓ + 3) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring

/-- If `|a| ≤ C |q|²` then `|a q^{ℓ+1}| ≤ C |q|^{ℓ+3}`. -/
lemma coeffCLeading_norm_mul_pow_le {a q : ℂ} {C : ℝ} {ℓ : ℕ} (h : ‖a‖ ≤ C * ‖q‖ ^ (1 + 1)) :
    ‖a * q ^ (ℓ + 1)‖ ≤ C * ‖q‖ ^ (ℓ + 3) := by
  rw [norm_mul, norm_pow]
  calc ‖a‖ * ‖q‖ ^ (ℓ + 1) ≤ C * ‖q‖ ^ (1 + 1) * ‖q‖ ^ (ℓ + 1) := by gcongr
    _ = C * ‖q‖ ^ (ℓ + 3) := by rw [mul_assoc, ← pow_add]; ring_nf

/-- **Leading term of `C_{m,ℓ,x}`.** For `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1` and
`0 ≤ ℓ < 2m` there are `C, T > 0` with
`|C_{m,ℓ,x}(τ) - x^{ℓ-2} q^{ℓ+1}| ≤ C |q|^{ℓ+3}` for all `τ ∈ ℍ` with `Im τ ≥ T`, where
`x = e(α)` and `q = e(τ)`. -/
theorem exists_norm_coeffC_sub_le {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖coeffC m ℓ α τ - e α ^ ((ℓ : ℤ) - 2) * e τ ^ (ℓ + 1)‖ ≤ C * ‖e τ‖ ^ (ℓ + 3) := by
  set x : ℂ := e α with hxdef
  have hx : ‖x‖ = 1 := by exact_mod_cast coeffCNormal_norm_e_ofReal α
  obtain ⟨C₁, δ, hC₁, hδ, hg1⟩ := exists_norm_gTail_sub_one_le hm x 1
  obtain ⟨B, hB0, hB⟩ :=
    exists_bound_norm_gTail hm (Q := 1 / 2) (by norm_num) (by norm_num) zero_le_one
  set M : ℝ := ∑' k : ℕ, ((k : ℝ) + 2) * (1 / 2) ^ k with hMdef
  have hM0 : 0 ≤ M := tsum_nonneg fun k => by positivity
  obtain ⟨T, hT0, hT⟩ := coeffCLeading_exists_im_ge (lt_min hδ (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨C₁ + B * M + 1, T, by positivity, hT0, fun τ hτH hτT => ?_⟩
  set q : ℂ := e τ with hqdef
  have hqδ : ‖q‖ < δ := (hT τ hτT).trans_le (min_le_left _ _)
  have hq2 : ‖q‖ ≤ 1 / 2 := ((hT τ hτT).trans_le (min_le_right _ _)).le
  set f : ℕ → ℂ := fun k => gTail m x k q *
    ∑ s ∈ Icc 1 k, x ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
      q ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s) with hfdef
  have hfs : Summable f := by
    obtain ⟨u, hu, -, hle⟩ := coeffCNormal_exists hm hα0 hα1 hℓ {τ} isCompact_singleton
      (Set.singleton_subset_iff.mpr hτH)
    exact Summable.of_norm_bounded hu fun k => hle k τ rfl
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hf1 : f 1 = gTail m x 1 q * q ^ (ℓ + 1) := by
    simp only [hfdef, Icc_self, sum_singleton, Nat.cast_one, sub_self, mul_zero, zpow_zero,
      one_mul]
    congr 1
    rw [← zpow_natCast]
    congr 1
    push_cast
    ring
  have htail : ‖∑' k, f (k + 2)‖ ≤ B * M * ‖q‖ ^ (ℓ + 3) := by
    refine tsum_of_norm_bounded
      ((summable_natCast_add_two_mul_half_pow.hasSum.mul_left B).mul_right _) fun k => ?_
    simp only [hfdef]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hB _ _ hq2 _ hx.le) (coeffCLeading_norm_sum_le hx hq2) (norm_nonneg _) hB0
  have hsplit : coeffC m ℓ α τ - x ^ ((ℓ : ℤ) - 2) * q ^ (ℓ + 1) =
      x ^ ((ℓ : ℤ) - 2) * ((gTail m x 1 q - 1) * q ^ (ℓ + 1) + ∑' k, f (k + 2)) := by
    have h := (hfs.sum_add_tsum_nat_add 2).symm
    rw [sum_range_succ, sum_range_one, hf0, hf1, zero_add] at h
    simp only [coeffC]
    rw [← hxdef, ← hqdef]
    change x ^ ((ℓ : ℤ) - 2) * ∑' k, f k - _ = _
    rw [h]
    ring
  rw [hsplit, norm_mul, norm_zpow, hx, one_zpow, one_mul]
  calc _ ≤ ‖(gTail m x 1 q - 1) * q ^ (ℓ + 1)‖ + ‖∑' k, f (k + 2)‖ := norm_add_le _ _
    _ ≤ C₁ * ‖q‖ ^ (ℓ + 3) + B * M * ‖q‖ ^ (ℓ + 3) :=
      add_le_add (coeffCLeading_norm_mul_pow_le (hg1 q hqδ)) htail
    _ ≤ (C₁ + B * M + 1) * ‖q‖ ^ (ℓ + 3) := by
      nlinarith [pow_nonneg (norm_nonneg q) (ℓ + 3)]

end HigherDyson3

end
