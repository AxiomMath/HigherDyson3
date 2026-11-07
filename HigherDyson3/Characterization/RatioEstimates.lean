/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.HRatio

/-!
# The bound `B'_{1/2} < 3` for the ratios `h_i(c)`

For `|c| = 1` and `|q| ≤ Q < 1`, the ratios `h_i(c) = (cq;q)_i / (c^d q^d; q^d)_i` of
[AOS, (7.2)] satisfy `|h_i(c)| ≤ ∏_{l=1}^{i} (1 + Q^l) / (1 - Q^{dl})`, since
`|1 - c q^l| ≤ 1 + |q|^l` and `|1 - c^d q^{dl}| ≥ 1 - |q|^{dl}` [AOS, (7.3)]. At `Q = 1/2`, with
`d ≥ 5`, the product is at most `exp(1 + 2/31) < 3` [AOS, proof of Lemma 7.5]. We also record
the Gaussian hypothesis of [AOS, Lemma 7.4] for the Lambert coefficients `b_i(c)`.

## Main results

* `HigherDyson3.norm_hRatio_le_prod`: the product bound.
* `HigherDyson3.norm_hRatio_le_three`: the bound `3` for `|q| ≤ 1/2`, `m ≥ 2`.
* `HigherDyson3.exists_gaussian_bound_lambertCoeff`: `|b_i(c)| ≤ B'_Q |q|^{i²}`.
-/

public section

noncomputable section

open Complex Finset

namespace HigherDyson3

/-- `|(cq;q)_i| ≤ ∏_{l<i} (1 + Q^{l+1})` for `|c| = 1`, `|q| ≤ Q`. -/
lemma norm_qPochhammer_mul_le {c q : ℂ} (hc : ‖c‖ = 1) {Q : ℝ} (hq : ‖q‖ ≤ Q) (i : ℕ) :
    ‖qPochhammer (c * q) q i‖ ≤ ∏ l ∈ range i, (1 + Q ^ (l + 1)) := by
  unfold qPochhammer
  rw [norm_prod]
  refine prod_le_prod₀ (fun _ _ => norm_nonneg _) fun l _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul, norm_mul, norm_pow, hc, one_mul, ← pow_succ']
  gcongr

/-- `|(c^d q^d; q^d)_i| ≥ ∏_{l<i} (1 - Q^{d(l+1)})` for `|c| = 1`, `|q| ≤ Q < 1`. -/
lemma prod_le_norm_qPochhammer_pow {c q : ℂ} (hc : ‖c‖ = 1) {Q : ℝ} (hq : ‖q‖ ≤ Q)
    (hQ1 : Q < 1) (d i : ℕ) :
    ∏ l ∈ range i, (1 - Q ^ (d * (l + 1))) ≤ ‖qPochhammer (c ^ d * q ^ d) (q ^ d) i‖ := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hq
  unfold qPochhammer
  rw [norm_prod]
  refine prod_le_prod₀ (fun l _ => sub_nonneg.mpr (pow_le_one₀ hQ0 hQ1.le)) fun l _ => ?_
  have h := norm_sub_norm_le (1 : ℂ) (c ^ d * q ^ d * (q ^ d) ^ l)
  simp only [norm_mul, norm_pow, norm_one, hc, one_pow, one_mul] at h
  rw [← pow_mul, ← pow_add] at h
  have : ‖q‖ ^ (d + d * l) ≤ Q ^ (d * (l + 1)) := by
    rw [show d + d * l = d * (l + 1) by ring]
    exact pow_le_pow_left₀ (norm_nonneg _) hq _
  linarith

/-- **The product bound** [AOS, (7.3)]: for `|c| = 1` and `|q| ≤ Q < 1`,
`|h_i(c)| ≤ ∏_{l=1}^{i} (1 + Q^l) / (1 - Q^{dl})`. -/
theorem norm_hRatio_le_prod (m : ℕ) {c q : ℂ} (hc : ‖c‖ = 1) {Q : ℝ} (hq : ‖q‖ ≤ Q)
    (hQ1 : Q < 1) (i : ℕ) :
    ‖hRatio m c q i‖ ≤ ∏ l ∈ range i, (1 + Q ^ (l + 1)) / (1 - Q ^ ((2 * m + 1) * (l + 1))) := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hq
  have hpos : 0 < ∏ l ∈ range i, (1 - Q ^ ((2 * m + 1) * (l + 1))) :=
    prod_pos fun l _ => sub_pos.mpr (pow_lt_one₀ hQ0 hQ1 (by positivity))
  unfold hRatio
  rw [norm_div, prod_div_distrib]
  exact div_le_div₀ (prod_nonneg fun l _ => by positivity) (norm_qPochhammer_mul_le hc hq i)
    hpos (prod_le_norm_qPochhammer_pow hc hq hQ1 _ i)

/-- `∑_{l<i} Q^{l+1} ≤ Q/(1-Q)` for `0 ≤ Q < 1`. -/
lemma sum_pow_succ_le {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (i : ℕ) :
    ∑ l ∈ range i, Q ^ (l + 1) ≤ Q / (1 - Q) := by
  have hs : Summable fun l : ℕ => Q ^ (l + 1) := by
    simpa [pow_succ'] using (summable_geometric_of_lt_one hQ0 hQ1).mul_left Q
  refine (hs.sum_le_tsum _ fun l _ => by positivity).trans_eq ?_
  simp_rw [pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_lt_one hQ0 hQ1, div_eq_mul_inv]

/-- **The bound at `Q = 1/2`** [AOS, proof of Lemma 7.5]: for `m ≥ 2`, `|c| = 1` and
`|q| ≤ 1/2`, `|h_i(c)| ≤ B'_{1/2} ≤ exp(1 + 2/31) < 3`. -/
theorem norm_hRatio_le_three {m : ℕ} (hm : 2 ≤ m) {c q : ℂ} (hc : ‖c‖ = 1)
    (hq : ‖q‖ ≤ 1 / 2) (i : ℕ) : ‖hRatio m c q i‖ ≤ 3 := by
  refine (norm_hRatio_le_prod m hc hq (by norm_num) i).trans ?_
  have hfac : ∀ l ∈ range i, (1 + (1 / 2 : ℝ) ^ (l + 1)) /
      (1 - (1 / 2 : ℝ) ^ ((2 * m + 1) * (l + 1))) ≤
        Real.exp ((1 / 2 : ℝ) ^ (l + 1) + 2 * (1 / 32 : ℝ) ^ (l + 1)) := by
    intro l _
    set t : ℝ := (1 / 2) ^ (l + 1)
    set s : ℝ := (1 / 2) ^ ((2 * m + 1) * (l + 1))
    have ht0 : 0 ≤ t := by positivity
    have hs0 : 0 ≤ s := by positivity
    have hs32 : s ≤ (1 / 32) ^ (l + 1) := by
      rw [show (1 / 32 : ℝ) = (1 / 2) ^ 5 by norm_num, ← pow_mul]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)
    have hs1 : (1 / 32 : ℝ) ^ (l + 1) ≤ 1 / 32 := pow_le_of_le_one (by norm_num) (by norm_num)
      (by omega)
    have h1s : 0 < 1 - s := by linarith
    calc (1 + t) / (1 - s) ≤ (1 + t) * (1 + 2 * s) := by
          rw [div_le_iff₀ h1s]
          have key : (1 + t) * (1 + 2 * s) * (1 - s) = (1 + t) + (1 + t) * s * (1 - 2 * s) := by
            ring
          have : 0 ≤ (1 + t) * s * (1 - 2 * s) :=
            mul_nonneg (mul_nonneg (by linarith) hs0) (by linarith)
          linarith
      _ ≤ Real.exp t * Real.exp (2 * (1 / 32 : ℝ) ^ (l + 1)) := by
          gcongr
          · linarith [Real.add_one_le_exp t]
          · linarith [Real.add_one_le_exp (2 * (1 / 32 : ℝ) ^ (l + 1))]
      _ = Real.exp (t + 2 * (1 / 32 : ℝ) ^ (l + 1)) := (Real.exp_add _ _).symm
  refine (prod_le_prod₀ (fun l _ => div_nonneg (by positivity)
    (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)))) hfac).trans ?_
  rw [← Real.exp_sum, sum_add_distrib, ← mul_sum]
  have h1 := sum_pow_succ_le (Q := 1 / 2) (by norm_num) (by norm_num) i
  have h2 := sum_pow_succ_le (Q := 1 / 32) (by norm_num) (by norm_num) i
  have he : Real.exp (2 / 31) < 31 / 29 := by
    have h := Real.exp_bound_div_one_sub_of_interval' (x := 2 / 31) (by norm_num) (by norm_num)
    rwa [show (1 : ℝ) / (1 - 2 / 31) = 31 / 29 by norm_num] at h
  calc Real.exp (∑ l ∈ range i, (1 / 2 : ℝ) ^ (l + 1) +
        2 * ∑ l ∈ range i, (1 / 32 : ℝ) ^ (l + 1))
      ≤ Real.exp (1 + 2 / 31) := by
        rw [Real.exp_le_exp]
        norm_num at h1 h2 ⊢
        linarith
    _ = Real.exp 1 * Real.exp (2 / 31) := Real.exp_add _ _
    _ ≤ 2.7182818286 * (31 / 29) :=
        mul_le_mul Real.exp_one_lt_d9.le he.le (Real.exp_pos _).le (by norm_num)
    _ ≤ 3 := by norm_num

/-- The Gaussian hypothesis of [AOS, Lemma 7.4] for the Lambert coefficients. -/
theorem exists_gaussian_bound_lambertCoeff (m : ℕ) {x c : ℂ} (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) :
    ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q →
      ‖lambertCoeff m x c i q‖ ≤ B * ‖q‖ ^ (i ^ 2) :=
  fun _ hQ0 hQ1 => ⟨_, fun i _ hq => norm_lambertCoeff_le hQ0.le hQ1 hx hc hq i⟩

end HigherDyson3
