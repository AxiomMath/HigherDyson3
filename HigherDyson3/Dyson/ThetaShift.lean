/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.AnalyticSeries
public import HigherDyson3.Product.ProdOneAddBound

/-!
# The theta products and the shift identity

For `|q| < 1` let `Θ(x;q) = (xq, q/x; q)_∞`, `A_s(x;n) = (x q^{n+1+s}, q^{n+1}/x; q)_∞` for
`s, n ≥ 0`, and, for `𝐬 ∈ ℤ_{≥0}^m`,
`F_m^𝐬(x_1,…,x_m;q) = ∑_{n ≥ 0} q^{n² + |𝐬| n} ∏_{j=1}^m A_{s_j}(x_j;n)`. Then
`(∏_j Θ(x_j;q)) R_m(x_1,…,x_m;q) = F_m^𝟎(x_1,…,x_m;q)` and
`F_m^𝐬(…, q x_i, …) - F_m^𝐬(…, x_i, …) = (q^{s_i+1} x_i - x_i^{-1}) F_m^{𝐬+𝐞_i}` [AOS, Theorem 2.4].

The first identity is termwise: `Θ(x;q) = (xq, q/x; q)_n A_0(x;n)`. The second rests on
`A_s(qx;n) - A_s(x;n) = q^n (q^{s+1} x - x^{-1}) A_{s+1}(x;n)`, and the series `F_m^𝐬` converge
absolutely since `|A_s(x;n)| ≤ exp((|x| + |x|^{-1})/(1 - |q|))`.

## Main results

* `HigherDyson3.thetaProduct`, `HigherDyson3.thetaTail`, `HigherDyson3.thetaFamily`: `Θ`, `A_s`,
  `F_m^𝐬`.
* `HigherDyson3.prod_thetaProduct_mul_higherDysonSeries`: the theta-product identity.
* `HigherDyson3.thetaFamily_update_mul_sub`: the shift identity.
-/

public section

noncomputable section

open Finset

namespace HigherDyson3

/-- `Θ(x;q) = (xq;q)_∞ (q/x;q)_∞` [AOS, §2]. -/
def thetaProduct (x q : ℂ) : ℂ := qPochhammerInf (x * q) q * qPochhammerInf (q / x) q

/-- `A_s(x;n) = (x q^{n+1+s};q)_∞ (q^{n+1}/x;q)_∞` [AOS, §2]. -/
def thetaTail (s : ℕ) (x : ℂ) (n : ℕ) (q : ℂ) : ℂ :=
  qPochhammerInf (x * q ^ (n + 1 + s)) q * qPochhammerInf (q ^ (n + 1) / x) q

/-- `F_m^𝐬(x_1,…,x_m;q) = ∑_{n ≥ 0} q^{n² + |𝐬| n} ∏_{j=1}^m A_{s_j}(x_j;n)` for
`𝐬 ∈ ℤ_{≥0}^m`, `|𝐬| = s_1 + ⋯ + s_m` [AOS, §2]. -/
def thetaFamily (m : ℕ) (s : Fin m → ℕ) (x : Fin m → ℂ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2 + (∑ j, s j) * n) * ∏ j, thetaTail (s j) (x j) n q

/-- `Θ(x;q) = (xq;q)_n (q/x;q)_n A_0(x;n)` for `|q| < 1`. -/
theorem thetaProduct_eq_mul_thetaTail (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    thetaProduct x q =
      qPochhammer (x * q) q n * qPochhammer (q / x) q n * thetaTail 0 x n q := by
  rw [thetaProduct, thetaTail, ← qPochhammer_mul_qPochhammerInf (x * q) hq n,
    ← qPochhammer_mul_qPochhammerInf (q / x) hq n,
    show x * q * q ^ n = x * q ^ (n + 1 + 0) by ring, show q / x * q ^ n = q ^ (n + 1) / x by ring]
  ring

/-- **The theta-product identity** [AOS, Theorem 2.4]: for `|q| < 1` and `x_j` with
`x_j q^k ≠ 1` and `q^k / x_j ≠ 1` for all `k ≥ 1`,
`(∏_{j=1}^m Θ(x_j;q)) R_m(x_1,…,x_m;q) = F_m^𝟎(x_1,…,x_m;q)`. -/
theorem prod_thetaProduct_mul_higherDysonSeries (m : ℕ) (x : Fin m → ℂ) {q : ℂ} (hq : ‖q‖ < 1)
    (hx : ∀ j, ∀ k : ℕ, 1 ≤ k → x j * q ^ k ≠ 1 ∧ q ^ k / x j ≠ 1) :
    (∏ j, thetaProduct (x j) q) * higherDysonSeries m x q = thetaFamily m 0 x q := by
  rw [higherDysonSeries_def, thetaFamily, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hD : ∏ j, (qPochhammer (x j * q) q n * qPochhammer (q / x j) q n) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun j _ => mul_ne_zero ?_ ?_
    · exact qPochhammer_ne_zero fun l _ => by
        rw [mul_assoc, ← pow_succ']; exact (hx j (l + 1) (by omega)).1
    · exact qPochhammer_ne_zero fun l _ => by
        rw [div_mul_eq_mul_div, ← pow_succ']; exact (hx j (l + 1) (by omega)).2
  have hT : ∏ j, thetaProduct (x j) q = (∏ j, (qPochhammer (x j * q) q n *
      qPochhammer (q / x j) q n)) * ∏ j, thetaTail 0 (x j) n q := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun j _ => thetaProduct_eq_mul_thetaTail _ hq n
  rw [hT]
  simp only [Pi.zero_apply, sum_const_zero, zero_mul, add_zero]
  rw [mul_comm _ (q ^ (n ^ 2) / _), div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc,
    mul_div_left_comm, div_self hD, mul_one]

/-- `|(c;q)_∞| ≤ exp(|c|/(1 - |q|))` for `|q| < 1`. -/
theorem norm_qPochhammerInf_le (c : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    ‖qPochhammerInf c q‖ ≤ Real.exp (‖c‖ / (1 - ‖q‖)) := by
  have hg := summable_geometric_of_lt_one (norm_nonneg q) hq
  have ha : Summable fun l : ℕ => ‖-(c * q ^ l)‖ := by
    simpa [norm_mul, norm_pow] using hg.mul_left ‖c‖
  have h := norm_tprod_one_add_sub_one_le ha
  have hsum : ∑' l : ℕ, ‖-(c * q ^ l)‖ = ‖c‖ / (1 - ‖q‖) := by
    simp only [norm_neg, norm_mul, norm_pow]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg q) hq, div_eq_mul_inv]
  rw [hsum] at h
  rw [qPochhammerInf_def]
  have h1 : ‖∏' l : ℕ, (1 - c * q ^ l)‖ ≤ ‖(1 : ℂ)‖ + ‖∏' l : ℕ, (1 - c * q ^ l) - 1‖ :=
    norm_le_insert' _ _
  simp only [sub_eq_add_neg] at h h1 ⊢
  simp only [norm_one] at h1
  linarith

/-- `|A_s(x;n)| ≤ exp(|x|/(1 - |q|)) exp(|x|^{-1}/(1 - |q|))` for `|q| < 1`. -/
theorem norm_thetaTail_le (s : ℕ) (x : ℂ) (n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    ‖thetaTail s x n q‖ ≤ Real.exp (‖x‖ / (1 - ‖q‖)) * Real.exp (‖x‖⁻¹ / (1 - ‖q‖)) := by
  have h1q : 0 < 1 - ‖q‖ := by linarith
  have hpow : ∀ k : ℕ, ‖q‖ ^ k ≤ 1 := fun k => pow_le_one₀ (norm_nonneg _) hq.le
  rw [thetaTail, norm_mul]
  refine mul_le_mul ((norm_qPochhammerInf_le _ hq).trans ?_)
    ((norm_qPochhammerInf_le _ hq).trans ?_) (norm_nonneg _) (Real.exp_pos _).le
  · refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ h1q.le)
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _) (hpow _)
  · refine Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ?_ h1q.le)
    rw [norm_div, norm_pow, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (hpow _)

/-- The series `F_m^𝐬(x_1,…,x_m;q)` converges for `|q| < 1`. -/
theorem summable_thetaFamily (m : ℕ) (s : Fin m → ℕ) (x : Fin m → ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => q ^ (n ^ 2 + (∑ j, s j) * n) * ∏ j, thetaTail (s j) (x j) n q := by
  set K : ℝ := ∏ j, (Real.exp (‖x j‖ / (1 - ‖q‖)) * Real.exp (‖x j‖⁻¹ / (1 - ‖q‖)))
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left K) fun n => ?_
  rw [norm_mul, norm_prod, norm_pow, mul_comm K]
  refine mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hq.le
    ((Nat.le_self_pow (by norm_num) n).trans (Nat.le_add_right _ _)))
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => norm_thetaTail_le _ _ _ hq)
    (prod_nonneg fun _ _ => norm_nonneg _) (by positivity)

/-- `A_s(qx;n) - A_s(x;n) = q^n (q^{s+1} x - x^{-1}) A_{s+1}(x;n)` for `0 < |q| < 1`, `x ≠ 0`. -/
theorem thetaTail_mul_sub (s : ℕ) {x : ℂ} (hx : x ≠ 0) (n : ℕ) {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) :
    thetaTail s (q * x) n q - thetaTail s x n q =
      q ^ n * (q ^ (s + 1) * x - x⁻¹) * thetaTail (s + 1) x n q := by
  rw [thetaTail, thetaTail, thetaTail,
    show q * x * q ^ (n + 1 + s) = x * q ^ (n + 1 + (s + 1)) by ring,
    show q ^ (n + 1) / (q * x) = q ^ n / x by field_simp; ring,
    qPochhammerInf_eq_one_sub_mul (q ^ n / x) hq,
    qPochhammerInf_eq_one_sub_mul (x * q ^ (n + 1 + s)) hq,
    show q ^ n / x * q = q ^ (n + 1) / x by ring,
    show x * q ^ (n + 1 + s) * q = x * q ^ (n + 1 + (s + 1)) by ring]
  field_simp
  ring

/-- **The shift identity** [AOS, Theorem 2.4]: for `0 < |q| < 1`, `1 ≤ i ≤ m`, `x_i ≠ 0` and
`𝐬 ∈ ℤ_{≥0}^m`, `F_m^𝐬(x_1,…,q x_i,…,x_m;q) - F_m^𝐬(x_1,…,x_i,…,x_m;q)
= (q^{s_i+1} x_i - x_i^{-1}) F_m^{𝐬+𝐞_i}(x_1,…,x_m;q)`. -/
theorem thetaFamily_update_mul_sub (m : ℕ) (s : Fin m → ℕ) (x : Fin m → ℂ) (i : Fin m)
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hxi : x i ≠ 0) :
    thetaFamily m s (Function.update x i (q * x i)) q - thetaFamily m s x q =
      (q ^ (s i + 1) * x i - (x i)⁻¹) * thetaFamily m (s + Pi.single i 1) x q := by
  rw [thetaFamily, thetaFamily, thetaFamily,
    ← (summable_thetaFamily m s _ hq).tsum_sub (summable_thetaFamily m s x hq), ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  set R := ∏ j ∈ univ.erase i, thetaTail (s j) (x j) n q
  have e1 : ∏ j, thetaTail (s j) (Function.update x i (q * x i) j) n q =
      thetaTail (s i) (q * x i) n q * R := by
    rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have e2 : ∏ j, thetaTail (s j) (x j) n q = thetaTail (s i) (x i) n q * R :=
    (mul_prod_erase univ _ (mem_univ i)).symm
  have e3 : ∏ j, thetaTail ((s + Pi.single i 1 : Fin m → ℕ) j) (x j) n q =
      thetaTail (s i + 1) (x i) n q * R := by
    rw [← mul_prod_erase univ _ (mem_univ i)]
    simp only [Pi.add_apply, Pi.single_eq_same]
    congr 1
    exact prod_congr rfl fun j hj => by rw [Pi.single_eq_of_ne (ne_of_mem_erase hj), add_zero]
  have e4 : ∑ j, (s + Pi.single i 1 : Fin m → ℕ) j = ∑ j, s j + 1 := by
    simp [sum_add_distrib]
  rw [e1, e2, e3, e4, ← mul_sub, ← sub_mul, thetaTail_mul_sub (s i) hxi n hq0 hq]
  ring

end HigherDyson3
