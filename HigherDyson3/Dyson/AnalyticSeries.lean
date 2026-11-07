/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.QPochhammer
public import HigherDyson3.Dyson.RootOfUnityCollapse
public import HigherDyson3.Product.GMultipliable

/-!
# The higher Dyson series as complex functions

The multivariable series `R_m(x_1,…,x_m;q) = ∑_{n ≥ 0} q^{n²} / ∏_{j=1}^m (x_j q, q/x_j; q)_n` and
its specialization `R_m(z;q) = R_m(z, z², …, z^m; q)` [AOS, (1.1), §2], as complex numbers.
At a primitive `d`-th root of unity, `d = 2m + 1`,
`R_m(ζ_d;q) = ∑_{n ≥ 0} q^{n²} (q;q)_n/(q^d;q^d)_n` [AOS, §1, §2]; and for `m ≥ 2` the value
`X_0^{(m)}(1;q)` of the deformation is `(q^d;q^d)_∞/(q;q)_∞ · R_m(ζ_d;q)` [AOS, (1.3)], where
`G_d(y;q) = ∏_{r ≥ 1} P_d(y q^r)` is the quotient `(y^d q^d;q^d)_∞/(yq;q)_∞` of [AOS, (1.2)].

## Main results

* `HigherDyson3.higherDysonSeries`, `HigherDyson3.higherDysonSeriesZ`: `R_m(x_1,…,x_m;q)`,
  `R_m(z;q)`.
* `HigherDyson3.prod_one_sub_primitive_mul`: `∏_{j=1}^m (1 - ζ^j y)(1 - ζ^{-j} y)
  = ∏_{r=1}^{d-1} (1 - ζ^r y) = (1 - y^d)/(1 - y)`.
* `HigherDyson3.higherDysonSeriesZ_primitive`: the collapse at a primitive root of unity.
* `HigherDyson3.GProduct_eq_div`: `G_d(y;q) = (y^d q^d;q^d)_∞/(yq;q)_∞`.
* `HigherDyson3.XSeries_one_zero_eq`: `X_0^{(m)}(1;q) = (q^d;q^d)_∞/(q;q)_∞ · R_m(ζ_d;q)`.
-/

public section

noncomputable section

open Finset

namespace HigherDyson3

/-- The multivariable higher Dyson series
`R_m(x_1,…,x_m;q) = ∑_{n ≥ 0} q^{n²} / ∏_{j=1}^m (x_j q;q)_n (q/x_j;q)_n` [AOS, §2]
(Mathlib's unconditional sum; the variable `x (j : Fin m)` is the paper's `x_{j+1}`). -/
def higherDysonSeries (m : ℕ) (x : Fin m → ℂ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, q ^ (n ^ 2) / ∏ j, (qPochhammer (x j * q) q n * qPochhammer (q / x j) q n)

/-- The higher Dyson series `R_m(z;q) = R_m(z, z², …, z^m; q)
= ∑_{n ≥ 0} q^{n²} / ∏_{j=1}^m (z^j q, z^{-j} q; q)_n` [AOS, (1.1)]. -/
def higherDysonSeriesZ (m : ℕ) (z q : ℂ) : ℂ :=
  higherDysonSeries m (fun j => z ^ ((j : ℕ) + 1)) q

theorem higherDysonSeries_def (m : ℕ) (x : Fin m → ℂ) (q : ℂ) :
    higherDysonSeries m x q =
      ∑' n : ℕ, q ^ (n ^ 2) / ∏ j, (qPochhammer (x j * q) q n * qPochhammer (q / x j) q n) :=
  (rfl)

theorem higherDysonSeriesZ_def (m : ℕ) (z q : ℂ) :
    higherDysonSeriesZ m z q = higherDysonSeries m (fun j => z ^ ((j : ℕ) + 1)) q :=
  (rfl)

/-- The factorization behind the collapse [AOS, §2]: for a primitive `d`-th root of unity `ζ`,
`d = 2m + 1`, and `y ≠ 1`,
`∏_{j=1}^m (1 - ζ^j y)(1 - ζ^{-j} y) = ∏_{r=1}^{d-1} (1 - ζ^r y) = (1 - y^d)/(1 - y)`; at
`y = q^k`, `k ≥ 1`, `|q| < 1`, this is the identity of [AOS, §2]. -/
theorem prod_one_sub_primitive_mul (m : ℕ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m + 1)) {y : ℂ}
    (hy : y ≠ 1) :
    ∏ j ∈ Icc 1 m, ((1 - ζ ^ j * y) * (1 - ζ⁻¹ ^ j * y)) =
        ∏ r ∈ Icc 1 (2 * m), (1 - ζ ^ r * y) ∧
      ∏ r ∈ Icc 1 (2 * m), (1 - ζ ^ r * y) = (1 - y ^ (2 * m + 1)) / (1 - y) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.mpr hy.symm
  have hR : ∏ k ∈ range (2 * m + 1), (1 - ζ ^ k * y) =
      (1 - y) * ∏ r ∈ Icc 1 (2 * m), (1 - ζ ^ r * y) := by
    rw [range_eq_Ico, prod_eq_prod_Ico_succ_bot (by omega), pow_zero, one_mul,
      ← Ico_add_one_right_eq_Icc]
  have h1 := prod_range_one_sub_pow_mul (RingHom.id ℂ) m hζ y
  have h2 := one_sub_mul_prod_one_sub_zpow (RingHom.id ℂ) m (Units.mk0 ζ hζ0) hζ y
  simp only [RingHom.id_apply, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, Units.val_mk0] at h1 h2
  rw [hR] at h1
  refine ⟨mul_left_cancel₀ hy1 ?_, eq_div_of_mul_eq hy1 ?_⟩
  · rw [h1, ← h2]
    simp only [inv_pow]
  · rw [mul_comm, h1]

/-- At a primitive `(2m+1)`-th root of unity,
`∏_{j=1}^m (ζ^j q;q)_n (q/ζ^j;q)_n · (q;q)_n = (q^d;q^d)_n`. -/
theorem prod_qPochhammer_primitive_mul (m n : ℕ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m + 1))
    (q : ℂ) :
    (∏ j : Fin m, (qPochhammer (ζ ^ ((j : ℕ) + 1) * q) q n *
      qPochhammer (q / ζ ^ ((j : ℕ) + 1)) q n)) * qPochhammer q q n =
      qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) n := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  set u : ℂˣ := Units.mk0 ζ hζ0
  have hu : (u : ℂ) = ζ := rfl
  have hreindex : ∀ g : ℕ → ℂ, ∏ j : Fin m, g ((j : ℕ) + 1) = ∏ j ∈ Icc 1 m, g j := by
    intro g
    rw [Fin.prod_univ_eq_prod_range (fun j => g (j + 1)), range_eq_Ico, prod_Ico_add']
    rfl
  simp only [qPochhammer, ← prod_mul_distrib]
  rw [hreindex (fun j => ∏ l ∈ range n,
    ((1 - ζ ^ j * q * q ^ l) * (1 - q / ζ ^ j * q ^ l))), prod_comm, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  have h := one_sub_mul_prod_one_sub_zpow (RingHom.id ℂ) m u (by rwa [hu]) (q ^ (l + 1))
  simp only [RingHom.id_apply, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, hu] at h
  rw [show (q ^ (2 * m + 1)) * (q ^ (2 * m + 1)) ^ l = (q ^ (l + 1)) ^ (2 * m + 1) by ring, ← h,
    mul_comm]
  congr 1
  · ring
  · refine prod_congr rfl fun j _ => ?_
    rw [div_eq_inv_mul]
    ring

/-- **The collapse at a primitive root of unity** [AOS, §1, §2]: for `d = 2m + 1`, a primitive
`d`-th root of unity `ζ` and `|q| < 1`, `R_m(ζ;q) = ∑_{n ≥ 0} q^{n²} (q;q)_n / (q^d;q^d)_n`. -/
theorem higherDysonSeriesZ_primitive (m : ℕ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m + 1))
    {q : ℂ} (hq : ‖q‖ < 1) :
    higherDysonSeriesZ m ζ q = ∑' n : ℕ, q ^ (n ^ 2) * qPochhammer q q n /
      qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) n := by
  refine tsum_congr fun n => ?_
  have h := prod_qPochhammer_primitive_mul m n hζ q
  have hP := qPochhammer_self_ne_zero hq n
  rw [← h, mul_div_mul_right _ _ hP]

/-- `G_d(y;q) = (y^d q^d;q^d)_∞ / (yq;q)_∞` [AOS, (1.2)] for `m ≥ 2`, `|q| < 1` and
`y q^r ≠ 1` for all `r ≥ 1`. -/
theorem GProduct_eq_div {m : ℕ} (hm : 2 ≤ m) {q : ℂ} (hq : ‖q‖ < 1) {y : ℂ}
    (hy : ∀ r : ℕ, y * q ^ (r + 1) ≠ 1) :
    GProduct m y q =
      qPochhammerInf (y ^ (2 * m + 1) * q ^ (2 * m + 1)) (q ^ (2 * m + 1)) /
        qPochhammerInf (y * q) q := by
  have hne : qPochhammerInf (y * q) q ≠ 0 :=
    qPochhammerInf_ne_zero hq fun r => by rw [mul_assoc, ← pow_succ']; exact hy r
  rw [eq_div_iff hne, GProduct, qPochhammerInf_def, qPochhammerInf_def,
    ← (multipliable_cyclotomicSum hm hq y).tprod_mul (multipliable_qPochhammerInf (y * q) hq)]
  refine tprod_congr fun r => ?_
  rw [cyclotomicSum, show y * q * q ^ r = y * q ^ (r + 1) by ring]
  have h := geom_sum_mul (y * q ^ (r + 1)) (2 * m + 1)
  rw [show y ^ (2 * m + 1) * q ^ (2 * m + 1) * (q ^ (2 * m + 1)) ^ r =
    (y * q ^ (r + 1)) ^ (2 * m + 1) by ring]
  linear_combination -h

/-- `G_d(q^k;q) = (q^d;q^d)_∞/(q;q)_∞ · (q;q)_k/(q^d;q^d)_k` for `m ≥ 2` and `|q| < 1`. -/
private theorem gTail_one_eq {m : ℕ} (hm : 2 ≤ m) {q : ℂ} (hq : ‖q‖ < 1) (k : ℕ) :
    gTail m 1 k q = qPochhammerInf (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) / qPochhammerInf q q *
      (qPochhammer q q k / qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) k) := by
  set d := 2 * m + 1
  have hqd : ‖q ^ d‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hlt : ∀ r : ℕ, ‖q ^ (r + 1)‖ < 1 := fun r => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hne1 : ∀ r : ℕ, q ^ (r + 1) ≠ 1 := fun r h => by have := hlt r; simp [h] at this
  have hy : ∀ r : ℕ, q ^ k * q ^ (r + 1) ≠ 1 := fun r => by rw [← pow_add]; exact hne1 _
  have hinf : ∀ (a : ℕ), ∀ r : ℕ, q ^ (a + 1) * q ^ r ≠ 1 := fun a r => by
    rw [← pow_add, show a + 1 + r = (a + r) + 1 by ring]; exact hne1 _
  have hinfd : ∀ r : ℕ, q ^ d * (q ^ d) ^ r ≠ 1 := fun r => by
    rw [← pow_succ', ← pow_mul]; have := hne1 (d * (r + 1) - 1)
    rwa [show d * (r + 1) - 1 + 1 = d * (r + 1) by
      have : 1 ≤ d * (r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity); omega] at this
  have hA : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero hq fun r => by
    simpa using hinf 0 r
  have hB : qPochhammerInf (q * q ^ k) q ≠ 0 := qPochhammerInf_ne_zero hq fun r => by
    rw [← pow_succ']; exact hinf k r
  have hP : qPochhammer q q k ≠ 0 := qPochhammer_self_ne_zero hq k
  have hPd : qPochhammer (q ^ d) (q ^ d) k ≠ 0 := qPochhammer_self_ne_zero hqd k
  have h1 := qPochhammer_mul_qPochhammerInf q hq k
  have h2 := qPochhammer_mul_qPochhammerInf (q ^ d) hqd k
  rw [gTail, one_mul, GProduct_eq_div hm hq hy, ← h1, ← h2, mul_comm (q ^ k) q]
  rw [show (q ^ k) ^ d * q ^ d = q ^ d * (q ^ d) ^ k by ring]
  field_simp
  rfl

/-- **The seed specialization** [AOS, (1.3)]: for `m ≥ 2`, `d = 2m + 1`, a primitive `d`-th root
of unity `ζ` and `|q| < 1`, `X_0^{(m)}(1;q) = (q^d;q^d)_∞/(q;q)_∞ · R_m(ζ;q)`. -/
theorem XSeries_one_zero_eq {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m + 1))
    {q : ℂ} (hq : ‖q‖ < 1) :
    XSeries m 1 0 q = qPochhammerInf (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) / qPochhammerInf q q *
      higherDysonSeriesZ m ζ q := by
  rw [higherDysonSeriesZ_primitive m hζ hq, ← tsum_mul_left, XSeries]
  refine tsum_congr fun k => ?_
  rw [gTail_one_eq hm hq k, show ((k : ℤ) ^ 2 + 0 * k) = ((k ^ 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast]
  ring

/-- **The collapse at roots of unity** [AOS, §1, (1.3), §2], all claims together: for
`d = 2m + 1`, a primitive `d`-th root of unity `ζ` and `|q| < 1`,
* for `k ≥ 1`, `∏_{j=1}^m (1 - ζ^j q^k)(1 - ζ^{-j} q^k) = ∏_{r=1}^{d-1} (1 - ζ^r q^k)
  = (1 - q^{dk})/(1 - q^k)`;
* `R_m(ζ;q) = ∑_{n ≥ 0} q^{n²} (q;q)_n/(q^d;q^d)_n`;
* for `m ≥ 2`, `X_0^{(m)}(1;q) = (q^d;q^d)_∞/(q;q)_∞ · R_m(ζ;q)`. -/
theorem higherDysonSeriesZ_primitive_collapse (m : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m + 1)) {q : ℂ} (hq : ‖q‖ < 1) :
    (∀ k : ℕ, 1 ≤ k →
      ∏ j ∈ Icc 1 m, ((1 - ζ ^ j * q ^ k) * (1 - ζ⁻¹ ^ j * q ^ k)) =
          ∏ r ∈ Icc 1 (2 * m), (1 - ζ ^ r * q ^ k) ∧
        ∏ r ∈ Icc 1 (2 * m), (1 - ζ ^ r * q ^ k) =
          (1 - q ^ ((2 * m + 1) * k)) / (1 - q ^ k)) ∧
    higherDysonSeriesZ m ζ q = ∑' n : ℕ, q ^ (n ^ 2) * qPochhammer q q n /
      qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) n ∧
    (2 ≤ m → XSeries m 1 0 q =
      qPochhammerInf (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) / qPochhammerInf q q *
        higherDysonSeriesZ m ζ q) := by
  refine ⟨fun k hk => ?_, higherDysonSeriesZ_primitive m hζ hq,
    fun hm => XSeries_one_zero_eq hm hζ hq⟩
  have hk1 : q ^ k ≠ 1 := fun h => by
    have : ‖q ^ k‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    simp [h] at this
  rw [mul_comm (2 * m + 1) k, pow_mul]
  exact prod_one_sub_primitive_mul m hζ hk1

end HigherDyson3
