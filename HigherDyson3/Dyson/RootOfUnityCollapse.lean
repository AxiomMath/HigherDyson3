/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Definitions
public import HigherDyson3.Dyson.RTermOrder

/-!
# The higher rank series at a primitive root of unity

For `d = 2m + 1` and a primitive `d`-th root of unity `ζ`, the residues `±1, …, ±m` together with
`0` form a complete residue system modulo `d`, so for every `r ≥ 1`
`(1 - q^r) ∏_{j=1}^m (1 - ζ^j q^r)(1 - ζ^{-j} q^r) = 1 - q^{dr}`. Hence the `n`-th term of
`R_m(ζ; q)` is `q^{n²} (q;q)_n / (q^d;q^d)_n`, and `R_m(ζ;q) = ∑_n q^{n²} (q;q)_n / (q^d;q^d)_n`
[AOS, §2].

## Main results

* `HigherDyson3.one_sub_mul_prod_one_sub_zpow`: `(1 - y) ∏_{j=1}^m (1 - ζ^j y)(1 - ζ^{-j} y)
  = 1 - y^{2m+1}` in any commutative `ℂ`-algebra.
* `HigherDyson3.map_zEval_RSeries_eq_primitiveRankSeries`: the formal identity
  `R_m(ζ; q) = ∑_n q^{n²} (q;q)_n / (q^d;q^d)_n` in `ℂ[[q]]`.
* `HigherDyson3.map_zEval_one_RSeries_eq_unitRankSeries`: the formal identity
  `R_m(1; q) = ∑_n q^{n²} / (q;q)_n^{2m}` in `ℂ[[q]]`.
-/

public section

open PowerSeries Finset

namespace HigherDyson3

/-- `∏_{k=0}^{d-1} (1 - ζ^k y) = 1 - y^d` for a primitive `d`-th root of unity `ζ`, `d = 2m + 1`,
and any `y` in a commutative ring receiving `ℂ`. -/
theorem prod_range_one_sub_pow_mul {A : Type*} [CommRing A] (f : ℂ →+* A) (m : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m + 1)) (y : A) :
    ∏ k ∈ range (2 * m + 1), (1 - f (ζ ^ k) * y) = 1 - y ^ (2 * m + 1) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hpoly : ∏ k ∈ range (2 * m + 1), (1 - Polynomial.C (ζ ^ k) * Polynomial.X) =
      1 - Polynomial.X ^ (2 * m + 1) := by
    have h := X_pow_sub_C_eq_prod hζ.inv (α := 1) (a := 1) (by omega) (one_pow _)
    have hfac : ∀ k, (1 - Polynomial.C (ζ ^ k) * Polynomial.X : Polynomial ℂ) =
        Polynomial.C (-ζ ^ k) * (Polynomial.X - Polynomial.C (ζ⁻¹ ^ k * 1)) := by
      intro k
      rw [mul_sub, ← Polynomial.C_mul, mul_one, inv_pow, neg_mul,
        mul_inv_cancel₀ (pow_ne_zero _ hζ0), Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]
      ring
    simp_rw [hfac]
    rw [prod_mul_distrib, ← h, ← map_prod, prod_neg]
    have hsum : ∏ k ∈ range (2 * m + 1), ζ ^ k = 1 := by
      rw [prod_pow_eq_pow_sum]
      have h2 := sum_range_id_mul_two (2 * m + 1)
      have : ∑ i ∈ range (2 * m + 1), i = (2 * m + 1) * m := by
        rw [show (2 * m + 1 - 1) = 2 * m by omega] at h2
        nlinarith
      rw [this, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hsum, card_range, mul_one, Odd.neg_one_pow ⟨m, rfl⟩, Polynomial.C_neg, Polynomial.C_1]
    simp
  have := congrArg (Polynomial.eval₂ f y) hpoly
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_one,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow] at this
  exact this

/-- `(1 - y) ∏_{j=1}^m (1 - ζ^j y)(1 - ζ^{-j} y) = 1 - y^{2m+1}` for a primitive `(2m+1)`-th root
of unity `ζ`: the exponents `0, ±1, …, ±m` run over all residues modulo `2m + 1`. -/
theorem one_sub_mul_prod_one_sub_zpow {A : Type*} [CommRing A] (f : ℂ →+* A) (m : ℕ) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) (y : A) :
    (1 - y) * ∏ j ∈ Icc 1 m,
      ((1 - f ((ζ ^ (j : ℤ) : ℂˣ) : ℂ) * y) * (1 - f ((ζ ^ (-(j : ℤ)) : ℂˣ) : ℂ) * y)) =
      1 - y ^ (2 * m + 1) := by
  rw [← prod_range_one_sub_pow_mul f m hζ y]
  set g : ℕ → A := fun k => 1 - f ((ζ : ℂ) ^ k) * y
  have hneg : ∀ j ∈ Icc 1 m, (1 - f ((ζ ^ (-(j : ℤ)) : ℂˣ) : ℂ) * y) = g (2 * m + 1 - j) := by
    intro j hj
    have hj' := (mem_Icc.mp hj).2
    simp only [g]
    congr 3
    rw [zpow_neg, Units.val_inv_eq_inv_val, zpow_natCast, Units.val_pow_eq_pow_val,
      eq_comm, inv_eq_of_mul_eq_one_left]
    rw [← pow_add, show 2 * m + 1 - j + j = 2 * m + 1 by omega, hζ.pow_eq_one]
  have hpos : ∀ j ∈ Icc 1 m, (1 - f ((ζ ^ (j : ℤ) : ℂˣ) : ℂ) * y) = g j := by
    intro j _
    simp [g]
  rw [prod_congr rfl fun j hj => by rw [hpos j hj, hneg j hj], prod_mul_distrib]
  have h1 : ∏ j ∈ Icc 1 m, g (2 * m + 1 - j) = ∏ j ∈ Ico (m + 1) (2 * m + 1), g j := by
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_reflect g 1 (by omega)]
    congr 1
    ext; simp only [mem_Ico]; omega
  have h0 : (1 - y) = g 0 := by simp [g]
  rw [h1, h0, ← mul_assoc, ← Ico_add_one_right_eq_Icc, range_eq_Ico,
    ← prod_Ico_consecutive _ (Nat.zero_le (m + 1)) (by omega : m + 1 ≤ 2 * m + 1),
    prod_eq_prod_Ico_succ_bot (by omega : 0 < m + 1)]

/-- The `q`-Pochhammer symbol `(cq;q)_n` has constant coefficient `1`. -/
private theorem constantCoeff_qPoch (c : LaurentRing) (n : ℕ) :
    constantCoeff (qPoch c n) = 1 := by
  rw [qPoch, map_prod]
  exact Finset.prod_eq_one fun r hr => by simp [Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hr).1]

/-- `(q^a;q^a)_n` over `ℂ`. -/
private theorem map_formalQPoch (a n : ℕ) :
    map (Int.castRingHom ℂ) (formalQPoch a n) = ∏ r ∈ Icc 1 n, (1 - X ^ (a * r)) := by
  simp [formalQPoch, map_prod]

/-- `(cq;q)_n` evaluated at `z = ζ`. -/
private theorem map_zEval_qPoch (ζ : ℂˣ) (c : LaurentRing) (n : ℕ) :
    map (zEval ζ) (qPoch c n) = ∏ r ∈ Icc 1 n, (1 - C (zEval ζ c) * X ^ r) := by
  simp [qPoch, map_prod]

/-- At a primitive `(2m+1)`-th root of unity `ζ`,
`∏_{j=1}^m (ζ^j q;q)_n (ζ^{-j} q;q)_n · (q;q)_n = (q^{2m+1};q^{2m+1})_n` in `ℂ[[q]]`. -/
private theorem map_zEval_denominator_mul (m n : ℕ) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    map (zEval ζ) (∏ j ∈ Icc 1 m,
        qPoch (LaurentPolynomial.T (j : ℤ)) n * qPoch (LaurentPolynomial.T (-(j : ℤ))) n) *
      map (Int.castRingHom ℂ) (formalQPoch 1 n) =
      map (Int.castRingHom ℂ) (formalQPoch (2 * m + 1) n) := by
  simp only [map_prod, map_mul, map_zEval_qPoch, map_formalQPoch, one_mul]
  simp only [zEval, LaurentPolynomial.eval₂_T]
  rw [← prod_congr rfl fun j _ => prod_mul_distrib, prod_comm, ← prod_mul_distrib]
  refine prod_congr rfl fun r _ => ?_
  rw [mul_comm, one_sub_mul_prod_one_sub_zpow C m ζ hζ (X ^ r), ← pow_mul, mul_comm r]

/-- The `n`-th term of `R_m` at a primitive `(2m+1)`-th root of unity:
`𝒯_{m,n}(ζ; q) = q^{n²} (q;q)_n / (q^d;q^d)_n`. -/
theorem map_zEval_RTerm (m n : ℕ) (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    map (zEval ζ) (RTerm m n) = map (Int.castRingHom ℂ)
      (X ^ (n ^ 2) * formalQPoch 1 n * invOfUnit (formalQPoch (2 * m + 1) n) 1) := by
  set D := ∏ j ∈ Icc 1 m,
    qPoch (LaurentPolynomial.T (j : ℤ)) n * qPoch (LaurentPolynomial.T (-(j : ℤ))) n
  set Q := formalQPoch (2 * m + 1) n
  have hD : constantCoeff D = 1 := by
    simp only [D, map_prod, map_mul, constantCoeff_qPoch, mul_one, prod_const_one]
  have hQ : constantCoeff Q = 1 := by
    simp only [Q, formalQPoch, map_prod, map_sub, map_one, map_pow, constantCoeff_X]
    refine prod_eq_one fun r hr => ?_
    have : r ≠ 0 := by have := (mem_Icc.mp hr).1; omega
    simp [this]
  have hA : map (zEval ζ) (seriesInv D) * map (zEval ζ) D = 1 := by
    rw [← map_mul, seriesInv, mul_comm, mul_invOfUnit D 1 (by simp [hD]), map_one]
  have hB : map (Int.castRingHom ℂ) (invOfUnit Q 1) * map (Int.castRingHom ℂ) Q = 1 := by
    rw [← map_mul, mul_comm, mul_invOfUnit Q 1 (by simp [hQ]), map_one]
  have hDQ := map_zEval_denominator_mul m n ζ hζ
  rw [RTerm, map_mul, map_mul, map_mul, map_pow, map_pow, map_X, map_X, mul_assoc]
  congr 1
  calc map (zEval ζ) (seriesInv D)
      = map (zEval ζ) (seriesInv D) * (map (Int.castRingHom ℂ) Q *
          map (Int.castRingHom ℂ) (invOfUnit Q 1)) := by
        rw [mul_comm _ (map _ (invOfUnit Q 1)), hB, mul_one]
    _ = (map (zEval ζ) (seriesInv D) * map (zEval ζ) D) *
          map (Int.castRingHom ℂ) (formalQPoch 1 n) * map (Int.castRingHom ℂ) (invOfUnit Q 1) := by
        rw [← hDQ]; ring
    _ = _ := by rw [hA, one_mul]

/-- **Collapse at a primitive root of unity** [AOS, §2]: for `m ≥ 1`, `d = 2m + 1` and a
primitive `d`-th root of unity `ζ`, `R_m(ζ; q) = ∑_{n ≥ 0} q^{n²} (q;q)_n / (q^d;q^d)_n` as formal
power series in `q`. -/
theorem map_zEval_RSeries_eq_primitiveRankSeries (m : ℕ) (_hm : 1 ≤ m) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    map (zEval ζ) (RSeries m) = map (Int.castRingHom ℂ) (primitiveRankSeries m) := by
  ext N
  have hsupp : (Function.support fun n => coeff N (RTerm m n)) ⊆ (range (N + 1) : Set ℕ) := by
    intro n hn
    simp only [coe_range, Set.mem_Iio]
    by_contra h
    exact hn (RTerm_coeff_eq_zero_of_lt m (by nlinarith))
  rw [coeff_map, coeff_map, RSeries, primitiveRankSeries, coeff_mk, coeff_mk,
    finsum_eq_sum_of_support_subset _ hsupp, map_sum, map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [← coeff_map, ← coeff_map, map_zEval_RTerm m n ζ hζ]

/-- The formal series `U_m(q) = ∑_{n ≥ 0} q^{n²} / (q;q)_n^{2m} ∈ ℤ[[q]]` [AOS, Corollary 2.7];
coefficientwise, the `N`-th coefficient only involves `n ≤ N`. -/
noncomputable def unitRankSeries (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun N => ∑ n ∈ range (N + 1),
    coeff N (X ^ (n ^ 2) * invOfUnit (formalQPoch 1 n ^ (2 * m)) 1)

/-- The `n`-th term of `R_m` at `z = 1`: `𝒯_{m,n}(1; q) = q^{n²} / (q;q)_n^{2m}`. -/
theorem map_zEval_one_RTerm (m n : ℕ) :
    map (zEval 1) (RTerm m n) =
      map (Int.castRingHom ℂ) (X ^ (n ^ 2) * invOfUnit (formalQPoch 1 n ^ (2 * m)) 1) := by
  set D := ∏ j ∈ Icc 1 m,
    qPoch (LaurentPolynomial.T (j : ℤ)) n * qPoch (LaurentPolynomial.T (-(j : ℤ))) n
  set Q := formalQPoch 1 n ^ (2 * m)
  have hD : constantCoeff D = 1 := by
    simp only [D, map_prod, map_mul, constantCoeff_qPoch, mul_one, prod_const_one]
  have hQ : constantCoeff Q = 1 := by
    simp only [Q, formalQPoch, map_pow, map_prod, map_sub, map_one, constantCoeff_X]
    rw [prod_eq_one fun r hr => ?_, one_pow]
    have : r ≠ 0 := by have := (mem_Icc.mp hr).1; omega
    simp [this]
  have hA : map (zEval 1) (seriesInv D) * map (zEval 1) D = 1 := by
    rw [← map_mul, seriesInv, mul_comm, mul_invOfUnit D 1 (by simp [hD]), map_one]
  have hB : map (Int.castRingHom ℂ) (invOfUnit Q 1) * map (Int.castRingHom ℂ) Q = 1 := by
    rw [← map_mul, mul_comm, mul_invOfUnit Q 1 (by simp [hQ]), map_one]
  have hDQ : map (zEval 1) D = map (Int.castRingHom ℂ) Q := by
    simp only [D, Q, map_prod, map_mul, map_pow, map_zEval_qPoch, map_formalQPoch, one_mul]
    simp only [zEval, LaurentPolynomial.eval₂_T, one_zpow, Units.val_one, map_one, one_mul]
    rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← sq, ← pow_mul, mul_comm]
  rw [RTerm, map_mul, map_mul, map_pow, map_pow, map_X, map_X]
  congr 1
  calc map (zEval 1) (seriesInv D)
      = map (zEval 1) (seriesInv D) * (map (Int.castRingHom ℂ) Q *
          map (Int.castRingHom ℂ) (invOfUnit Q 1)) := by
        rw [mul_comm _ (map _ (invOfUnit Q 1)), hB, mul_one]
    _ = (map (zEval 1) (seriesInv D) * map (zEval 1) D) *
          map (Int.castRingHom ℂ) (invOfUnit Q 1) := by
        rw [hDQ]; ring
    _ = _ := by rw [hA, one_mul]

/-- **The higher rank series at `z = 1`** [AOS, Corollary 2.7]:
`R_m(1; q) = ∑_{n ≥ 0} q^{n²} / (q;q)_n^{2m}` as formal power series in `q`. -/
theorem map_zEval_one_RSeries_eq_unitRankSeries (m : ℕ) :
    map (zEval 1) (RSeries m) = map (Int.castRingHom ℂ) (unitRankSeries m) := by
  ext N
  have hsupp : (Function.support fun n => coeff N (RTerm m n)) ⊆ (range (N + 1) : Set ℕ) := by
    intro n hn
    simp only [coe_range, Set.mem_Iio]
    by_contra h
    exact hn (RTerm_coeff_eq_zero_of_lt m (by nlinarith))
  rw [coeff_map, coeff_map, RSeries, unitRankSeries, coeff_mk, coeff_mk,
    finsum_eq_sum_of_support_subset _ hsupp, map_sum, map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [← coeff_map, ← coeff_map, map_zEval_one_RTerm m n]

end HigherDyson3
