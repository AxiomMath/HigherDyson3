/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Definitions
public import HigherDyson3.Dyson.RootOfUnityCollapse

/-!
# The backward polynomials `P_J`

At `x = 1`, `γ = 1`, solving the recurrence backwards from the terminal values
`Y_J = ⋯ = Y_{J+2m-1} = 1` gives polynomials `Y_j ∈ ℤ[q]`, and `P_J = Y_0` agrees with
`R_m(ζ_d; q)` modulo `q^{J+1}` [AOS, Theorem 7.1(iii)].

The proof works in `ℤ[[q]]` with the truncations
`Y*_j = ∑_{n < K} q^{n² + jn} (q;q)_n / (q^d;q^d)_n`, `K = J + 1`, of the formal Dyson sequence.
These satisfy `Y*_j ≡ 1 (mod q^{j+1})` and the recurrence
`∑_{r=0}^{d-1} Y*_{i+r} - q^{i+1} Y*_{i+2} ≡ d (mod q^{J+1})`: as in [AOS, proof of Lemma 7.2(b)]
the left side telescopes, by `(1 - q^n) P_d(q^n) = 1 - q^{dn}`, to `d` minus a boundary term
divisible by `q^{K²}`. A descending induction then gives `Y_j ≡ Y*_j (mod q^{J+1})`
[AOS, proof of Theorem 7.1(iii)].

## Main results

* `HigherDyson3.coeff_backwardPolynomial`: `[q^N] P_J = [q^N] ∑_n q^{n²} (q;q)_n/(q^d;q^d)_n`
  for `N ≤ J`.
* `HigherDyson3.backwardPolynomial_congr_RSeries`: `R_m(ζ_d; q) ≡ P_J(q) (mod q^{J+1})`.
-/

public section

noncomputable section

open Finset PowerSeries

namespace HigherDyson3

/-- The formal ratio `(q;q)_n / (q^d;q^d)_n ∈ ℤ[[q]]`, `d = 2m + 1`. -/
def formalRatio (m n : ℕ) : PowerSeries ℤ :=
  formalQPoch 1 n * invOfUnit (formalQPoch (2 * m + 1) n) 1

/-- The truncated formal Dyson sequence `Y*_j = ∑_{n < K} q^{n² + jn} (q;q)_n / (q^d;q^d)_n`. -/
def formalDysonTrunc (m K j : ℕ) : PowerSeries ℤ :=
  ∑ n ∈ range K, X ^ (n ^ 2 + j * n) * formalRatio m n

theorem formalQPoch_zero (a : ℕ) : formalQPoch a 0 = 1 := by
  simp [formalQPoch]

theorem formalQPoch_succ (a n : ℕ) :
    formalQPoch a (n + 1) = formalQPoch a n * (1 - X ^ (a * (n + 1))) := by
  rw [formalQPoch, formalQPoch, prod_Icc_succ_top (by omega)]

theorem constantCoeff_formalQPoch {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    constantCoeff (formalQPoch a n) = 1 := by
  rw [formalQPoch, map_prod]
  refine prod_eq_one fun r hr => ?_
  have : a * r ≠ 0 := by have := (mem_Icc.mp hr).1; positivity
  simp [this]

theorem formalQPoch_mul_inv (m n : ℕ) :
    formalQPoch (2 * m + 1) n * invOfUnit (formalQPoch (2 * m + 1) n) 1 = 1 :=
  mul_invOfUnit _ _ (by rw [constantCoeff_formalQPoch (by omega)]; simp)

theorem formalRatio_zero (m : ℕ) : formalRatio m 0 = 1 := by
  have h := formalQPoch_mul_inv m 0
  rw [formalQPoch_zero, one_mul] at h
  simp only [formalRatio, formalQPoch_zero, one_mul]
  exact h

/-- `P_d(y) = ∑_{r<d} y^r` over `ℤ[[q]]`. -/
def formalCyclotomicSum (m : ℕ) (y : PowerSeries ℤ) : PowerSeries ℤ :=
  ∑ r ∈ range (2 * m + 1), y ^ r

/-- **The formal recursion of the ratios**:
`(q;q)_{n+1}/(q^d;q^d)_{n+1} · P_d(q^{n+1}) = (q;q)_n/(q^d;q^d)_n`. -/
theorem formalRatio_succ_mul (m n : ℕ) :
    formalRatio m (n + 1) * formalCyclotomicSum m (X ^ (n + 1)) = formalRatio m n := by
  set P := formalQPoch (2 * m + 1) n
  set P' := formalQPoch (2 * m + 1) (n + 1)
  have hP : P ≠ 0 := fun h => by
    have := constantCoeff_formalQPoch (a := 2 * m + 1) (by omega) n
    rw [← show P = formalQPoch (2 * m + 1) n from rfl, h, map_zero] at this
    exact zero_ne_one this
  have hgeom : formalCyclotomicSum m (X ^ (n + 1)) * (1 - X ^ (n + 1)) =
      1 - X ^ ((2 * m + 1) * (n + 1)) := by
    rw [formalCyclotomicSum, geom_sum_mul_neg, ← pow_mul, mul_comm (n + 1)]
  have hinv : (1 - X ^ ((2 * m + 1) * (n + 1))) * invOfUnit P' 1 = invOfUnit P 1 := by
    refine mul_left_cancel₀ hP ?_
    rw [← mul_assoc, ← formalQPoch_succ, formalQPoch_mul_inv, formalQPoch_mul_inv]
  rw [formalRatio, formalRatio, formalQPoch_succ, one_mul, ← hinv, ← hgeom]
  ring

/-- `Y*_j ≡ 1 (mod q^{j+1})` [AOS, (7.16)]. -/
theorem X_pow_dvd_formalDysonTrunc_sub_one (m : ℕ) {K : ℕ} (hK : 1 ≤ K) (j : ℕ) :
    X ^ (j + 1) ∣ formalDysonTrunc m K j - 1 := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  rw [formalDysonTrunc, sum_range_succ', formalRatio_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    pow_zero, mul_one, add_sub_cancel_right]
  refine dvd_sum fun n _ => dvd_mul_of_dvd_left (pow_dvd_pow _ ?_) _
  nlinarith

/-- **The formal recurrence modulo `q^{J+1}`.** For `K ≥ J + 1` and every `i`,
`∑_{r=0}^{d-1} Y*_{i+r} - q^{i+1} Y*_{i+2} ≡ d (mod q^{J+1})`. -/
theorem X_pow_dvd_formalDysonTrunc_recurrence (m : ℕ) {J K : ℕ} (hK : J + 1 ≤ K) (i : ℕ) :
    X ^ (J + 1) ∣ (∑ r ∈ range (2 * m + 1), formalDysonTrunc m K (i + r) -
      X ^ (i + 1) * formalDysonTrunc m K (i + 2)) - (2 * m + 1 : PowerSeries ℤ) := by
  set a : ℕ → PowerSeries ℤ := fun n =>
    X ^ (n ^ 2 + i * n) * formalRatio m n * formalCyclotomicSum m (X ^ n) with ha
  have h1 : ∑ r ∈ range (2 * m + 1), formalDysonTrunc m K (i + r) = ∑ n ∈ range K, a n := by
    simp only [formalDysonTrunc]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => ?_
    simp only [ha, formalCyclotomicSum, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [← pow_mul, show n ^ 2 + (i + r) * n = (n ^ 2 + i * n) + n * r by ring, pow_add]
    ring
  have h2 : X ^ (i + 1) * formalDysonTrunc m K (i + 2) = ∑ n ∈ range K, a (n + 1) := by
    simp only [formalDysonTrunc, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    simp only [ha]
    rw [mul_assoc _ (formalRatio m (n + 1)), formalRatio_succ_mul, ← mul_assoc, ← pow_add]
    congr 2
    ring
  have ha0 : a 0 = (2 * m + 1 : PowerSeries ℤ) := by
    simp [ha, formalRatio_zero, formalCyclotomicSum]
  rw [h1, h2, ← sum_sub_distrib, sum_range_sub', ha0, sub_sub_cancel_left]
  refine (dvd_neg).mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow _ ?_) _) _)
  nlinarith

/-- The terminal values of the backward solution. -/
theorem backwardSequence_of_le {m J i : ℕ} (h : J ≤ i) : backwardSequence m J i = 1 := by
  rw [backwardSequence]
  simp only [h, ↓reduceIte]

/-- One backward step (7.14). -/
theorem backwardSequence_of_lt {m J i : ℕ} (h : i < J) :
    backwardSequence m J i = (2 * m + 1 : Polynomial ℤ) +
      Polynomial.X ^ (i + 1) * backwardSequence m J (i + 2) -
      ∑ r ∈ Ico 1 (2 * m + 1), backwardSequence m J (i + r) := by
  rw [backwardSequence]
  simp only [show ¬J ≤ i by omega, ↓reduceIte]
  rw [sum_attach (Ico 1 (2 * m + 1))
    (fun r => backwardSequence m J (i + r))]

/-- **The backward solution agrees with the formal Dyson sequence modulo `q^{J+1}`**
[AOS, proof of Theorem 7.1(iii)]. -/
theorem X_pow_dvd_backwardSequence_sub (m J i : ℕ) :
    X ^ (J + 1) ∣ (backwardSequence m J i : PowerSeries ℤ) - formalDysonTrunc m (J + 1) i := by
  have key : ∀ k i, J ≤ i + k →
      X ^ (J + 1) ∣ (backwardSequence m J i : PowerSeries ℤ) - formalDysonTrunc m (J + 1) i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      rw [backwardSequence_of_le (by omega), Polynomial.coe_one, ← neg_sub, dvd_neg]
      exact (pow_dvd_pow X (by omega)).trans
        (X_pow_dvd_formalDysonTrunc_sub_one m (by omega) i)
    | succ k ih =>
      intro i hi
      by_cases hik : J ≤ i + k
      · exact ih i hik
      · set Y := fun n => formalDysonTrunc m (J + 1) n
        set B := fun n => (backwardSequence m J n : PowerSeries ℤ)
        have hE := X_pow_dvd_formalDysonTrunc_recurrence m (J := J) (K := J + 1) le_rfl i
        have hsplit : ∑ r ∈ range (2 * m + 1), Y (i + r) =
            Y i + ∑ r ∈ Ico 1 (2 * m + 1), Y (i + r) := by
          rw [sum_range_succ', sum_Ico_eq_sum_range, add_comm]
          simp only [add_zero, Nat.add_sub_cancel]
          congr 1
          exact sum_congr rfl fun r _ => by rw [add_comm 1 r]
        have hB : B i = (2 * m + 1 : PowerSeries ℤ) + X ^ (i + 1) * B (i + 2) -
            ∑ r ∈ Ico 1 (2 * m + 1), B (i + r) := by
          simp only [B]
          rw [backwardSequence_of_lt (by omega)]
          simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub, map_mul,
            map_pow, map_sum, map_natCast, map_ofNat, map_one]
          simp [Polynomial.coeToPowerSeries.ringHom_apply]
        have hid : B i - Y i = X ^ (i + 1) * (B (i + 2) - Y (i + 2)) -
            ∑ r ∈ Ico 1 (2 * m + 1), (B (i + r) - Y (i + r)) -
            ((∑ r ∈ range (2 * m + 1), Y (i + r) - X ^ (i + 1) * Y (i + 2)) -
              (2 * m + 1 : PowerSeries ℤ)) := by
          rw [hB, hsplit, sum_sub_distrib]
          ring
        change X ^ (J + 1) ∣ B i - Y i
        rw [hid]
        refine dvd_sub (dvd_sub (dvd_mul_of_dvd_right (ih _ (by omega)) _)
          (dvd_sum fun r hr => ih _ ?_)) hE
        have := (mem_Ico.mp hr).1
        omega
  exact key J i (by omega)

/-- The coefficients of `Y*_0` up to `q^J` are those of `∑_n q^{n²} (q;q)_n/(q^d;q^d)_n`. -/
theorem coeff_formalDysonTrunc_zero {m J N : ℕ} (hN : N ≤ J) :
    coeff N (formalDysonTrunc m (J + 1) 0) = coeff N (primitiveRankSeries m) := by
  rw [formalDysonTrunc, primitiveRankSeries, coeff_mk, map_sum]
  simp only [zero_mul, add_zero, formalRatio, mul_assoc]
  refine (sum_subset (range_subset_range.mpr (by omega)) fun n _ hn' => ?_).symm
  simp only [mem_range, not_lt] at hn'
  rw [coeff_X_pow_mul']
  simp only [show ¬n ^ 2 ≤ N by nlinarith, ↓reduceIte]

/-- **Theorem 7.1(iii), coefficientwise.** The backward polynomial `P_J ∈ ℤ[q]` has the same
coefficients up to `q^J` as `∑_{n ≥ 0} q^{n²} (q;q)_n / (q^d;q^d)_n`, `d = 2m + 1`
[AOS, Theorem 7.1(iii)]. -/
theorem coeff_backwardPolynomial (m J : ℕ) {N : ℕ} (hN : N ≤ J) :
    (backwardPolynomial m J).coeff N = coeff N (primitiveRankSeries m) := by
  have h := (X_pow_dvd_iff.mp (X_pow_dvd_backwardSequence_sub m J 0)) N (by omega)
  rw [map_sub, Polynomial.coeff_coe, sub_eq_zero] at h
  rw [backwardPolynomial, h, coeff_formalDysonTrunc_zero hN]

/-- **Theorem 7.1(iii) in `ℤ[[q]]`.** `P_J ≡ ∑_n q^{n²} (q;q)_n / (q^d;q^d)_n (mod q^{J+1})`
[AOS, Theorem 7.1(iii)]. -/
theorem X_pow_dvd_primitiveRankSeries_sub_backwardPolynomial (m J : ℕ) :
    X ^ (J + 1) ∣ primitiveRankSeries m - (backwardPolynomial m J : PowerSeries ℤ) := by
  refine X_pow_dvd_iff.mpr fun N hN => ?_
  rw [map_sub, Polynomial.coeff_coe, coeff_backwardPolynomial m J (by omega), sub_self]

/-- **Theorem 7.1(iii).** For `m ≥ 1`, `d = 2m + 1`, a primitive `d`-th root of unity `ζ` and
`J ≥ 0`, the backward polynomial `P_J ∈ ℤ[q]` of (7.14) satisfies
`R_m(ζ; q) ≡ P_J(q) (mod q^{J+1})` in `ℂ[[q]]` [AOS, Theorem 7.1(iii)]. -/
theorem X_pow_dvd_RSeries_sub_backwardPolynomial (m : ℕ) (hm : 1 ≤ m) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) (J : ℕ) :
    X ^ (J + 1) ∣ map (zEval ζ) (RSeries m) -
      map (Int.castRingHom ℂ) (backwardPolynomial m J : PowerSeries ℤ) := by
  rw [map_zEval_RSeries_eq_primitiveRankSeries m hm ζ hζ, ← map_sub]
  obtain ⟨g, hg⟩ := X_pow_dvd_primitiveRankSeries_sub_backwardPolynomial m J
  exact ⟨map (Int.castRingHom ℂ) g, by rw [hg, map_mul, map_pow, map_X]⟩

/-- **Theorem 7.1(iii), coefficientwise in `ℂ`.** For `N ≤ J`, the `N`-th coefficient of `P_J`
equals the `N`-th coefficient of `R_m(ζ; q)` [AOS, Theorem 7.1(iii)]. -/
theorem coeff_backwardPolynomial_eq_coeff_RSeries (m : ℕ) (hm : 1 ≤ m) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) {J N : ℕ} (hN : N ≤ J) :
    ((backwardPolynomial m J).coeff N : ℂ) = coeff N (map (zEval ζ) (RSeries m)) := by
  rw [map_zEval_RSeries_eq_primitiveRankSeries m hm ζ hζ, coeff_map,
    coeff_backwardPolynomial m J hN]
  rfl

/-- The example of [AOS, §7]: for `m = 2` and `J = 4`, `P_4 = 1 + q - q² + q⁴ - q⁵ - q⁶`. -/
theorem backwardPolynomial_two_four :
    backwardPolynomial 2 4 = 1 + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 4 -
      Polynomial.X ^ 5 - Polynomial.X ^ 6 := by
  have h3 : backwardSequence 2 4 3 = 1 + Polynomial.X ^ 4 := by
    rw [backwardSequence_of_lt (by norm_num)]
    simp [backwardSequence_of_le, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
    ring
  have h2 : backwardSequence 2 4 2 = 1 + Polynomial.X ^ 3 - Polynomial.X ^ 4 := by
    rw [backwardSequence_of_lt (by norm_num)]
    simp [backwardSequence_of_le, h3, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
    ring
  have h1 : backwardSequence 2 4 1 =
      1 + Polynomial.X ^ 2 - Polynomial.X ^ 3 + Polynomial.X ^ 6 := by
    rw [backwardSequence_of_lt (by norm_num)]
    simp [backwardSequence_of_le, h3, h2, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
    ring
  rw [backwardPolynomial, backwardSequence_of_lt (by norm_num)]
  simp [backwardSequence_of_le, h3, h2, h1, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  ring

/-- **Theorem 7.1(iii)** [AOS, Theorem 7.1(iii)]. For `m ≥ 1`, `d = 2m + 1`, a primitive
`d`-th root of unity `ζ` and `J ≥ 0`, the backward polynomial `P_J = Y_0 ∈ ℤ[q]` of (7.14)
satisfies `R_m(ζ; q) ≡ P_J(q) (mod q^{J+1})`, i.e. their coefficients agree up to `q^J`; and
for `m = 2`, `P_4 = 1 + q - q² + q⁴ - q⁵ - q⁶`. -/
theorem backwardPolynomial_congruence (m : ℕ) (hm : 1 ≤ m) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) (J : ℕ) :
    (X ^ (J + 1) ∣ map (zEval ζ) (RSeries m) -
      map (Int.castRingHom ℂ) (backwardPolynomial m J : PowerSeries ℤ)) ∧
    (∀ N ≤ J, ((backwardPolynomial m J).coeff N : ℂ) = coeff N (map (zEval ζ) (RSeries m))) ∧
    backwardPolynomial 2 4 = 1 + Polynomial.X - Polynomial.X ^ 2 + Polynomial.X ^ 4 -
      Polynomial.X ^ 5 - Polynomial.X ^ 6 :=
  ⟨X_pow_dvd_RSeries_sub_backwardPolynomial m hm ζ hζ J,
    fun _ hN => coeff_backwardPolynomial_eq_coeff_RSeries m hm ζ hζ hN,
    backwardPolynomial_two_four⟩

end HigherDyson3
