/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Backward
public import HigherDyson3.Dyson.AnalyticSeries
import HigherDyson3.Bounds.GaussianSummable

/-!
# The formal and the analytic higher Dyson series at a primitive root of unity

For `d = 2m + 1`, a primitive `d`-th root of unity `ζ` and `‖q‖ < 1`, the analytic series
`R_m(ζ;q) = ∑_{n ≥ 0} q^{n²} (q;q)_n/(q^d;q^d)_n` [AOS, §1, (1.3)] is the sum of the formal power
series `R_m(ζ;q) ∈ ℤ[[q]]` evaluated at `q`, and the convergence is absolute. Consequently
`R_m(ζ;·)` is holomorphic on the unit disc with Taylor coefficients those of the formal series, and
the backward polynomial `P_J` agrees with `R_m(ζ;q)` modulo `q^{J+1}` as analytic functions
[AOS, Theorem 7.1(iii)].

The proof expands each term `q^{n²} (q;q)_n/(q^d;q^d)_n` as a finite product of absolutely
convergent power series (`1 - q^r` and the geometric series `1/(1 - q^{dr})`), bounds its absolute
sum by `‖q‖^{n²} (2/(1 - ‖q‖))^n`, and interchanges the two sums.

## Main results

* `HigherDyson3.hasSum_coeff_primitiveRankSeries_mul_pow`:
  `∑_N [q^N] R_m(ζ;q) · q^N = R_m(ζ;q)` for `‖q‖ < 1`.
* `HigherDyson3.hasSum_coeff_map_zEval_RSeries_mul_pow`: the same with the formal series
  `RSeries m` evaluated at `z = ζ`.
* `HigherDyson3.hasFPowerSeriesOnBall_higherDysonSeriesZ`: `R_m(ζ;·)` has the formal series as its
  power series expansion on the unit disc; `HigherDyson3.differentiableOn_higherDysonSeriesZ`.
* `HigherDyson3.higherDysonSeriesZ_sub_backwardPolynomial`: `R_m(ζ;q) - P_J(q) = q^{J+1} F(q)` with
  `F` holomorphic on the unit disc.
-/

public section

noncomputable section

open Finset PowerSeries

namespace HigherDyson3

/-- A power series `f` converges absolutely at `q` with sum `v` and absolute sum at most `B`. -/
private def AbsEval (f : PowerSeries ℂ) (q v : ℂ) (B : ℝ) : Prop :=
  (Summable fun N => ‖coeff N f * q ^ N‖) ∧ HasSum (fun N => coeff N f * q ^ N) v ∧
    ∑' N, ‖coeff N f * q ^ N‖ ≤ B

private theorem AbsEval.mono {f : PowerSeries ℂ} {q v : ℂ} {B B' : ℝ} (h : AbsEval f q v B)
    (hB : B ≤ B') : AbsEval f q v B' :=
  ⟨h.1, h.2.1, h.2.2.trans hB⟩

private theorem AbsEval.nonneg {f : PowerSeries ℂ} {q v : ℂ} {B : ℝ} (h : AbsEval f q v B) :
    0 ≤ B :=
  (tsum_nonneg fun _ => norm_nonneg _).trans h.2.2

private theorem coeff_mul_mul_pow (f g : PowerSeries ℂ) (q : ℂ) (N : ℕ) :
    coeff N (f * g) * q ^ N = ∑ kl ∈ antidiagonal N,
      (coeff kl.1 f * q ^ kl.1) * (coeff kl.2 g * q ^ kl.2) := by
  rw [coeff_mul, sum_mul]
  refine sum_congr rfl fun kl hkl => ?_
  rw [← mem_antidiagonal.mp hkl, pow_add]
  ring

private theorem AbsEval.mul {f g : PowerSeries ℂ} {q v w : ℂ} {B C : ℝ} (hf : AbsEval f q v B)
    (hg : AbsEval g q w C) : AbsEval (f * g) q (v * w) (B * C) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  simp only [AbsEval, coeff_mul_mul_pow]
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf1 hg1
  refine ⟨hs, ?_, ?_⟩
  · rw [← hf2.tsum_eq, ← hg2.tsum_eq,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf1 hg1]
    exact (hs.of_norm).hasSum
  · have hf1' : Summable fun N => ‖‖coeff N f * q ^ N‖‖ := by simpa using hf1
    have hg1' : Summable fun N => ‖‖coeff N g * q ^ N‖‖ := by simpa using hg1
    have hs' := summable_norm_sum_mul_antidiagonal_of_summable_norm hf1' hg1'
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf1' hg1'
    calc ∑' N, ‖∑ kl ∈ antidiagonal N, (coeff kl.1 f * q ^ kl.1) * (coeff kl.2 g * q ^ kl.2)‖
        ≤ ∑' N, ∑ kl ∈ antidiagonal N, ‖coeff kl.1 f * q ^ kl.1‖ * ‖coeff kl.2 g * q ^ kl.2‖ := by
          refine Summable.tsum_le_tsum (fun N => ?_) hs hs'.of_norm
          exact (norm_sum_le _ _).trans (sum_le_sum fun kl _ => norm_mul_le _ _)
      _ = (∑' N, ‖coeff N f * q ^ N‖) * ∑' N, ‖coeff N g * q ^ N‖ := heq.symm
      _ ≤ B * C := mul_le_mul hf3 hg3 (tsum_nonneg fun _ => norm_nonneg _)
          ((tsum_nonneg fun _ => norm_nonneg _).trans hf3)

private theorem AbsEval.sub {f g : PowerSeries ℂ} {q v w : ℂ} {B C : ℝ} (hf : AbsEval f q v B)
    (hg : AbsEval g q w C) : AbsEval (f - g) q (v - w) (B + C) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hle : ∀ N, ‖coeff N (f - g) * q ^ N‖ ≤ ‖coeff N f * q ^ N‖ + ‖coeff N g * q ^ N‖ :=
    fun N => by rw [map_sub, sub_mul]; exact norm_sub_le _ _
  have hs : Summable fun N => ‖coeff N (f - g) * q ^ N‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hf1.add hg1)
  refine ⟨hs, ?_, ?_⟩
  · simpa only [map_sub, sub_mul] using hf2.sub hg2
  · calc ∑' N, ‖coeff N (f - g) * q ^ N‖
        ≤ ∑' N, (‖coeff N f * q ^ N‖ + ‖coeff N g * q ^ N‖) :=
          Summable.tsum_le_tsum hle hs (hf1.add hg1)
      _ = _ := hf1.tsum_add hg1
      _ ≤ B + C := add_le_add hf3 hg3

private theorem AbsEval.X_pow (q : ℂ) (k : ℕ) : AbsEval (X ^ k) q (q ^ k) (‖q‖ ^ k) := by
  have hfin : ∀ N ∉ ({k} : Finset ℕ), coeff N (X ^ k : PowerSeries ℂ) * q ^ N = 0 := by
    intro N hN
    rw [coeff_X_pow, ite_eq_right (by simpa using hN), zero_mul]
  have hfin' : ∀ N ∉ ({k} : Finset ℕ), ‖coeff N (X ^ k : PowerSeries ℂ) * q ^ N‖ = 0 := by
    intro N hN; rw [hfin N hN, norm_zero]
  refine ⟨summable_of_ne_finset_zero hfin', ?_, ?_⟩
  · simpa using hasSum_sum_of_ne_finset_zero hfin
  · rw [tsum_eq_sum hfin']
    simp

private theorem AbsEval.one (q : ℂ) : AbsEval 1 q 1 1 := by
  simpa using AbsEval.X_pow q 0

private theorem AbsEval.prod {ι : Type*} (s : Finset ι) {F : ι → PowerSeries ℂ} {q : ℂ}
    {v : ι → ℂ} {B : ι → ℝ} (h : ∀ i ∈ s, AbsEval (F i) q (v i) (B i)) :
    AbsEval (∏ i ∈ s, F i) q (∏ i ∈ s, v i) (∏ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AbsEval.one q
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- The geometric series `∑_k q^{bk} = 1/(1 - q^b)` as a formal power series. -/
private def geomSeries (b : ℕ) : PowerSeries ℂ := mk fun N => if b ∣ N then 1 else 0

private theorem one_sub_X_pow_mul_geomSeries {b : ℕ} (hb : 1 ≤ b) :
    (1 - X ^ b) * geomSeries b = 1 := by
  ext N
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomSeries, coeff_mk, coeff_one]
  by_cases hN : N = 0
  · subst hN
    simp [show ¬b ≤ 0 by omega]
  · rw [ite_eq_right hN, coeff_mk]
    by_cases hbN : b ≤ N
    · rw [ite_eq_left hbN]
      have hiff : b ∣ N - b ↔ b ∣ N := Nat.dvd_sub_iff_left hbN dvd_rfl
      by_cases h : b ∣ N
      · rw [ite_eq_left h, ite_eq_left (hiff.mpr h), sub_self]
      · rw [ite_eq_right h, ite_eq_right (mt hiff.mp h), sub_self]
    · rw [ite_eq_right hbN, sub_zero, ite_eq_right]
      exact fun h => hbN (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h)

private theorem hasSum_ite_dvd_pow {K : Type*} [NormedDivisionRing K] [CompleteSpace K] {x : K}
    (hx : ‖x‖ < 1) {b : ℕ} (hb : 1 ≤ b) :
    HasSum (fun N => if b ∣ N then x ^ N else 0) (1 - x ^ b)⁻¹ := by
  have hxb : ‖x ^ b‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by omega)
  have hinj : Function.Injective fun k : ℕ => b * k := fun k l h =>
    Nat.eq_of_mul_eq_mul_left (by omega) h
  rw [← hinj.hasSum_iff]
  · convert hasSum_geometric_of_norm_lt_one hxb using 1
    ext k
    simp [pow_mul]
  · intro N hN
    rw [ite_eq_right]
    rintro ⟨k, rfl⟩
    exact hN ⟨k, rfl⟩

private theorem AbsEval.geomSeries {q : ℂ} (hq : ‖q‖ < 1) {b : ℕ} (hb : 1 ≤ b) :
    AbsEval (geomSeries b) q (1 - q ^ b)⁻¹ (1 - ‖q‖ ^ b)⁻¹ := by
  have hterm : ∀ N, coeff N (HigherDyson3.geomSeries b) * q ^ N =
      if b ∣ N then q ^ N else 0 := fun N => by
    rw [HigherDyson3.geomSeries, coeff_mk]; split_ifs <;> simp
  have hnorm : ∀ N, ‖coeff N (HigherDyson3.geomSeries b) * q ^ N‖ =
      if b ∣ N then ‖q‖ ^ N else 0 := fun N => by
    rw [hterm]; split_ifs <;> simp
  have hR := hasSum_ite_dvd_pow (K := ℝ) (x := ‖q‖) (by simpa using hq) hb
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hnorm] using hR.summable
  · simpa only [hterm] using hasSum_ite_dvd_pow hq hb
  · simpa only [hnorm] using hR.tsum_eq.le

private theorem prod_Icc_one_eq_prod_range (f : ℕ → ℂ) (n : ℕ) :
    ∏ r ∈ Icc 1 n, f r = ∏ l ∈ range n, f (l + 1) := by
  rw [range_eq_Ico, prod_Ico_add' f 0 n 1]
  rfl

/-- The `n`-th term `q^{n²} (q;q)_n/(q^d;q^d)_n` of `primitiveRankSeries m`, over `ℂ`. -/
private def primitiveTerm (m n : ℕ) : PowerSeries ℂ :=
  map (Int.castRingHom ℂ)
    (X ^ (n ^ 2) * formalQPoch 1 n * invOfUnit (formalQPoch (2 * m + 1) n) 1)

private theorem primitiveTerm_eq (m n : ℕ) :
    primitiveTerm m n = X ^ (n ^ 2) * (∏ r ∈ Icc 1 n, (1 - X ^ r)) *
      ∏ r ∈ Icc 1 n, geomSeries ((2 * m + 1) * r) := by
  have hQ := formalQPoch_mul_inv m n
  have hmQ : map (Int.castRingHom ℂ) (formalQPoch (2 * m + 1) n) =
      ∏ r ∈ Icc 1 n, (1 - X ^ ((2 * m + 1) * r)) := by
    simp [formalQPoch, map_prod]
  have hG : map (Int.castRingHom ℂ) (formalQPoch (2 * m + 1) n) *
      ∏ r ∈ Icc 1 n, geomSeries ((2 * m + 1) * r) = 1 := by
    rw [hmQ, ← prod_mul_distrib]
    exact prod_eq_one fun r hr => one_sub_X_pow_mul_geomSeries (by
      have := (mem_Icc.mp hr).1; nlinarith)
  have hinv : map (Int.castRingHom ℂ) (invOfUnit (formalQPoch (2 * m + 1) n) 1) =
      ∏ r ∈ Icc 1 n, geomSeries ((2 * m + 1) * r) := by
    calc map (Int.castRingHom ℂ) (invOfUnit (formalQPoch (2 * m + 1) n) 1)
        = map (Int.castRingHom ℂ) (invOfUnit (formalQPoch (2 * m + 1) n) 1) *
            (map (Int.castRingHom ℂ) (formalQPoch (2 * m + 1) n) *
              ∏ r ∈ Icc 1 n, geomSeries ((2 * m + 1) * r)) := by rw [hG, mul_one]
      _ = map (Int.castRingHom ℂ) (formalQPoch (2 * m + 1) n *
            invOfUnit (formalQPoch (2 * m + 1) n) 1) *
              ∏ r ∈ Icc 1 n, geomSeries ((2 * m + 1) * r) := by rw [map_mul]; ring
      _ = _ := by rw [hQ, map_one, one_mul]
  rw [primitiveTerm, map_mul, map_mul, hinv, map_pow, map_X]
  simp [formalQPoch, map_prod]

/-- The term `q^{n²} (q;q)_n/(q^d;q^d)_n` converges absolutely, with absolute sum at most
`‖q‖^{n²} (2/(1 - ‖q‖))^n`. -/
private theorem absEval_primitiveTerm (m n : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    AbsEval (primitiveTerm m n) q
      (q ^ (n ^ 2) * qPochhammer q q n / qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) n)
      (‖q‖ ^ (n ^ 2) * (2 * (1 - ‖q‖)⁻¹) ^ n) := by
  have h1 : ∀ r ∈ Icc 1 n, AbsEval (1 - X ^ r) q (1 - q ^ r) (1 + ‖q‖ ^ r) :=
    fun r _ => (AbsEval.one q).sub (AbsEval.X_pow q r)
  have h2 : ∀ r ∈ Icc 1 n, AbsEval (geomSeries ((2 * m + 1) * r)) q
      (1 - q ^ ((2 * m + 1) * r))⁻¹ (1 - ‖q‖ ^ ((2 * m + 1) * r))⁻¹ :=
    fun r hr => AbsEval.geomSeries hq (by have := (mem_Icc.mp hr).1; nlinarith)
  have h := ((AbsEval.X_pow q (n ^ 2)).mul (AbsEval.prod _ h1)).mul (AbsEval.prod _ h2)
  have hv : q ^ (n ^ 2) * qPochhammer q q n / qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) n =
      q ^ (n ^ 2) * (∏ r ∈ Icc 1 n, (1 - q ^ r)) *
        ∏ r ∈ Icc 1 n, (1 - q ^ ((2 * m + 1) * r))⁻¹ := by
    rw [prod_inv_distrib, prod_Icc_one_eq_prod_range, prod_Icc_one_eq_prod_range, qPochhammer,
      qPochhammer, div_eq_mul_inv]
    congr 3 <;> funext l
    · rw [pow_succ']
    · rw [← pow_succ', ← pow_mul]
  rw [primitiveTerm_eq, hv]
  refine h.mono ?_
  have hq0 := norm_nonneg q
  have hpos : 0 < 1 - ‖q‖ := by linarith
  have hA : ∏ r ∈ Icc 1 n, (1 + ‖q‖ ^ r) ≤ 2 ^ n := by
    calc ∏ r ∈ Icc 1 n, (1 + ‖q‖ ^ r) ≤ ∏ _r ∈ Icc 1 n, (2 : ℝ) :=
          prod_le_prod₀ (fun _ _ => by positivity) fun r _ => by
            have := pow_le_one₀ hq0 hq.le (n := r); linarith
      _ = 2 ^ n := by rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  have hB : ∏ r ∈ Icc 1 n, (1 - ‖q‖ ^ ((2 * m + 1) * r))⁻¹ ≤ ((1 - ‖q‖)⁻¹) ^ n := by
    calc ∏ r ∈ Icc 1 n, (1 - ‖q‖ ^ ((2 * m + 1) * r))⁻¹ ≤ ∏ _r ∈ Icc 1 n, (1 - ‖q‖)⁻¹ := by
          refine prod_le_prod₀ (fun r hr => ?_) fun r hr => ?_
          · have := pow_le_one₀ hq0 hq.le (n := (2 * m + 1) * r)
            have : ‖q‖ ^ ((2 * m + 1) * r) < 1 :=
              pow_lt_one₀ hq0 hq (by have := (mem_Icc.mp hr).1; positivity)
            exact inv_nonneg.mpr (by linarith)
          · have hle : ‖q‖ ^ ((2 * m + 1) * r) ≤ ‖q‖ :=
              pow_le_of_le_one hq0 hq.le (by have := (mem_Icc.mp hr).1; positivity)
            exact inv_anti₀ hpos (by linarith)
      _ = ((1 - ‖q‖)⁻¹) ^ n := by rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [mul_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul hA hB ?_ (by positivity)) (by positivity)
  exact prod_nonneg fun r hr => inv_nonneg.mpr (by
    have : ‖q‖ ^ ((2 * m + 1) * r) < 1 :=
      pow_lt_one₀ hq0 hq (by have := (mem_Icc.mp hr).1; positivity)
    linarith)

private theorem summable_norm_primitiveTerm (m : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun p : ℕ × ℕ => ‖coeff p.2 (primitiveTerm m p.1) * q ^ p.2‖ := by
  have hV : 1 ≤ 2 * (1 - ‖q‖)⁻¹ := by
    have h0 : 0 < 1 - ‖q‖ := by linarith
    have : 1 ≤ (1 - ‖q‖)⁻¹ := (one_le_inv₀ h0).mpr (by linarith [norm_nonneg q])
    linarith
  refine (summable_prod_of_nonneg fun _ => norm_nonneg _).mpr
    ⟨fun n => (absEval_primitiveTerm m n hq).1, ?_⟩
  have hgs := gaussianSummable_nat (m := 1) le_rfl (norm_nonneg q) hq hV
  simp only [one_mul] at hgs
  exact Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
    (fun n => (absEval_primitiveTerm m n hq).2.2) hgs

private theorem coeff_primitiveTerm_eq_zero (m : ℕ) {n N : ℕ} (h : N < n ^ 2) :
    coeff N (primitiveTerm m n) = 0 := by
  rw [primitiveTerm, mul_assoc, map_mul, map_pow, map_X, coeff_X_pow_mul',
    ite_eq_right (by omega)]

private theorem hasSum_primitiveTerm_fiber (m N : ℕ) (q : ℂ) :
    HasSum (fun n => coeff N (primitiveTerm m n) * q ^ N)
      (((coeff N (primitiveRankSeries m) : ℤ) : ℂ) * q ^ N) := by
  have hc : ((coeff N (primitiveRankSeries m) : ℤ) : ℂ) =
      ∑ n ∈ range (N + 1), coeff N (primitiveTerm m n) := by
    rw [primitiveRankSeries, coeff_mk, Int.cast_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [primitiveTerm, coeff_map]
    rfl
  rw [hc, sum_mul]
  refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
  rw [coeff_primitiveTerm_eq_zero m (by simp only [mem_range, not_lt] at hn; nlinarith), zero_mul]

/-- **The formal series converges to the analytic one** [AOS, §1, (1.3)]: for `d = 2m + 1`, a
primitive `d`-th root of unity `ζ` and `‖q‖ < 1`, the formal power series
`∑_{n ≥ 0} q^{n²} (q;q)_n/(q^d;q^d)_n ∈ ℤ[[q]]` evaluated at `q` sums to `R_m(ζ;q)`. -/
theorem hasSum_coeff_primitiveRankSeries_mul_pow (m : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m + 1)) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun N => ((coeff N (primitiveRankSeries m) : ℤ) : ℂ) * q ^ N)
      (higherDysonSeriesZ m ζ q) := by
  set G : ℕ × ℕ → ℂ := fun p => coeff p.2 (primitiveTerm m p.1) * q ^ p.2
  have hG : HasSum G (∑' p, G p) := (summable_norm_primitiveTerm m hq).of_norm.hasSum
  have hrow := hG.prod_fiberwise fun n => (absEval_primitiveTerm m n hq).2.1
  have hcol := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hG).prod_fiberwise
    fun N => hasSum_primitiveTerm_fiber m N q
  rw [higherDysonSeriesZ_primitive m hζ hq, hrow.tsum_eq]
  exact hcol

/-- The power series `∑_{n ≥ 0} q^{n²} (q;q)_n/(q^d;q^d)_n ∈ ℤ[[q]]` converges absolutely on the
unit disc. -/
theorem summable_norm_coeff_primitiveRankSeries_mul_pow (m : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun N => ‖((coeff N (primitiveRankSeries m) : ℤ) : ℂ) * q ^ N‖ := by
  have hs' := (Equiv.prodComm ℕ ℕ).summable_iff.mpr (summable_norm_primitiveTerm m hq)
  have h := (summable_prod_of_nonneg fun _ => norm_nonneg _).mp hs'
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_) h.2
  rw [← (hasSum_primitiveTerm_fiber m N q).tsum_eq]
  exact norm_tsum_le_tsum_norm (h.1 N)

/-- **The formal higher rank series converges to `R_m(ζ;q)`** [AOS, §1, (1.3)]: for `m ≥ 1`,
`d = 2m + 1`, a primitive `d`-th root of unity `ζ` and `‖q‖ < 1`, the formal series
`R_m(z;q) ∈ ℤ[z, z⁻¹][[q]]` specialized at `z = ζ` and evaluated at `q` sums to `R_m(ζ;q)`. -/
theorem hasSum_coeff_map_zEval_RSeries_mul_pow (m : ℕ) (hm : 1 ≤ m) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun N => coeff N (map (zEval ζ) (RSeries m)) * q ^ N)
      (higherDysonSeriesZ m ζ q) := by
  rw [map_zEval_RSeries_eq_primitiveRankSeries m hm ζ hζ]
  simpa [coeff_map] using hasSum_coeff_primitiveRankSeries_mul_pow m hζ hq

/-- A function summed by an absolutely convergent power series on the unit disc has that power
series as its expansion there. -/
private theorem hasFPowerSeriesOnBall_ofScalars_of_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hs : ∀ q : ℂ, ‖q‖ < 1 → Summable fun N => ‖c N * q ^ N‖)
    (hf : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun N => c N * q ^ N) (f q)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    have := hs r (by simpa using hr1)
    simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using this
  r_pos := zero_lt_one
  hasSum := by
    intro y hy
    have h' : ‖y‖ₑ < 1 := by simpa using hy
    have hy1 : ‖y‖ < 1 := by rwa [← ofReal_norm, ENNReal.ofReal_lt_one] at h'
    have := hf y hy1
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add]
    exact this

private theorem ball_subset_eball : Metric.ball (0 : ℂ) 1 ⊆ Metric.eball 0 1 := fun q hq => by
  have h : ‖q‖ₑ < 1 := by
    rw [← ofReal_norm, ENNReal.ofReal_lt_one]
    simpa using hq
  simpa using h

/-- **`R_m(ζ;·)` is holomorphic on the unit disc with the formal Taylor coefficients**
[AOS, §1, (1.3)]: for `d = 2m + 1` and a primitive `d`-th root of unity `ζ`, the function
`q ↦ R_m(ζ;q)` is given on `‖q‖ < 1` by the power series
`∑_{n ≥ 0} q^{n²} (q;q)_n/(q^d;q^d)_n ∈ ℤ[[q]]`. -/
theorem hasFPowerSeriesOnBall_higherDysonSeriesZ (m : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m + 1)) :
    HasFPowerSeriesOnBall (higherDysonSeriesZ m ζ)
      (FormalMultilinearSeries.ofScalars ℂ fun N => ((coeff N (primitiveRankSeries m) : ℤ) : ℂ))
      0 1 :=
  hasFPowerSeriesOnBall_ofScalars_of_hasSum
    (fun _ hq => summable_norm_coeff_primitiveRankSeries_mul_pow m hq)
    (fun _ hq => hasSum_coeff_primitiveRankSeries_mul_pow m hζ hq)

/-- `R_m(ζ;·)` is holomorphic on the unit disc, for a primitive `(2m+1)`-th root of unity `ζ`. -/
theorem differentiableOn_higherDysonSeriesZ (m : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m + 1)) :
    DifferentiableOn ℂ (higherDysonSeriesZ m ζ) (Metric.ball 0 1) :=
  (hasFPowerSeriesOnBall_higherDysonSeriesZ m hζ).differentiableOn.mono ball_subset_eball

/-- **Theorem 7.1(iii), analytically** [AOS, Theorem 7.1(iii)]: for `d = 2m + 1`, a primitive
`d`-th root of unity `ζ` and `J ≥ 0`, the backward polynomial `P_J ∈ ℤ[q]` of (7.14) satisfies
`R_m(ζ;q) ≡ P_J(q) (mod q^{J+1})` as holomorphic functions on the unit disc:
`R_m(ζ;q) - P_J(q) = q^{J+1} F(q)` with `F` holomorphic on `‖q‖ < 1`. -/
theorem higherDysonSeriesZ_sub_backwardPolynomial (m : ℕ) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m + 1)) (J : ℕ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 1) ∧ ∀ q : ℂ, ‖q‖ < 1 →
      higherDysonSeriesZ m ζ q - Polynomial.aeval q (backwardPolynomial m J) =
        q ^ (J + 1) * F q := by
  set P := backwardPolynomial m J
  set e : ℕ → ℂ := fun N => ((coeff N (primitiveRankSeries m) : ℤ) : ℂ) - (P.coeff N : ℂ)
  have he0 : ∀ N ≤ J, e N = 0 := fun N hN => by
    simp only [e, P, coeff_backwardPolynomial m J hN, sub_self]
  have hdiff : ∀ q : ℂ, ‖q‖ < 1 → (Summable fun N => ‖e N * q ^ N‖) ∧
      HasSum (fun N => e N * q ^ N) (higherDysonSeriesZ m ζ q - Polynomial.aeval q P) := by
    intro q hq
    have hPfin : ∀ N ∉ range (P.natDegree + 1), (P.coeff N : ℂ) * q ^ N = 0 := fun N hN => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hN), Int.cast_zero, zero_mul]
    have hPs : HasSum (fun N => (P.coeff N : ℂ) * q ^ N) (Polynomial.aeval q P) := by
      rw [Polynomial.aeval_eq_sum_range]
      simpa only [zsmul_eq_mul] using hasSum_sum_of_ne_finset_zero hPfin
    have hPn : Summable fun N => ‖(P.coeff N : ℂ) * q ^ N‖ :=
      summable_of_ne_finset_zero (s := range (P.natDegree + 1)) fun N hN => by
        rw [hPfin N hN, norm_zero]
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_)
        ((summable_norm_coeff_primitiveRankSeries_mul_pow m hq).add hPn)
      simp only [e, sub_mul]
      exact norm_sub_le _ _
    · simpa only [e, sub_mul] using (hasSum_coeff_primitiveRankSeries_mul_pow m hζ hq).sub hPs
  have hshift : ∀ q : ℂ, ‖q‖ < 1 → Summable fun N => ‖e (N + (J + 1)) * q ^ N‖ := by
    intro q hq
    set r : ℝ := (1 + ‖q‖) / 2
    have hq0 := norm_nonneg q
    have hr0 : 0 < r := by positivity
    have hr1 : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
      simp only [r]
      linarith
    have hqr : ‖q‖ ≤ r := by simp only [r]; linarith
    have hs := (summable_nat_add_iff (J + 1)).mpr (hdiff r hr1).1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_)
      (hs.div_const (r ^ (J + 1)))
    have hN : ‖e (N + (J + 1)) * (r : ℂ) ^ (N + (J + 1))‖ / r ^ (J + 1) =
        ‖e (N + (J + 1))‖ * r ^ N := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le, pow_add, ← mul_assoc,
        mul_div_cancel_right₀ _ (pow_ne_zero _ hr0.ne')]
    rw [hN, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hqr N) (norm_nonneg _)
  refine ⟨fun q => ∑' N, e (N + (J + 1)) * q ^ N, ?_, fun q hq => ?_⟩
  · exact (hasFPowerSeriesOnBall_ofScalars_of_hasSum (c := fun N => e (N + (J + 1))) hshift
      fun q hq => (hshift q hq).of_norm.hasSum).differentiableOn.mono ball_subset_eball
  · have h1 := (hasSum_nat_add_iff' (J + 1)).mpr (hdiff q hq).2
    rw [sum_eq_zero fun N hN => by rw [he0 N (by simp only [mem_range] at hN; omega), zero_mul],
      sub_zero] at h1
    refine h1.unique ?_
    convert ((hshift q hq).of_norm.hasSum).mul_left (q ^ (J + 1)) using 1
    funext N
    rw [pow_add]
    ring

end HigherDyson3
