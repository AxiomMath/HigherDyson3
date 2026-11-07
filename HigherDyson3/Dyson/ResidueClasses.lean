/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.CombinatorialGenSeries
public import HigherDyson3.Dyson.RootOfUnityCollapse

/-!
# The full rank modulo `d = 2m + 1`

For `N ≥ 0` and `a ∈ ℤ/dℤ`, `N_m(a,d;N)` counts the uncoupled `m`-Dyson symbols of size `N` whose
full rank is congruent to `a` modulo `d = 2m + 1`. When `d` is prime the nonzero residue classes
are equally populated [AOS, Theorem 2.6], and the class sizes are determined by
`U_m(N) = [q^N] R_m(1;q)` and `D_m(N) = [q^N] R_m(ζ_d;q)` [AOS, Corollary 2.7].

The proof follows [AOS, Theorem 2.6] with one simplification: by the collapse at roots of unity,
`F_N(ζ) = [q^N] R_m(ζ;q)` is the `N`-th coefficient `δ_N ∈ ℤ` of
`∑_n q^{n²}(q;q)_n/(q^d;q^d)_n`, which needs no Galois argument. Then `F_N - δ_N ∈ ℤ[X]` vanishes
at `ζ`, so the cyclotomic polynomial `Φ_d = ∑_{a<d} X^a` divides it, and comparing degrees gives
`F_N - δ_N = c_N Φ_d`.

## Main results

* `HigherDyson3.residueCount`: the count `N_m(a,d;N)`.
* `HigherDyson3.residueCount_eq_of_prime`: `N_m(a,d;N) = N_m(b,d;N)` for `1 ≤ a, b ≤ d - 1`.
* `HigherDyson3.coeff_RSeries_primitive_eq_residueCount_sub`:
  `[q^N] R_m(ζ_d;q) = N_m(0,d;N) - N_m(1,d;N)`.
* `HigherDyson3.residueCount_zero_eq` and `HigherDyson3.residueCount_one_eq`: the class sizes in
  terms of `U_m(N)` and `D_m(N)`.
-/

public section

open PowerSeries Finset

namespace HigherDyson3

/-- `N_m(a,d;N)`: the number of uncoupled `m`-Dyson symbols of size `N` whose full rank is
congruent to `a` modulo `d = 2m + 1` (`0` if there are infinitely many). -/
noncomputable def residueCount (m : ℕ) (a : ℤ) (N : ℕ) : ℕ :=
  Nat.card {s : DysonSymbol m // s.size = N ∧ s.fullRank ≡ a [ZMOD (2 * m + 1)]}

/-- `[q^N] R_m(z;q) = ∑_{|Σ| = N} z^{FR_m(Σ)}`, over the finitely many symbols of size `N`. -/
theorem qCoeff_RSeries_eq_sum (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    qCoeff N (RSeries m) =
      ∑ s ∈ (DysonSymbol.finite_size_eq m hm N).toFinset, LaurentPolynomial.T s.fullRank := by
  classical
  refine LaurentPolynomial.ext fun r => ?_
  have h := RSeries_zCoeff_qCoeff m hm N r
  rw [zCoeff] at h
  rw [h, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [LaurentPolynomial.T_apply, sum_boole, rankCount]
  rw [← Nat.card_eq_finsetCard]
  exact_mod_cast Nat.card_congr (Equiv.subtypeEquivRight fun s => by simp [eq_comm])

/-- The residue-class polynomial `F_N(X) = ∑_{a=0}^{d-1} N_m(a,d;N) X^a ∈ ℤ[X]`, `d = 2m + 1`,
of the proof of [AOS, Theorem 2.6]. -/
noncomputable def residuePolynomial (m N : ℕ) : Polynomial ℤ :=
  ∑ a ∈ range (2 * m + 1), Polynomial.C (residueCount m a N : ℤ) * Polynomial.X ^ a

private theorem residuePolynomial_coeff (m N : ℕ) {a : ℕ} (ha : a < 2 * m + 1) :
    (residuePolynomial m N).coeff a = residueCount m a N := by
  simp only [residuePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [sum_ite_eq (range (2 * m + 1)) a, ite_eq_left (mem_range.mpr ha)]

private theorem residuePolynomial_natDegree_le (m N : ℕ) :
    (residuePolynomial m N).natDegree ≤ 2 * m := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp ha; omega)

/-- For `ζ^d = 1`, `ζ^k = ζ^{k mod d}`. -/
private theorem zpow_eq_pow_emod {m : ℕ} (ζ : ℂˣ) (hζ : (ζ : ℂ) ^ (2 * m + 1) = 1) (k : ℤ) :
    ((ζ ^ k : ℂˣ) : ℂ) = (ζ : ℂ) ^ (k % (2 * m + 1 : ℤ)).toNat := by
  have hu : ζ ^ (2 * m + 1) = 1 := Units.ext (by simpa using hζ)
  have hu' : ζ ^ (2 * m + 1 : ℤ) = 1 := by
    rw [show (2 * m + 1 : ℤ) = ((2 * m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hu]
  have hnn : 0 ≤ k % (2 * m + 1 : ℤ) := Int.emod_nonneg _ (by omega)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, k % (2 * m + 1 : ℤ) = t := ⟨_, (Int.toNat_of_nonneg hnn).symm⟩
  rw [ht, Int.toNat_natCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv k (2 * m + 1 : ℤ), ht]
  rw [zpow_add, zpow_mul, hu', one_zpow, mul_one, zpow_natCast, Units.val_pow_eq_pow_val]

/-- `F_N(ζ) = [q^N] R_m(ζ;q)` whenever `ζ^d = 1`. -/
theorem aeval_residuePolynomial (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (ζ : ℂˣ)
    (hζ : (ζ : ℂ) ^ (2 * m + 1) = 1) :
    Polynomial.aeval (ζ : ℂ) (residuePolynomial m N) = coeff N (map (zEval ζ) (RSeries m)) := by
  classical
  set S := (DysonSymbol.finite_size_eq m hm N).toFinset
  set g : DysonSymbol m → ℕ := fun s => (s.fullRank % (2 * m + 1 : ℤ)).toNat
  have hg : ∀ s ∈ S, g s ∈ range (2 * m + 1) := fun s _ => by
    have h1 : s.fullRank % (2 * m + 1 : ℤ) < 2 * m + 1 := Int.emod_lt_of_pos _ (by omega)
    have h2 : 0 ≤ s.fullRank % (2 * m + 1 : ℤ) := Int.emod_nonneg _ (by omega)
    simp only [mem_range, g]
    omega
  have hcount : ∀ a ∈ range (2 * m + 1), (S.filter fun s => g s = a).card = residueCount m a N := by
    intro a ha
    have ha' := mem_range.mp ha
    rw [residueCount, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun s => ?_)
    have h2 : 0 ≤ s.fullRank % (2 * m + 1 : ℤ) := Int.emod_nonneg _ (by omega)
    simp only [mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, g, S, Int.ModEq,
      Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ a) (by omega : (a : ℤ) < 2 * m + 1)]
    omega
  rw [coeff_map, ← qCoeff, qCoeff_RSeries_eq_sum m hm N, map_sum]
  simp only [zEval, LaurentPolynomial.eval₂_T, zpow_eq_pow_emod ζ hζ]
  rw [← sum_fiberwise_of_maps_to hg, residuePolynomial, map_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [sum_eq_card_nsmul (b := (ζ : ℂ) ^ a) fun s hs => by
    rw [← (mem_filter.mp hs).2], hcount a ha]
  simp [nsmul_eq_mul]

/-- At a primitive `d`-th root of unity, `[q^N] R_m(ζ;q)` is the integer
`δ_N = [q^N] ∑_n q^{n²}(q;q)_n/(q^d;q^d)_n`. -/
private theorem coeff_map_zEval_primitive (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    coeff N (map (zEval ζ) (RSeries m)) = (Int.cast (coeff N (primitiveRankSeries m)) : ℂ) := by
  rw [map_zEval_RSeries_eq_primitiveRankSeries m hm ζ hζ, coeff_map]
  rfl

/-- The core of [AOS, Theorem 2.6]: for `d = 2m + 1` prime there is `c_N ∈ ℤ` with
`N_m(a,d;N) = c_N` for `1 ≤ a ≤ d - 1` and `N_m(0,d;N) - δ_N = c_N`. -/
private theorem exists_residueCount_eq (m : ℕ) (hm : 1 ≤ m) (hp : (2 * m + 1).Prime) (N : ℕ)
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    ∃ c : ℤ, (∀ a ∈ Icc 1 (2 * m), (residueCount m a N : ℤ) = c) ∧
      (residueCount m 0 N : ℤ) - coeff N (primitiveRankSeries m) = c := by
  have := Fact.mk hp
  set δ := coeff N (primitiveRankSeries m)
  set G := residuePolynomial m N - Polynomial.C δ
  have hev : Polynomial.aeval (ζ : ℂ) G = 0 := by
    have h1 := aeval_residuePolynomial m hm N ζ hζ.pow_eq_one
    rw [coeff_map_zEval_primitive m hm N ζ hζ] at h1
    simp [G, h1, δ]
  have hdvd : Polynomial.cyclotomic (2 * m + 1) ℤ ∣ G := by
    rw [Polynomial.cyclotomic_eq_minpoly hζ (by omega)]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral (by omega)) hev
  obtain ⟨Q, hQ⟩ := hdvd
  have hdeg : G.natDegree ≤ 2 * m :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (residuePolynomial_natDegree_le m N) (by simp))
  obtain ⟨c, hQC⟩ : ∃ c, Q = Polynomial.C c := by
    refine ⟨Q.coeff 0, ?_⟩
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    refine Polynomial.eq_C_of_natDegree_eq_zero ?_
    rw [hQ, Polynomial.natDegree_mul (Polynomial.cyclotomic_ne_zero _ _) hQ0,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime hp] at hdeg
    omega
  have hcoeff : ∀ a < 2 * m + 1, G.coeff a = c := by
    intro a ha
    rw [hQ, hQC, Polynomial.coeff_mul_C, Polynomial.cyclotomic_prime,
      Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_X_pow]
    rw [sum_ite_eq (range (2 * m + 1)) a, ite_eq_left (mem_range.mpr ha), one_mul]
  refine ⟨c, fun a ha => ?_, ?_⟩
  · have ha' := mem_Icc.mp ha
    have := hcoeff a (by omega)
    rwa [Polynomial.coeff_sub, residuePolynomial_coeff m N (by omega), Polynomial.coeff_C,
      ite_eq_right (by omega), sub_zero] at this
  · have := hcoeff 0 (by omega)
    rwa [Polynomial.coeff_sub, residuePolynomial_coeff m N (by omega), Polynomial.coeff_C,
      ite_eq_left rfl] at this

/-- A primitive `n`-th root of unity in `ℂ`, as a unit. -/
private theorem exists_primitive_unit (n : ℕ) (hn : n ≠ 0) :
    ∃ ζ : ℂˣ, IsPrimitiveRoot (ζ : ℂ) n :=
  ⟨Units.mk0 _ ((Complex.isPrimitiveRoot_exp n hn).ne_zero hn),
    Complex.isPrimitiveRoot_exp n hn⟩

/-- **Equidistribution of the nonzero residue classes** [AOS, Theorem 2.6]: for `m ≥ 1` with
`d = 2m + 1` prime and every `N ≥ 0`, `N_m(1,d;N) = N_m(2,d;N) = ⋯ = N_m(d-1,d;N)`. -/
theorem residueCount_eq_of_prime (m : ℕ) (hm : 1 ≤ m) (hp : (2 * m + 1).Prime) (N : ℕ)
    {a b : ℕ} (ha : a ∈ Icc 1 (2 * m)) (hb : b ∈ Icc 1 (2 * m)) :
    residueCount m a N = residueCount m b N := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit (2 * m + 1) (by omega)
  obtain ⟨c, hc, -⟩ := exists_residueCount_eq m hm hp N ζ hζ
  exact_mod_cast (hc a ha).trans (hc b hb).symm

/-- **The specialized coefficient** [AOS, Theorem 2.6]: for `m ≥ 1` with `d = 2m + 1` prime and a
primitive `d`-th root of unity `ζ`, there are integers `A_m(N)`, `B_m(N)` with
`N_m(0,d;N) = A_m(N)`, `N_m(a,d;N) = B_m(N)` for `1 ≤ a ≤ d - 1`, and
`[q^N] R_m(ζ;q) = A_m(N) - B_m(N)`. -/
theorem exists_residueCount_coeff_RSeries (m : ℕ) (hm : 1 ≤ m) (hp : (2 * m + 1).Prime)
    (N : ℕ) (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    ∃ A B : ℤ, (residueCount m 0 N : ℤ) = A ∧ (∀ a ∈ Icc 1 (2 * m), (residueCount m a N : ℤ) = B) ∧
      coeff N (map (zEval ζ) (RSeries m)) = (A - B : ℂ) := by
  obtain ⟨c, hc, h0⟩ := exists_residueCount_eq m hm hp N ζ hζ
  refine ⟨residueCount m 0 N, c, rfl, hc, ?_⟩
  rw [coeff_map_zEval_primitive m hm N ζ hζ, ← h0]
  push_cast
  ring

/-- [AOS, Theorem 2.6] with `A_m(N) = N_m(0,d;N)` and `B_m(N) = N_m(1,d;N)`:
`[q^N] R_m(ζ;q) = N_m(0,d;N) - N_m(1,d;N)` for `d = 2m + 1` prime and `ζ` a primitive `d`-th root
of unity. -/
theorem coeff_RSeries_primitive_eq_residueCount_sub (m : ℕ) (hm : 1 ≤ m)
    (hp : (2 * m + 1).Prime) (N : ℕ) (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    coeff N (map (zEval ζ) (RSeries m)) = (residueCount m 0 N : ℂ) - residueCount m 1 N := by
  obtain ⟨c, hc, h0⟩ := exists_residueCount_eq m hm hp N ζ hζ
  have h1 := hc 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)
  rw [coeff_map_zEval_primitive m hm N ζ hζ]
  have : (coeff N (primitiveRankSeries m) : ℤ) = residueCount m 0 N - residueCount m 1 N := by
    push_cast at h1 ⊢
    omega
  exact_mod_cast this

/-- **[AOS, Theorem 2.6]**, both claims together: for `m ≥ 1` with `d = 2m + 1` prime, `N ≥ 0`
and a primitive `d`-th root of unity `ζ`, `N_m(1,d;N) = ⋯ = N_m(d-1,d;N)`, and there are integers
`A_m(N) = N_m(0,d;N)` and `B_m(N) = N_m(a,d;N)` (`1 ≤ a ≤ d - 1`) with
`[q^N] R_m(ζ;q) = A_m(N) - B_m(N)`. -/
theorem residueCount_equidistribution (m : ℕ) (hm : 1 ≤ m) (hp : (2 * m + 1).Prime) (N : ℕ)
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    (∀ a ∈ Icc 1 (2 * m), ∀ b ∈ Icc 1 (2 * m), residueCount m a N = residueCount m b N) ∧
    ∃ A B : ℤ, (residueCount m 0 N : ℤ) = A ∧ (∀ a ∈ Icc 1 (2 * m), (residueCount m a N : ℤ) = B) ∧
      coeff N (map (zEval ζ) (RSeries m)) = (A - B : ℂ) :=
  ⟨fun _ ha _ hb => residueCount_eq_of_prime m hm hp N ha hb,
    exists_residueCount_coeff_RSeries m hm hp N ζ hζ⟩

/-- `U_m(N) = ∑_{a=0}^{d-1} N_m(a,d;N)`: `[q^N] R_m(1;q)` counts all symbols of size `N`. -/
private theorem coeff_RSeries_one_eq_sum (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    coeff N (map (zEval 1) (RSeries m)) = ∑ a ∈ range (2 * m + 1), (residueCount m a N : ℂ) := by
  rw [← aeval_residuePolynomial m hm N 1 (by simp), residuePolynomial, map_sum]
  simp

/-- **The class sizes** [AOS, Corollary 2.7]: for `d = 2m + 1` prime, with
`U_m(N) = [q^N] R_m(1;q)` and `D_m(N) = [q^N] R_m(ζ_d;q)`,
`A_m(N) = N_m(0,d;N) = (U_m(N) + (d-1) D_m(N)) / d` and
`B_m(N) = N_m(a,d;N) = (U_m(N) - D_m(N)) / d` for `1 ≤ a ≤ d - 1`. -/
theorem residueCount_eq_div (m : ℕ) (hm : 1 ≤ m) (hp : (2 * m + 1).Prime) (N : ℕ) (ζ : ℂˣ)
    (hζ : IsPrimitiveRoot (ζ : ℂ) (2 * m + 1)) :
    (residueCount m 0 N : ℂ) = (coeff N (map (zEval 1) (RSeries m)) +
        ((2 * m + 1 : ℕ) - 1 : ℂ) * coeff N (map (zEval ζ) (RSeries m))) / (2 * m + 1 : ℕ) ∧
      ∀ a ∈ Icc 1 (2 * m), (residueCount m a N : ℂ) = (coeff N (map (zEval 1) (RSeries m)) -
        coeff N (map (zEval ζ) (RSeries m))) / (2 * m + 1 : ℕ) := by
  obtain ⟨c, hc, h0⟩ := exists_residueCount_eq m hm hp N ζ hζ
  have hU : coeff N (map (zEval 1) (RSeries m)) = residueCount m 0 N + 2 * m * c := by
    rw [coeff_RSeries_one_eq_sum m hm N, sum_range_succ']
    rw [sum_congr rfl fun a ha => show (residueCount m ((a + 1 : ℕ) : ℤ) N : ℂ) = c by
      have := hc (a + 1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp ha; omega⟩)
      exact_mod_cast this]
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]
    ring
  have hD : coeff N (map (zEval ζ) (RSeries m)) = residueCount m 0 N - c := by
    rw [coeff_map_zEval_primitive m hm N ζ hζ, ← h0]
    push_cast
    ring
  have hd : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * m + 1 ≠ 0)
  refine ⟨?_, fun a ha => ?_⟩
  · rw [eq_div_iff hd, hU, hD]
    push_cast
    ring
  · rw [eq_div_iff hd, hU, hD, show (residueCount m a N : ℂ) = c by exact_mod_cast hc a ha]
    push_cast
    ring

end HigherDyson3
