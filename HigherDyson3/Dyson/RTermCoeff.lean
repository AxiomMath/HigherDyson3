/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Dyson.RTermExpand
public import HigherDyson3.Dyson.SymbolsOfSizeFinite

/-!
# The coefficients of the terms of the higher rank series

For `m ≥ 1`, `n, N ∈ ℕ` and `r ∈ ℤ`, the coefficient `[z^r] [q^N] 𝒯_{m,n}` is the number of
`m`-Dyson symbols `Σ` with `n(Σ) = n`, `|Σ| = N` and `FR_m(Σ) = r`.

By the expansion `𝒯_{m,n} = q^{n²} ∏_{j=1}^m Φ_{z^j,n} Φ_{z^{-j},n}`, the coefficient
`[q^N] 𝒯_{m,n}` vanishes for `N < n²` and is otherwise `[q^{N-n²}]` of the product of the `2m`
partition series. The coefficient `[q^M]` of a finite product `∏_i Φ_{c_i,n}` is the sum,
over the tuples `(λ_i)_i` of partitions with parts at most `n` and total size `M`, of
`∏_i c_i^{ℓ(λ_i)}`. For the `2m` series at hand these tuples are exactly the Dyson symbols
with square `n` and size `N`, and the monomial attached to such a symbol is `z^{FR_m(Σ)}`.

## Main results

* `HigherDyson3.RTerm_zCoeff_qCoeff`: `[z^r] [q^N] 𝒯_{m,n}` is the number of `m`-Dyson symbols
  `Σ` with `n(Σ) = n`, `|Σ| = N` and `FR_m(Σ) = r`.

## Implementation notes

The count is the cardinality `Nat.card` of the subtype of such symbols, cast to `ℤ`; the
subtype is finite by `HigherDyson3.DysonSymbol.finite_size_eq`. The pair `(α j, β j)` of a
symbol, `j : Fin m`, carries the weight `j + 1`, so the product over `j ∈ [1, m]` is reindexed
by `Fin m`.
-/

public section

open PowerSeries Finset

namespace HigherDyson3

/-- The partitions with parts at most `n` and size `k` form a finite set. -/
private theorem RTermCoeff_finite (n k : ℕ) :
    {p : Partition | p ∈ boundedPartitions n ∧ p.size = k}.Finite := by
  refine ((DysonSymbol.finite_size_eq 1 le_rfl (n ^ 2 + k)).image fun s => s.α 0).subset ?_
  rintro p ⟨hp, hk⟩
  refine ⟨⟨n, fun _ => p, fun _ => 0, fun _ => hp, fun _ => by simp [boundedPartitions]⟩,
    ?_, rfl⟩
  simp only [DysonSymbol.size, Partition.size] at hk ⊢
  simp [hk]

/-- The finset of partitions with parts at most `n` and size `k`. -/
private noncomputable def rTermCoeffParts (n k : ℕ) : Finset Partition :=
  (RTermCoeff_finite n k).toFinset

private theorem RTermCoeff_mem_parts {n k : ℕ} {p : Partition} :
    p ∈ rTermCoeffParts n k ↔ p ∈ boundedPartitions n ∧ p.size = k := by
  simp [rTermCoeffParts]

private theorem RTermCoeff_coeff_partitionSeries (c : LaurentRing) (n k : ℕ) :
    coeff k (partitionSeries c n) = ∑ p ∈ rTermCoeffParts n k, c ^ p.length := by
  rw [partitionSeries, coeff_mk]
  exact finsum_mem_eq_finite_toFinset_sum _ (RTermCoeff_finite n k)

/-- The finset of tuples `(λ_i)_{i ∈ ι}` of partitions with parts at most `n` and total
size `M`. -/
private noncomputable def rTermCoeffTuples (ι : Type*) [Fintype ι] [DecidableEq ι]
    (n M : ℕ) : Finset (ι → Partition) :=
  (finsuppAntidiag (univ : Finset ι) M).biUnion fun l =>
    Fintype.piFinset fun i => rTermCoeffParts n (l i)

private theorem RTermCoeff_mem_tuples {ι : Type*} [Fintype ι] [DecidableEq ι] {n M : ℕ}
    {f : ι → Partition} :
    f ∈ rTermCoeffTuples ι n M ↔ (∀ i, f i ∈ boundedPartitions n) ∧ ∑ i, (f i).size = M := by
  simp only [rTermCoeffTuples, mem_biUnion, mem_finsuppAntidiag, Fintype.mem_piFinset,
    RTermCoeff_mem_parts]
  constructor
  · rintro ⟨l, ⟨hl, -⟩, hf⟩
    exact ⟨fun i => (hf i).1, hl ▸ sum_congr rfl fun i _ => (hf i).2⟩
  · rintro ⟨hb, hs⟩
    refine ⟨Finsupp.equivFunOnFinite.symm fun i => (f i).size,
      ⟨by simpa using hs, fun i _ => mem_univ i⟩, fun i => ⟨hb i, by simp⟩⟩

/-- The coefficient `[q^M]` of a finite product of partition series `∏_i Φ_{c_i,n}`. -/
private theorem RTermCoeff_coeff_prod (ι : Type*) [Fintype ι] [DecidableEq ι]
    (c : ι → LaurentRing) (n M : ℕ) :
    coeff M (∏ i, partitionSeries (c i) n) =
      ∑ f ∈ rTermCoeffTuples ι n M, ∏ i, c i ^ (f i).length := by
  rw [coeff_prod, rTermCoeffTuples, sum_biUnion]
  · refine sum_congr rfl fun l _ => ?_
    simp_rw [RTermCoeff_coeff_partitionSeries]
    exact prod_univ_sum _ _
  · intro l₁ _ l₂ _ hne
    rw [Function.onFun, disjoint_left]
    intro f h1 h2
    simp only [Fintype.mem_piFinset, RTermCoeff_mem_parts] at h1 h2
    exact hne (Finsupp.ext fun i => (h1 i).2.symm.trans (h2 i).2)

private theorem RTermCoeff_prod_T {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, (LaurentPolynomial.T (a i) : LaurentRing) = LaurentPolynomial.T (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [prod_insert hx, sum_insert hx, ih, LaurentPolynomial.T_add]

/-- The weight `j + 1` of `α j` and `-(j + 1)` of `β j`. -/
private abbrev rTermCoeffWeight (m : ℕ) : Fin m ⊕ Fin m → ℤ :=
  Sum.elim (fun j => (j : ℤ) + 1) (fun j => -((j : ℤ) + 1))

private theorem RTermCoeff_prod_eq (m n : ℕ) :
    ∏ j ∈ Icc 1 m, partitionSeries (LaurentPolynomial.T (j : ℤ)) n *
      partitionSeries (LaurentPolynomial.T (-(j : ℤ))) n =
      ∏ i, partitionSeries (LaurentPolynomial.T (rTermCoeffWeight m i)) n := by
  have hreindex : ∀ g : ℕ → PowerSeries LaurentRing,
      ∏ j ∈ Icc 1 m, g j = ∏ j : Fin m, g (j + 1) := by
    intro g
    rw [Fin.prod_univ_eq_prod_range (fun j => g (j + 1)), range_eq_Ico, prod_Ico_add']
    rfl
  rw [hreindex, Fintype.prod_sum_type, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  simp only [rTermCoeffWeight, Sum.elim_inl, Sum.elim_inr]
  push_cast
  rfl

private theorem RTermCoeff_sum_size {m : ℕ} (α β : Fin m → Partition) :
    ∑ i, (Sum.elim α β i).size = ∑ j, ((α j).size + (β j).size) := by
  rw [Fintype.sum_sum_type, sum_add_distrib]
  rfl

private theorem RTermCoeff_sum_rank {m : ℕ} (α β : Fin m → Partition) :
    ∑ i, ((Sum.elim α β i).length : ℤ) * rTermCoeffWeight m i =
      ∑ j : Fin m, ((j : ℤ) + 1) * (((α j).length : ℤ) - (β j).length) := by
  rw [Fintype.sum_sum_type, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [rTermCoeffWeight, Sum.elim_inl, Sum.elim_inr]
  ring

/-- For `n² ≤ N`, the Dyson symbols with square `n`, size `N` and full rank `r` are in
bijection with the tuples of `2m` partitions with parts at most `n`, total size `N - n²` and
weighted length `r`. -/
private theorem RTermCoeff_card_eq {m n N : ℕ} (r : ℤ) (hN : n ^ 2 ≤ N) :
    Nat.card ((rTermCoeffTuples (Fin m ⊕ Fin m) n (N - n ^ 2)).filter
        fun f => ∑ i, ((f i).length : ℤ) * rTermCoeffWeight m i = r) =
      Nat.card {s : DysonSymbol m // s.n = n ∧ s.size = N ∧ s.fullRank = r} := by
  have hfe : ∀ f : Fin m ⊕ Fin m → Partition,
      Sum.elim (fun j => f (Sum.inl j)) (fun j => f (Sum.inr j)) = f :=
    fun f => funext fun i => by rcases i with j | j <;> rfl
  have hto : ∀ s : {s : DysonSymbol m // s.n = n ∧ s.size = N ∧ s.fullRank = r},
      Sum.elim s.1.α s.1.β ∈ (rTermCoeffTuples (Fin m ⊕ Fin m) n (N - n ^ 2)).filter
        fun f => ∑ i, ((f i).length : ℤ) * rTermCoeffWeight m i = r := by
    rintro ⟨s, hn, hs, hr⟩
    rw [mem_filter, RTermCoeff_mem_tuples, RTermCoeff_sum_rank]
    refine ⟨⟨fun i => ?_, ?_⟩, hr⟩
    · rcases i with j | j
      · exact hn ▸ s.α_mem j
      · exact hn ▸ s.β_mem j
    · rw [RTermCoeff_sum_size]
      simp only [DysonSymbol.size, hn] at hs
      change ∑ j, ((s.α j).size + (s.β j).size) = N - n ^ 2
      omega
  have hinv : ∀ f ∈ (rTermCoeffTuples (Fin m ⊕ Fin m) n (N - n ^ 2)).filter
      (fun f => ∑ i, ((f i).length : ℤ) * rTermCoeffWeight m i = r),
      (∀ i, f i ∈ boundedPartitions n) ∧
        n ^ 2 + ∑ j, ((f (Sum.inl j)).size + (f (Sum.inr j)).size) = N ∧
        ∑ j : Fin m, ((j : ℤ) + 1) *
          (((f (Sum.inl j)).length : ℤ) - (f (Sum.inr j)).length) = r := by
    intro f hf
    obtain ⟨hf, hr⟩ := mem_filter.1 hf
    obtain ⟨hb, hs⟩ := RTermCoeff_mem_tuples.1 hf
    rw [← hfe f, RTermCoeff_sum_size] at hs
    rw [← hfe f, RTermCoeff_sum_rank] at hr
    exact ⟨hb, by omega, hr⟩
  refine (Nat.card_congr
    { toFun := fun s => ⟨Sum.elim s.1.α s.1.β, hto s⟩
      invFun := fun f => ⟨⟨n, fun j => f.1 (Sum.inl j), fun j => f.1 (Sum.inr j),
        fun j => (hinv f.1 f.2).1 _, fun j => (hinv f.1 f.2).1 _⟩,
        rfl, (hinv f.1 f.2).2.1, (hinv f.1 f.2).2.2⟩
      left_inv := ?_
      right_inv := ?_ }).symm
  · rintro ⟨⟨n', α, β, hα, hβ⟩, rfl, hs, hr⟩
    rfl
  · rintro ⟨f, hf⟩
    exact Subtype.ext (hfe f)

/-- **Coefficients of `𝒯_{m,n}`**: for `m ≥ 1`, `[z^r] [q^N] 𝒯_{m,n}` is the number of
`m`-Dyson symbols `Σ` with `n(Σ) = n`, `|Σ| = N` and `FR_m(Σ) = r`. -/
theorem RTerm_zCoeff_qCoeff (m : ℕ) (_hm : 1 ≤ m) (n N : ℕ) (r : ℤ) :
    zCoeff r (qCoeff N (RTerm m n)) =
      (Nat.card {s : DysonSymbol m // s.n = n ∧ s.size = N ∧ s.fullRank = r} : ℤ) := by
  classical
  have hmon : ∀ f : Fin m ⊕ Fin m → Partition,
      ∏ i, (LaurentPolynomial.T (rTermCoeffWeight m i) : LaurentRing) ^ (f i).length =
        LaurentPolynomial.T (∑ i, ((f i).length : ℤ) * rTermCoeffWeight m i) := by
    intro f
    simp_rw [LaurentPolynomial.T_pow]
    exact RTermCoeff_prod_T _ _
  rw [qCoeff, RTerm_eq, RTermCoeff_prod_eq, coeff_X_pow_mul']
  split_ifs with hN
  · rw [RTermCoeff_coeff_prod]
    simp_rw [hmon]
    simp only [zCoeff]
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [LaurentPolynomial.T_apply, sum_boole]
    rw [← Nat.card_eq_finsetCard]
    exact_mod_cast RTermCoeff_card_eq r hN
  · have : IsEmpty {s : DysonSymbol m // s.n = n ∧ s.size = N ∧ s.fullRank = r} :=
      ⟨fun ⟨s, hn, hs, _⟩ => hN (hs ▸ hn ▸ Nat.le_add_right _ _)⟩
    simp [zCoeff]

end HigherDyson3
