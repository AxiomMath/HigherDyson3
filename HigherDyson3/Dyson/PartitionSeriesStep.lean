/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Adding the part size `n` to the partition series

`(1 - c q^n) Φ_{c,n} = Φ_{c,n-1}`: the partitions of `N` with parts at most `n` and some
part equal to `n` correspond, by removing one part `n`, to the partitions of `N - n` with
parts at most `n`.
-/

public section

open PowerSeries

namespace HigherDyson3

/-- Each part of a partition is at most its size. -/
private theorem partitionSeriesStep_le_size {p : Partition} {i : ℕ+} (hi : i ∈ p) :
    (i : ℕ) ≤ p.size :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hi)

private theorem partitionSeriesStep_size_cons (a : ℕ+) (p : Partition) :
    Partition.size (a ::ₘ p) = a + p.size := by
  simp [Partition.size]

/-- There are finitely many partitions of size at most `N`. -/
private theorem partitionSeriesStep_finite (N : ℕ) :
    {p : Partition | p.size ≤ N}.Finite := by
  let M : Multiset ℕ := N • Multiset.range (N + 1)
  have hM : {q : Multiset ℕ | q ≤ M}.Finite :=
    (Multiset.powerset M).toFinset.finite_toSet.subset fun q hq => by simpa using hq
  refine (hM.preimage (Multiset.map_injective PNat.coe_injective).injOn).subset ?_
  intro p hp
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hp ⊢
  rw [Multiset.le_iff_count]
  intro i
  by_cases hi : i ∈ p.map ((↑) : ℕ+ → ℕ)
  · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hi
    rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem (Multiset.nodup_range _)
      (Multiset.mem_range.2 (Nat.lt_succ_of_le ((partitionSeriesStep_le_size hj).trans hp))),
      mul_one]
    calc Multiset.count (j : ℕ) (p.map ((↑) : ℕ+ → ℕ))
        ≤ Multiset.card (p.map ((↑) : ℕ+ → ℕ)) := Multiset.count_le_card _ _
      _ ≤ N := by
        simpa [Partition.size] using
          (Multiset.card_nsmul_le_sum (s := p.map ((↑) : ℕ+ → ℕ)) (a := 1)
            (by simpa using fun x _ => x.pos)).trans hp
  · simp [Multiset.count_eq_zero.2 hi]

/-- The index set `{λ ∈ 𝒫_{≤n} : |λ| = N}` of the coefficient `[q^N] Φ_{c,n}`. -/
private abbrev partitionSeriesStep_index (n N : ℕ) : Set Partition :=
  {p | p ∈ boundedPartitions n ∧ p.size = N}

private theorem partitionSeriesStep_index_finite (n N : ℕ) :
    (partitionSeriesStep_index n N).Finite :=
  (partitionSeriesStep_finite N).subset fun _ hp => hp.2.le

private theorem partitionSeriesStep_coeff (c : LaurentRing) (n N : ℕ) :
    coeff N (partitionSeries c n) =
      ∑ᶠ p ∈ partitionSeriesStep_index n N, c ^ p.length := by
  simp only [partitionSeries, coeff_mk]
  rfl

/-- Partitions with parts at most `k + 1` split by whether the part `P = k + 1` occurs. -/
private theorem partitionSeriesStep_index_succ {k N : ℕ} {P : ℕ+} (hP : (P : ℕ) = k + 1) :
    partitionSeriesStep_index (k + 1) N =
      partitionSeriesStep_index k N ∪ {p | p ∈ partitionSeriesStep_index (k + 1) N ∧ P ∈ p} := by
  ext p
  simp only [Set.mem_union, Set.mem_ofPred_eq, boundedPartitions]
  constructor
  · rintro ⟨hb, hs⟩
    by_cases hp : P ∈ p
    · exact Or.inr ⟨⟨hb, hs⟩, hp⟩
    · refine Or.inl ⟨fun i hi => ?_, hs⟩
      have := hb i hi
      have hne : (i : ℕ) ≠ k + 1 := fun h => hp (by rwa [PNat.eq (h.trans hP.symm)] at hi)
      omega
  · rintro (⟨hb, hs⟩ | ⟨h, _⟩)
    · exact ⟨fun i hi => (hb i hi).trans k.le_succ, hs⟩
    · exact h

private theorem partitionSeriesStep_disjoint {k N : ℕ} {P : ℕ+} (hP : (P : ℕ) = k + 1) :
    Disjoint (partitionSeriesStep_index k N)
      {p | p ∈ partitionSeriesStep_index (k + 1) N ∧ P ∈ p} := by
  rw [Set.disjoint_left]
  rintro p ⟨hb, _⟩ ⟨_, hp⟩
  have : (P : ℕ) ≤ k := hb P hp
  omega

/-- Removing one part `P = k + 1` identifies the partitions containing it with the partitions
of `N - (k + 1)`. -/
private theorem partitionSeriesStep_eq_image {k N : ℕ} {P : ℕ+} (hP : (P : ℕ) = k + 1)
    (hN : k + 1 ≤ N) :
    {p | p ∈ partitionSeriesStep_index (k + 1) N ∧ P ∈ p} =
      (P ::ₘ ·) '' partitionSeriesStep_index (k + 1) (N - (k + 1)) := by
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq, boundedPartitions]
  constructor
  · rintro ⟨⟨hb, hs⟩, hp⟩
    refine ⟨p.erase P, ⟨fun i hi => hb i (Multiset.mem_of_mem_erase hi), ?_⟩,
      Multiset.cons_erase hp⟩
    have h2 := partitionSeriesStep_size_cons P (p.erase P)
    rw [Multiset.cons_erase hp] at h2
    omega
  · rintro ⟨q, ⟨hb, hs⟩, rfl⟩
    refine ⟨⟨fun i hi => ?_, ?_⟩, Multiset.mem_cons_self _ _⟩
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · exact hP.le
      · exact hb i hi
    · rw [partitionSeriesStep_size_cons]
      omega

private theorem partitionSeriesStep_eq_empty {k N : ℕ} {P : ℕ+} (hP : (P : ℕ) = k + 1)
    (hN : ¬k + 1 ≤ N) :
    {p | p ∈ partitionSeriesStep_index (k + 1) N ∧ P ∈ p} = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨⟨_, hs⟩, hp⟩ =>
    hN (by have := partitionSeriesStep_le_size hp; omega)

/-- **Adding the part size `n`**: `(1 - c q^n) Φ_{c,n} = Φ_{c,n-1}` for `n ≥ 1`. -/
theorem partitionSeries_step (c : LaurentRing) (n : ℕ) (hn : 1 ≤ n) :
    (1 - C c * X ^ n) * partitionSeries c n = partitionSeries c (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set P : ℕ+ := ⟨k + 1, k.succ_pos⟩
  have hP : (P : ℕ) = k + 1 := rfl
  refine PowerSeries.ext fun N => ?_
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    partitionSeriesStep_coeff, partitionSeriesStep_coeff, partitionSeriesStep_coeff,
    partitionSeriesStep_index_succ hP, finsum_mem_union (partitionSeriesStep_disjoint hP)
      (partitionSeriesStep_index_finite k N)
      ((partitionSeriesStep_index_finite (k + 1) N).subset fun _ h => h.1)]
  suffices hT : ∑ᶠ p ∈ {p | p ∈ partitionSeriesStep_index (k + 1) N ∧ P ∈ p}, c ^ p.length =
      c * (if k + 1 ≤ N then
        ∑ᶠ p ∈ partitionSeriesStep_index (k + 1) (N - (k + 1)), c ^ p.length else 0) by
    rw [hT, add_sub_cancel_right]
  split_ifs with hN
  · rw [partitionSeriesStep_eq_image hP hN,
      finsum_mem_image fun _ _ _ _ h => (Multiset.cons_inj_right P).1 h,
      mul_finsum_mem' _ _ (partitionSeriesStep_index_finite _ _)]
    refine finsum_mem_congr rfl fun q _ => ?_
    simp [Partition.length, pow_succ']
  · rw [partitionSeriesStep_eq_empty hP hN, finsum_mem_empty, mul_zero]

end HigherDyson3
