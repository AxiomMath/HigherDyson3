/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Definitions

/-!
# Finitely many Dyson symbols of each size

A symbol of size `N` has square at most `N` and all its partitions of size at most `N`;
there are finitely many partitions of size at most `N`, hence finitely many such symbols.

## Main results

* `HigherDyson3.DysonSymbol.finite_size_eq`: for `m ≥ 1`, the set of `m`-Dyson symbols of size `N`
  is finite.
-/

public section

namespace HigherDyson3

/-- The number of parts of a partition is at most its size. -/
private theorem symbolsOfSizeFinite_length_le_size (p : Partition) : p.length ≤ p.size := by
  have h := Multiset.card_nsmul_le_sum (s := p.map ((↑) : ℕ+ → ℕ)) (a := 1)
    (by simpa using fun x _ => x.pos)
  simpa [Partition.length, Partition.size] using h

/-- Each part of a partition is at most its size. -/
private theorem symbolsOfSizeFinite_le_size {p : Partition} {i : ℕ+} (hi : i ∈ p) :
    (i : ℕ) ≤ p.size :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hi)

/-- There are finitely many partitions of size at most `N`. -/
private theorem symbolsOfSizeFinite_partitions (N : ℕ) :
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
    have hjN : (j : ℕ) ≤ N := (symbolsOfSizeFinite_le_size hj).trans hp
    have h1 : Multiset.count (j : ℕ) (Multiset.range (N + 1)) = 1 :=
      Multiset.count_eq_one_of_mem (Multiset.nodup_range _)
        (Multiset.mem_range.2 (Nat.lt_succ_of_le hjN))
    rw [Multiset.count_nsmul, h1, mul_one]
    calc Multiset.count (j : ℕ) (p.map ((↑) : ℕ+ → ℕ))
        ≤ Multiset.card (p.map ((↑) : ℕ+ → ℕ)) := Multiset.count_le_card _ _
      _ = Partition.length p := by simp [Partition.length]
      _ ≤ N := (symbolsOfSizeFinite_length_le_size p).trans hp
  · simp [Multiset.count_eq_zero.2 hi]

/-- **Finitely many symbols of each size**: for `m ≥ 1` and `N ∈ ℕ`, the set of
`m`-Dyson symbols of size `N` is finite. -/
theorem DysonSymbol.finite_size_eq (m : ℕ) (_hm : 1 ≤ m) (N : ℕ) :
    {s : DysonSymbol m | s.size = N}.Finite := by
  let F := {p : Partition | p.size ≤ N}
  have hF : F.Finite := symbolsOfSizeFinite_partitions N
  let f : DysonSymbol m → ℕ × (Fin m → Partition) × (Fin m → Partition) :=
    fun s => (s.n, s.α, s.β)
  have hf : Function.Injective f := by
    rintro ⟨n, α, β, _, _⟩ ⟨n', α', β', _, _⟩ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  refine (((Set.finite_Iic N).prod ((Set.Finite.pi fun _ => hF).prod
    (Set.Finite.pi fun _ => hF))).preimage hf.injOn).subset ?_
  rintro s (hs : s.size = N)
  have hα : ∀ j, (s.α j).size ≤ N := fun j => by
    have := Finset.single_le_sum (f := fun j => (s.α j).size + (s.β j).size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [DysonSymbol.size] at hs
    omega
  have hβ : ∀ j, (s.β j).size ≤ N := fun j => by
    have := Finset.single_le_sum (f := fun j => (s.α j).size + (s.β j).size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [DysonSymbol.size] at hs
    omega
  have hn : s.n ≤ N := by
    simp only [DysonSymbol.size] at hs
    have : s.n ≤ s.n ^ 2 := by nlinarith
    omega
  exact ⟨hn, fun j _ => hα j, fun j _ => hβ j⟩

end HigherDyson3
