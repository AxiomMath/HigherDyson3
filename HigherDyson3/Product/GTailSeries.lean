/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Product.GMultipliable

/-!
# The tails `g_{k,1}` as partition generating functions

For `d = 2m + 1`, let `𝒫_{d,k}` be the set of partitions whose parts exceed `k` and in which each
part occurs at most `d - 1` times. By the factorization
`g_{k,1}(q) = ∏_{r ≥ 1} (1 + q^{k+r} + ⋯ + q^{(d-1)(k+r)})`, `g_{k,1}` is the generating function
of `𝒫_{d,k}` [AOS, §6, after Proposition 6.2].

The partial product over `r ≤ R` is the generating function of the partitions in `𝒫_{d,k}` with
parts at most `k + R`, which are in bijection with the multiplicity vectors `Fin R → Fin d`. The
partial products at `|q|` are increasing and bounded by `g_{k,1}(|q|)`, which gives absolute
convergence of `∑_{λ ∈ 𝒫_{d,k}} q^{|λ|}`, and the sums over the exhausting finite sets converge to
the product.

## Main results

* `HigherDyson3.restrictedPartitions`: the set `𝒫_{d,k}`.
* `HigherDyson3.restrictedPartitionCount`: the number of partitions of `N` in `𝒫_{d,k}`.
* `HigherDyson3.hasSum_restrictedPartitions`: `g_{k,1}(q) = ∑_{λ ∈ 𝒫_{d,k}} q^{|λ|}`.
* `HigherDyson3.hasSum_restrictedPartitionCount`: `g_{k,1}(q) = ∑_N #{λ ∈ 𝒫_{d,k} : |λ| = N} q^N`.
-/

public section

open Finset Filter Topology

namespace HigherDyson3

/-- The set `𝒫_{d,k}`, `d = 2m + 1`, of partitions whose parts exceed `k` and in which each part
occurs at most `d - 1 = 2m` times [AOS, §6]. -/
def restrictedPartitions (m k : ℕ) : Set Partition :=
  {p | ∀ i ∈ p, k < (i : ℕ) ∧ p.count i ≤ 2 * m}

theorem mem_restrictedPartitions {m k : ℕ} {p : Partition} :
    p ∈ restrictedPartitions m k ↔ ∀ i ∈ p, k < (i : ℕ) ∧ p.count i ≤ 2 * m := Iff.rfl

/-- The number of partitions of `N` in `𝒫_{2m+1,k}` (`0` if there are infinitely many). -/
noncomputable def restrictedPartitionCount (m k N : ℕ) : ℕ :=
  Nat.card {p : Partition // p ∈ restrictedPartitions m k ∧ p.size = N}

/-- The part `k + r + 1`. -/
private def shiftedPart (k r : ℕ) : ℕ+ := ⟨k + r + 1, by omega⟩

private theorem shiftedPart_inj {k r r' : ℕ} : shiftedPart k r = shiftedPart k r' ↔ r = r' := by
  constructor
  · intro h
    have := congrArg PNat.val h
    simp only [shiftedPart, PNat.mk_coe] at this
    omega
  · rintro rfl
    rfl

/-- The partition with the part `k + r + 1` occurring `μ r` times, `r < R`. -/
private def partitionOfMult (m k R : ℕ) (μ : Fin R → Fin (2 * m + 1)) : Partition :=
  ∑ r : Fin R, (μ r : ℕ) • ({shiftedPart k r} : Multiset ℕ+)

private theorem count_partitionOfMult {m k R : ℕ} (μ : Fin R → Fin (2 * m + 1)) (i : ℕ+) :
    (partitionOfMult m k R μ).count i =
      ∑ r : Fin R, if i = shiftedPart k r then (μ r : ℕ) else 0 := by
  simp only [partitionOfMult, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]
  exact sum_congr rfl fun r _ => by split_ifs <;> simp

private theorem count_partitionOfMult_shiftedPart {m k R : ℕ} (μ : Fin R → Fin (2 * m + 1))
    (r : Fin R) : (partitionOfMult m k R μ).count (shiftedPart k r) = μ r := by
  rw [count_partitionOfMult, sum_eq_single r (fun r' _ h => by
    rw [ite_eq_right (fun h' => absurd (Fin.ext (shiftedPart_inj.mp h').symm) h)]) (by simp)]
  simp

/-- The size of a partition, as an additive map. -/
private def sizeHom : Partition →+ ℕ where
  toFun := Partition.size
  map_zero' := by simp [Partition.size]
  map_add' p p' := by simp [Partition.size, Multiset.map_add]

private theorem size_partitionOfMult {m k R : ℕ} (μ : Fin R → Fin (2 * m + 1)) :
    (partitionOfMult m k R μ).size = ∑ r : Fin R, (k + r + 1) * (μ r : ℕ) := by
  change sizeHom (partitionOfMult m k R μ) = _
  rw [partitionOfMult, map_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [map_nsmul, smul_eq_mul, mul_comm]
  change Partition.size {shiftedPart k r} * _ = _
  simp only [Partition.size, Multiset.map_singleton, Multiset.sum_singleton]
  rfl

private theorem le_size_of_mem {p : Partition} {i : ℕ+} (hi : i ∈ p) : (i : ℕ) ≤ p.size :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hi)

private theorem partitionOfMult_mem {m k R : ℕ} (μ : Fin R → Fin (2 * m + 1)) :
    partitionOfMult m k R μ ∈ restrictedPartitions m k ∧
      ∀ i ∈ partitionOfMult m k R μ, (i : ℕ) ≤ k + R := by
  have key : ∀ i ∈ partitionOfMult m k R μ, ∃ r : Fin R, i = shiftedPart k r := by
    intro i hi
    by_contra h
    push Not at h
    rw [← Multiset.count_ne_zero, count_partitionOfMult] at hi
    exact hi (sum_eq_zero fun r _ => ite_eq_right (h r))
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;> obtain ⟨r, rfl⟩ := key i hi
  · refine ⟨by simp [shiftedPart], ?_⟩
    rw [count_partitionOfMult_shiftedPart]
    exact Nat.lt_succ_iff.mp (μ r).2
  · have := r.2
    simp only [shiftedPart, PNat.mk_coe]
    omega

private theorem partitionOfMult_injective (m k R : ℕ) :
    Function.Injective (partitionOfMult m k R) := by
  intro μ μ' h
  funext r
  have := congrArg (fun p => Multiset.count (shiftedPart k r) p) h
  simp only [count_partitionOfMult_shiftedPart] at this
  exact Fin.ext this

private theorem exists_partitionOfMult {m k R : ℕ} {p : Partition}
    (hp : p ∈ restrictedPartitions m k) (hR : ∀ i ∈ p, (i : ℕ) ≤ k + R) :
    ∃ μ, partitionOfMult m k R μ = p := by
  refine ⟨fun r => ⟨p.count (shiftedPart k r), ?_⟩, ?_⟩
  · by_cases h : shiftedPart k r ∈ p
    · exact Nat.lt_succ_of_le (hp _ h).2
    · rw [Multiset.count_eq_zero_of_notMem h]; omega
  refine Multiset.ext.mpr fun i => ?_
  rw [count_partitionOfMult]
  by_cases h : ∃ r : Fin R, i = shiftedPart k r
  · obtain ⟨r, rfl⟩ := h
    rw [sum_eq_single r (fun r' _ h => by
      rw [ite_eq_right (fun h' => absurd (Fin.ext (shiftedPart_inj.mp h').symm) h)]) (by simp)]
    simp
  · push Not at h
    rw [sum_eq_zero fun r _ => ite_eq_right (h r), eq_comm, Multiset.count_eq_zero]
    intro hi
    have h1 := (hp i hi).1
    have h2 := hR i hi
    exact h ⟨(i : ℕ) - k - 1, by omega⟩ (PNat.eq (by simp [shiftedPart]; omega))

/-- The finite set of partitions in `𝒫_{2m+1,k}` with parts at most `k + R`. -/
private noncomputable def boundedRestricted (m k R : ℕ) : Finset Partition :=
  univ.image (partitionOfMult m k R)

private theorem mem_boundedRestricted {m k R : ℕ} {p : Partition} :
    p ∈ boundedRestricted m k R ↔ p ∈ restrictedPartitions m k ∧ ∀ i ∈ p, (i : ℕ) ≤ k + R := by
  rw [boundedRestricted, mem_image]
  constructor
  · rintro ⟨μ, -, rfl⟩
    exact partitionOfMult_mem μ
  · rintro ⟨hp, hR⟩
    obtain ⟨μ, rfl⟩ := exists_partitionOfMult hp hR
    exact ⟨μ, mem_univ _, rfl⟩

private theorem boundedRestricted_mono (m k : ℕ) : Monotone (boundedRestricted m k) :=
  fun _ _ h _ hp => mem_boundedRestricted.mpr
    ⟨(mem_boundedRestricted.mp hp).1, fun i hi => ((mem_boundedRestricted.mp hp).2 i hi).trans
      (by omega)⟩

/-- The partial product `∏_{r < R} P_d(q^{k+r+1})` is the generating function of the partitions
in `𝒫_{d,k}` with parts at most `k + R`. -/
private theorem prod_range_cyclotomicSum (m k R : ℕ) (q : ℂ) :
    ∏ r ∈ range R, cyclotomicSum m (1 * q ^ k * q ^ (r + 1)) =
      ∑ p ∈ boundedRestricted m k R, q ^ p.size := by
  rw [boundedRestricted, sum_image fun μ _ μ' _ h => partitionOfMult_injective m k R h,
    ← Fin.prod_univ_eq_prod_range (fun r => cyclotomicSum m (1 * q ^ k * q ^ (r + 1)))]
  simp only [cyclotomicSum, ← Fin.sum_univ_eq_sum_range]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun μ _ => ?_
  rw [size_partitionOfMult, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun r _ => ?_
  rw [one_mul, ← pow_add, ← pow_mul]
  ring_nf

/-- **`g_{k,1}` is the generating function of `𝒫_{d,k}`** [AOS, §6]: for `m ≥ 2`, `k ≥ 0` and
`|q| < 1`, `g_{k,1}(q) = ∑_{λ ∈ 𝒫_{2m+1,k}} q^{|λ|}`, the series converging absolutely. -/
theorem hasSum_restrictedPartitions {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun p : restrictedPartitions m k => q ^ (p : Partition).size) (gTail m 1 k q) := by
  classical
  have hlim : ∀ y : ℂ, ‖y‖ < 1 → Tendsto (fun R => ∑ p ∈ boundedRestricted m k R, y ^ p.size)
      atTop (𝓝 (gTail m 1 k y)) := fun y hy => by
    have := (summable_norm_cyclotomicSum_sub_one_and_tendsto_GProduct hm hy (1 * y ^ k)).2
    rw [show gTail m 1 k y = GProduct m (1 * y ^ k) y from rfl]
    exact this.congr fun R => prod_range_cyclotomicSum m k R y
  set t := ‖q‖
  have ht : ‖(t : ℂ)‖ < 1 := by simpa [t] using hq
  set L := (gTail m 1 k (t : ℂ)).re
  have hreal : Tendsto (fun R => ∑ p ∈ boundedRestricted m k R, t ^ p.size) atTop (𝓝 L) := by
    have := (Complex.continuous_re.tendsto _).comp (hlim (t : ℂ) ht)
    refine this.congr fun R => ?_
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_re (∑ p ∈ boundedRestricted m k R, t ^ p.size)]
    push_cast
    rfl
  have hmono : Monotone fun R => ∑ p ∈ boundedRestricted m k R, t ^ p.size :=
    fun R R' h => sum_le_sum_of_subset_of_nonneg (boundedRestricted_mono m k h)
      fun _ _ _ => by positivity
  have hle : ∀ R, ∑ p ∈ boundedRestricted m k R, t ^ p.size ≤ L := hmono.ge_of_tendsto hreal
  have hsumm : Summable fun p : restrictedPartitions m k => t ^ (p : Partition).size := by
    refine summable_of_sum_le (c := L) (fun _ => by positivity) fun u => ?_
    set R := ∑ p ∈ u, (p : Partition).size
    refine le_trans ?_ (hle R)
    rw [show ∑ x ∈ u, t ^ (x : Partition).size =
        ∑ p ∈ u.map (Function.Embedding.subtype _), t ^ p.size by rw [sum_map]; rfl]
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
    obtain ⟨p', hp', rfl⟩ := mem_map.mp hp
    refine mem_boundedRestricted.mpr ⟨p'.2, fun i hi => ?_⟩
    have h1 := le_size_of_mem hi
    have h2 : (p' : Partition).size ≤ R :=
      single_le_sum (f := fun p : restrictedPartitions m k => (p : Partition).size)
        (fun _ _ => Nat.zero_le _) hp'
    have h3 : ((Function.Embedding.subtype _) p' : Partition) = p' := rfl
    rw [h3] at h1
    omega
  have hsc : Summable fun p : restrictedPartitions m k => q ^ (p : Partition).size :=
    hsumm.of_norm_bounded fun p => by rw [norm_pow]
  set B' : ℕ → Finset (restrictedPartitions m k) := fun R =>
    (boundedRestricted m k R).subtype (· ∈ restrictedPartitions m k)
  have hB' : Tendsto B' atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun R R' h p hp => ?_) fun p => ⟨(p : Partition).size,
      ?_⟩
    · rw [mem_subtype] at hp ⊢
      exact boundedRestricted_mono m k h hp
    · rw [mem_subtype]
      exact mem_boundedRestricted.mpr ⟨p.2, fun i hi => (le_size_of_mem hi).trans (by omega)⟩
  have h2 := hsc.hasSum.comp hB'
  have h3 : Tendsto (fun R => ∑ p ∈ boundedRestricted m k R, q ^ p.size) atTop
      (𝓝 (∑' p : restrictedPartitions m k, q ^ (p : Partition).size)) := by
    refine h2.congr fun R => ?_
    simp only [Function.comp_apply, B']
    exact sum_subtype_of_mem (fun p : Partition => q ^ p.size)
      fun p hp => (mem_boundedRestricted.mp hp).1
  have := hsc.hasSum
  rwa [tendsto_nhds_unique h3 (hlim q hq)] at this

/-- Grouping a series `∑_{y ∈ V} q^{w(y)}` by the value of `w`: if each level set
`{y ∈ V : w y = N}` is finite, the coefficient of `q^N` is its cardinality. -/
theorem hasSum_card_fiber {Y : Type*} {V : Set Y} (w : Y → ℕ) {q a : ℂ}
    (h : HasSum (fun y : V => q ^ w y) a) (hfin : ∀ N, {y | y ∈ V ∧ w y = N}.Finite) :
    HasSum (fun N => (Nat.card {y // y ∈ V ∧ w y = N} : ℂ) * q ^ N) a := by
  have h' := (Equiv.sigmaFiberEquiv fun y : V => w y).hasSum_iff.mpr h
  refine h'.sigma fun N => ?_
  let E := Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ V) (fun y => w y = N)
  have : Finite {y : V // w y = N} := by
    have : Finite {y // y ∈ V ∧ w y = N} := (hfin N).to_subtype
    exact Finite.of_equiv _ E.symm
  have := Fintype.ofFinite {y : V // w y = N}
  convert hasSum_fintype (fun c : {y : V // w y = N} => q ^ w (c.1 : Y)) using 1
  · funext c
    rfl
  · rw [sum_congr rfl fun c _ => by rw [c.2], sum_const, card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.card_congr E]

/-- **`g_{k,1}` counts `𝒫_{d,k}`** [AOS, §6]: for `m ≥ 2`, `k ≥ 0` and `|q| < 1`,
`g_{k,1}(q) = ∑_{N ≥ 0} #{λ ∈ 𝒫_{2m+1,k} : |λ| = N} q^N`; each count is finite. -/
theorem hasSum_restrictedPartitionCount {m : ℕ} (hm : 2 ≤ m) (k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun N => (restrictedPartitionCount m k N : ℂ) * q ^ N) (gTail m 1 k q) := by
  refine hasSum_card_fiber Partition.size (hasSum_restrictedPartitions hm k hq) fun N => ?_
  refine (boundedRestricted m k N).finite_toSet.subset fun p hp => ?_
  exact mem_boundedRestricted.mpr
    ⟨hp.1, fun i hi => (le_size_of_mem hi).trans (by have := hp.2; omega)⟩

/-- Each level set of `𝒫_{2m+1,k}` by size is finite. -/
theorem finite_restrictedPartitions_size_le (m k N : ℕ) :
    {p | p ∈ restrictedPartitions m k ∧ p.size ≤ N}.Finite := by
  refine (boundedRestricted m k N).finite_toSet.subset fun p hp => ?_
  exact mem_boundedRestricted.mpr
    ⟨hp.1, fun i hi => (le_size_of_mem hi).trans (by have := hp.2; omega)⟩

end HigherDyson3
