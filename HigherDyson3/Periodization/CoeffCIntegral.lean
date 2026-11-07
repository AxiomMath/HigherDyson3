/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Periodization.CoeffCDisk
public import HigherDyson3.Periodization.CoeffCLeading
public import HigherDyson3.Periodization.CoeffCPos
public import HigherDyson3.Product.GTailSeries

/-!
# Integrality and positivity of the coefficients of `C_{m,ℓ,1}`

For `x = 1`, `C_{m,ℓ,1}(q) = ∑_{k ≥ 1} g_{k,1}(q) ∑_{s=1}^k q^{(m+1)k² - ms² + ℓs}`, and `g_{k,1}`
is the generating function of the set `𝒫_{d,k}` of partitions with parts exceeding `k` and
multiplicities at most `d - 1`. Hence the coefficient of `q^N` in `C_{m,ℓ,1}` is the number of
triples `(k, s, λ)` with `k ≥ 1`, `1 ≤ s ≤ k`, `λ ∈ 𝒫_{d,k}` and
`N = (m+1)k² - ms² + ℓs + |λ|`, a finite count; in particular these coefficients are nonnegative
integers [AOS, Proposition 6.2 and the paragraph after it]. The first nonzero one is the
coefficient of `q^{ℓ+1}`, equal to `1`, and the coefficient of `q^{ℓ+2}` vanishes.

## Main results

* `HigherDyson3.thetaTriples`, `HigherDyson3.thetaTripleCount`: the triples `(k, s, λ)` and their
  number for each `N`.
* `HigherDyson3.hasSum_thetaTriples`: `C_{m,ℓ,1}(q) = ∑_{(k,s,λ)} q^{(m+1)k² - ms² + ℓs + |λ|}`.
* `HigherDyson3.hasSum_thetaTripleCount`: `C_{m,ℓ,1}(q) = ∑_N #(triples of weight N) q^N`.
* `HigherDyson3.thetaTripleCount_leading`: the coefficients below `q^{ℓ+1}` vanish, that of
  `q^{ℓ+1}` is `1` and that of `q^{ℓ+2}` is `0`.
-/

public section

open Finset Filter Topology
open scoped ComplexOrder

namespace HigherDyson3

/-- The triples `(k, s, λ)` with `k ≥ 1`, `1 ≤ s ≤ k` and `λ ∈ 𝒫_{2m+1,k}` [AOS, §6]. -/
def thetaTriples (m : ℕ) : Set (ℕ × ℕ × Partition) :=
  {y | 1 ≤ y.1 ∧ 1 ≤ y.2.1 ∧ y.2.1 ≤ y.1 ∧ y.2.2 ∈ restrictedPartitions m y.1}

/-- The weight `(m+1)k² - ms² + ℓs + |λ|` of a triple `(k, s, λ)` (computed in `ℕ`; the
subtraction is exact when `s ≤ k`). -/
def thetaTripleWeight (m ℓ : ℕ) (y : ℕ × ℕ × Partition) : ℕ :=
  (m + 1) * y.1 ^ 2 + ℓ * y.2.1 - m * y.2.1 ^ 2 + y.2.2.size

/-- The number of triples `(k, s, λ)` with `k ≥ 1`, `1 ≤ s ≤ k`, `λ ∈ 𝒫_{2m+1,k}` and
`N = (m+1)k² - ms² + ℓs + |λ|` [AOS, §6] (`0` if there are infinitely many). -/
noncomputable def thetaTripleCount (m ℓ N : ℕ) : ℕ :=
  Nat.card {y : ℕ × ℕ × Partition // y ∈ thetaTriples m ∧
    (N : ℤ) = (m + 1) * (y.1 : ℤ) ^ 2 - m * (y.2.1 : ℤ) ^ 2 + ℓ * y.2.1 + y.2.2.size}

/-- The exponent `(m+1)k² - ms² + ℓs` of `q` in the `(k, s)` term. -/
private abbrev thetaExp (m ℓ k s : ℕ) : ℕ := (m + 1) * k ^ 2 + ℓ * s - m * s ^ 2

private theorem thetaTripleWeight_eq (m ℓ : ℕ) (y : ℕ × ℕ × Partition) :
    thetaTripleWeight m ℓ y = thetaExp m ℓ y.1 y.2.1 + y.2.2.size := rfl

/-- The summand family `q^{weight}` on the triples, extended by `0`. -/
private noncomputable def tripleFamily (m ℓ : ℕ) (q : ℂ) : ℕ × ℕ × Partition → ℂ :=
  (thetaTriples m).indicator fun y => q ^ thetaTripleWeight m ℓ y

private theorem mem_thetaTriples {m k s : ℕ} {p : Partition} :
    (k, s, p) ∈ thetaTriples m ↔ s ∈ Icc 1 k ∧ p ∈ restrictedPartitions m k := by
  change 1 ≤ k ∧ 1 ≤ s ∧ s ≤ k ∧ p ∈ restrictedPartitions m k ↔ _
  rw [mem_Icc]
  constructor
  · rintro ⟨-, h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1.trans h2, h1, h2, h3⟩

/-- For fixed `(k, s)`, the sum over `λ` is `q^{(m+1)k² - ms² + ℓs} g_{k,1}(q)` for
`1 ≤ s ≤ k`, and `0` otherwise. -/
private theorem hasSum_tripleFamily_slice {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {q : ℂ} (hq : ‖q‖ < 1)
    (k s : ℕ) :
    HasSum (fun p => tripleFamily m ℓ q (k, s, p))
      (if s ∈ Icc 1 k then q ^ thetaExp m ℓ k s * gTail m 1 k q else 0) := by
  classical
  split_ifs with hs
  · have h := ((hasSum_subtype_iff_indicator (f := fun p : Partition => q ^ p.size)
      (s := restrictedPartitions m k)).mp (hasSum_restrictedPartitions hm k hq)).mul_left
      (q ^ thetaExp m ℓ k s)
    have key : ∀ p, tripleFamily m ℓ q (k, s, p) =
        q ^ thetaExp m ℓ k s * (restrictedPartitions m k).indicator (fun p => q ^ p.size) p := by
      intro p
      by_cases hp : p ∈ restrictedPartitions m k
      · rw [tripleFamily, Set.indicator_of_mem (mem_thetaTriples.mpr ⟨hs, hp⟩),
          Set.indicator_of_mem hp, thetaTripleWeight_eq, pow_add]
      · rw [tripleFamily, Set.indicator_of_notMem (fun h => hp (mem_thetaTriples.mp h).2),
          Set.indicator_of_notMem hp, mul_zero]
    rw [show (fun p => tripleFamily m ℓ q (k, s, p)) = fun p => q ^ thetaExp m ℓ k s *
      (restrictedPartitions m k).indicator (fun p => q ^ p.size) p from funext key]
    exact h
  · have key : ∀ p, tripleFamily m ℓ q (k, s, p) = 0 := fun p => by
      rw [tripleFamily, Set.indicator_of_notMem (fun h => hs (mem_thetaTriples.mp h).1)]
    rw [show (fun p => tripleFamily m ℓ q (k, s, p)) = fun _ => 0 from funext key]
    exact hasSum_zero

/-- `∑' s, [1 ≤ s ≤ k] q^{e(k,s)} g = ∑_{s=1}^k q^{e(k,s)} g`. -/
private theorem tsum_slice (m ℓ k : ℕ) (q : ℂ) :
    ∑' s : ℕ, (if s ∈ Icc 1 k then q ^ thetaExp m ℓ k s * gTail m 1 k q else 0) =
      gTail m 1 k q * ∑ s ∈ Icc 1 k, q ^ thetaExp m ℓ k s := by
  rw [tsum_eq_sum (s := Icc 1 k) fun s hs => ite_eq_right hs, mul_sum]
  exact sum_congr rfl fun s hs => by rw [ite_eq_left hs, mul_comm]

/-- The explicit series `∑_{k ≥ 1} g_{k,1}(q) ∑_{s=1}^k q^{(m+1)k² - ms² + ℓs}`. -/
private noncomputable def cSeries (m ℓ : ℕ) (q : ℂ) : ℂ :=
  ∑' k : ℕ, gTail m 1 k q * ∑ s ∈ Icc 1 k, q ^ thetaExp m ℓ k s

private theorem norm_tripleFamily (m ℓ : ℕ) (q : ℂ) (y : ℕ × ℕ × Partition) :
    ‖tripleFamily m ℓ q y‖ = ‖tripleFamily m ℓ (‖q‖ : ℂ) y‖ := by
  classical
  by_cases hy : y ∈ thetaTriples m
  · rw [tripleFamily, tripleFamily, Set.indicator_of_mem hy, Set.indicator_of_mem hy, norm_pow,
      norm_pow]
    simp
  · rw [tripleFamily, tripleFamily, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

private theorem tripleFamily_real (m ℓ : ℕ) (t : ℝ) (y : ℕ × ℕ × Partition) :
    tripleFamily m ℓ (t : ℂ) y =
      ((thetaTriples m).indicator (fun y => t ^ thetaTripleWeight m ℓ y) y : ℝ) := by
  classical
  by_cases hy : y ∈ thetaTriples m
  · rw [tripleFamily, Set.indicator_of_mem hy, Set.indicator_of_mem hy]; push_cast; rfl
  · rw [tripleFamily, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp

/-- The triple family is absolutely summable for `|q| < 1`. -/
private theorem summable_tripleFamily {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (tripleFamily m ℓ q) := by
  set t := ‖q‖
  have ht : ‖(t : ℂ)‖ < 1 := by simpa [t] using hq
  set r : ℕ × ℕ × Partition → ℝ := (thetaTriples m).indicator fun y => t ^ thetaTripleWeight m ℓ y
  have hr0 : ∀ y, 0 ≤ r y := fun y => Set.indicator_nonneg (fun _ _ => by positivity) y
  have hnr : ∀ y, ‖tripleFamily m ℓ (t : ℂ) y‖ = r y := fun y => by
    rw [tripleFamily_real, Complex.norm_real, Real.norm_of_nonneg (hr0 y)]
  -- slices over `λ`
  have hslice : ∀ k s, Summable (fun p => r (k, s, p)) ∧
      ((∑' p, r (k, s, p) : ℝ) : ℂ) =
        if s ∈ Icc 1 k then (t : ℂ) ^ thetaExp m ℓ k s * gTail m 1 k t else 0 := by
    intro k s
    have h := hasSum_tripleFamily_slice hm ℓ ht k s
    have hs : Summable fun p => r (k, s, p) := by
      have := (summable_norm_iff (E := ℂ)).mpr h.summable
      simpa only [hnr] using this
    refine ⟨hs, ?_⟩
    rw [Complex.ofReal_tsum]
    refine (h.congr_fun fun p => ?_).tsum_eq
    rw [tripleFamily_real]
  -- slices over `(s, λ)`
  have hk : ∀ k, Summable (fun z : ℕ × Partition => r (k, z)) ∧
      ((∑' z : ℕ × Partition, r (k, z) : ℝ) : ℂ) =
        gTail m 1 k t * ∑ s ∈ Icc 1 k, (t : ℂ) ^ thetaExp m ℓ k s := by
    intro k
    have hs2 : Summable fun s => ∑' p, r (k, s, p) :=
      summable_of_ne_finset_zero (s := Icc 1 k) fun s hs => by
        have := (hslice k s).2
        rw [ite_eq_right hs] at this
        exact_mod_cast this
    have hsum : Summable (fun z : ℕ × Partition => r (k, z)) :=
      (summable_prod_of_nonneg fun z => hr0 _).mpr ⟨fun s => (hslice k s).1, hs2⟩
    refine ⟨hsum, ?_⟩
    rw [hsum.tsum_prod' fun s => (hslice k s).1, Complex.ofReal_tsum, ← tsum_slice]
    exact tsum_congr fun s => (hslice k s).2
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_gTail hm (norm_nonneg q) hq (B := 1) zero_le_one
  have hout : Summable fun k => ∑' z : ℕ × Partition, r (k, z) := by
    have hg := (summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖t‖ < 1 by
      rw [Real.norm_of_nonneg (norm_nonneg q)]; exact hq)).mul_left C
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun z => hr0 _) (fun k => ?_) hg
    have h1 : ∑' z : ℕ × Partition, r (k, z) =
        ‖gTail m 1 k t * ∑ s ∈ Icc 1 k, (t : ℂ) ^ thetaExp m ℓ k s‖ := by
      rw [← (hk k).2, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun z => hr0 _)]
    rw [h1, norm_mul]
    refine mul_le_mul (hC k _ (by simp [t]) 1 (by simp)) ?_ (norm_nonneg _) hC0
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ s ∈ Icc 1 k, ‖(t : ℂ) ^ thetaExp m ℓ k s‖ ≤ t ^ k := by
      intro s hs
      have ht1 : t ≤ 1 := hq.le
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg q)]
      calc t ^ thetaExp m ℓ k s ≤ t ^ (k ^ 2) :=
            pow_le_pow_of_le_one (norm_nonneg _) ht1 (coeffCqTerm_exponent hs)
        _ ≤ t ^ k := pow_le_pow_of_le_one (norm_nonneg _) ht1 (by nlinarith)
    refine (sum_le_sum hterm).trans ?_
    simp
  have hrs : Summable r := (summable_prod_of_nonneg hr0).mpr ⟨fun k => (hk k).1, hout⟩
  refine Summable.of_norm_bounded hrs fun y => ?_
  rw [norm_tripleFamily, hnr]

private theorem hasSum_tripleFamily {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (tripleFamily m ℓ q) (cSeries m ℓ q) := by
  have hf := summable_tripleFamily hm ℓ hq
  convert hf.hasSum using 1
  rw [hf.tsum_prod' fun k => hf.prod_factor k, cSeries]
  refine tsum_congr fun k => ?_
  rw [(hf.prod_factor k).tsum_prod' fun s => (hf.prod_factor k).prod_factor s, ← tsum_slice]
  exact tsum_congr fun s => ((hasSum_tripleFamily_slice hm ℓ hq k s).tsum_eq).symm

/-- `C_{m,ℓ,1}(τ)` is the explicit series at `q = e(τ)`. -/
private theorem coeffC_zero_eq_cSeries (m ℓ : ℕ) (τ : ℂ) :
    coeffC m ℓ 0 τ = cSeries m ℓ (e τ) := by
  have hx : e ((0 : ℚ) : ℂ) = 1 := by simp [e]
  rw [coeffC, cSeries, hx, one_zpow, one_mul]
  refine tsum_congr fun k => ?_
  congr 1
  refine sum_congr rfl fun s hs => ?_
  have hsk : s ≤ k := (mem_Icc.mp hs).2
  have h3 : m * s ^ 2 ≤ (m + 1) * k ^ 2 + ℓ * s := by
    have : m * s ^ 2 ≤ m * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsk 2)
    nlinarith
  have h2 : (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s) =
      ((thetaExp m ℓ k s : ℕ) : ℤ) := by
    push_cast [thetaExp, h3]; ring
  rw [one_zpow, one_mul, h2, zpow_natCast]

/-- **The `q`-expansion of `C_{m,ℓ,1}` over triples** [AOS, §6]: for `m ≥ 2` and `τ ∈ ℍ`,
`C_{m,ℓ,1}(τ) = ∑_{(k,s,λ)} q^{(m+1)k² - ms² + ℓs + |λ|}`, `q = e(τ)`, over `k ≥ 1`, `1 ≤ s ≤ k`,
`λ ∈ 𝒫_{2m+1,k}`, the series converging absolutely. -/
theorem hasSum_thetaTriples {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun y : thetaTriples m => e τ ^ thetaTripleWeight m ℓ y) (coeffC m ℓ 0 τ) := by
  have hq : ‖e τ‖ < 1 := by
    rw [e, Complex.norm_exp]
    refine Real.exp_lt_one_iff.mpr ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith [Real.pi_pos]
  rw [coeffC_zero_eq_cSeries]
  exact (hasSum_subtype_iff_indicator (f := fun y => e τ ^ thetaTripleWeight m ℓ y)).mpr
    (hasSum_tripleFamily hm ℓ hq)

/-- `(m+1)k² - ms² + ℓs ≥ k² + ℓ` for `1 ≤ s ≤ k`. -/
private theorem thetaExp_ge {m ℓ k s : ℕ} (hs : s ∈ Icc 1 k) : k ^ 2 + ℓ ≤ thetaExp m ℓ k s := by
  obtain ⟨hs1, hsk⟩ := mem_Icc.mp hs
  have h1 : m * s ^ 2 ≤ m * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsk 2)
  have h2 : ℓ ≤ ℓ * s := Nat.le_mul_of_pos_right ℓ hs1
  have h3 : (m + 1) * k ^ 2 = m * k ^ 2 + k ^ 2 := by ring
  simp only [thetaExp]
  omega

/-- The count of `thetaTripleCount` is that of the triples of weight `N`. -/
private theorem thetaTripleCount_eq_card (m ℓ N : ℕ) :
    thetaTripleCount m ℓ N =
      Nat.card {y : ℕ × ℕ × Partition // y ∈ thetaTriples m ∧ thetaTripleWeight m ℓ y = N} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  obtain ⟨k, s, p⟩ := y
  refine and_congr_right fun hy => ?_
  have hs := (mem_thetaTriples.mp hy).1
  have hsk : s ≤ k := (mem_Icc.mp hs).2
  have h3 : m * s ^ 2 ≤ (m + 1) * k ^ 2 + ℓ * s := by
    have : m * s ^ 2 ≤ m * k ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsk 2)
    nlinarith
  have hw : ((thetaTripleWeight m ℓ (k, s, p) : ℕ) : ℤ) =
      (m + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s + p.size := by
    simp only [thetaTripleWeight]
    push_cast [h3]
    ring
  simp only at hw ⊢
  rw [← hw]
  exact ⟨fun h => by exact_mod_cast h.symm, fun h => by rw [h]⟩

/-- For each `N` there are finitely many triples `(k, s, λ)` of weight `N` [AOS, §6]. -/
theorem finite_thetaTriples_weight (m ℓ N : ℕ) :
    {y | y ∈ thetaTriples m ∧ thetaTripleWeight m ℓ y = N}.Finite := by
  refine ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod
    (finite_restrictedPartitions_size_le m 0 N))).subset ?_
  rintro ⟨k, s, p⟩ ⟨hy, hw⟩
  obtain ⟨hs, hp⟩ := mem_thetaTriples.mp hy
  have he := thetaExp_ge (m := m) (ℓ := ℓ) hs
  have hsk : s ≤ k := (mem_Icc.mp hs).2
  have hkk : k ≤ k ^ 2 := by nlinarith
  rw [thetaTripleWeight_eq] at hw
  dsimp only at hw
  have hp' := mem_restrictedPartitions.mp hp
  simp only [Set.mem_prod, Set.mem_Iic, Set.mem_ofPred_eq]
  refine ⟨by omega, by omega,
    mem_restrictedPartitions.mpr fun i hi => ⟨by have := (hp' i hi).1; omega, (hp' i hi).2⟩,
    by omega⟩

private theorem hasSum_thetaTripleCount_cSeries {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {q : ℂ}
    (hq : ‖q‖ < 1) :
    HasSum (fun N => (thetaTripleCount m ℓ N : ℂ) * q ^ N) (cSeries m ℓ q) := by
  have h := (hasSum_subtype_iff_indicator (f := fun y => q ^ thetaTripleWeight m ℓ y)
    (s := thetaTriples m)).mpr (hasSum_tripleFamily hm ℓ hq)
  simp only [thetaTripleCount_eq_card]
  exact hasSum_card_fiber (thetaTripleWeight m ℓ) h (finite_thetaTriples_weight m ℓ)

/-- **The coefficients of `C_{m,ℓ,1}` count triples** [AOS, Proposition 6.2 and §6]: for `m ≥ 2`
and `τ ∈ ℍ`, `C_{m,ℓ,1}(τ) = ∑_{N ≥ 0} c_N q^N` with `q = e(τ)` and `c_N ∈ ℕ` the (finite) number
of triples `(k, s, λ)` with `k ≥ 1`, `1 ≤ s ≤ k`, `λ ∈ 𝒫_{2m+1,k}` and
`N = (m+1)k² - ms² + ℓs + |λ|`; in particular the coefficients are nonnegative integers. -/
theorem hasSum_thetaTripleCount {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun N => (thetaTripleCount m ℓ N : ℂ) * e τ ^ N) (coeffC m ℓ 0 τ) := by
  have hq : ‖e τ‖ < 1 := by
    rw [e, Complex.norm_exp]
    refine Real.exp_lt_one_iff.mpr ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith [Real.pi_pos]
  rw [coeffC_zero_eq_cSeries]
  exact hasSum_thetaTripleCount_cSeries hm ℓ hq

/-- **The leading coefficients of `C_{m,ℓ,1}`**: no triple has weight `N ≤ ℓ`, exactly one
(`(1, 1, ∅)`) has weight `ℓ + 1`, and none has weight `ℓ + 2`; that is,
`C_{m,ℓ,1} = q^{ℓ+1}(1 + O(q^2))` [AOS, Proposition 6.2]. -/
theorem thetaTripleCount_leading (m ℓ : ℕ) :
    (∀ N ≤ ℓ, thetaTripleCount m ℓ N = 0) ∧ thetaTripleCount m ℓ (ℓ + 1) = 1 ∧
      thetaTripleCount m ℓ (ℓ + 2) = 0 := by
  have key : ∀ k s p, (k, s, p) ∈ thetaTriples m →
      k ^ 2 + ℓ + p.size ≤ thetaTripleWeight m ℓ (k, s, p) ∧ 1 ≤ k ∧ 1 ≤ s ∧ s ≤ k :=
      fun k s p hy => by
    obtain ⟨hs, -⟩ := mem_thetaTriples.mp hy
    have := thetaExp_ge (m := m) (ℓ := ℓ) hs
    rw [thetaTripleWeight_eq]
    exact ⟨by simp only; omega, (mem_Icc.mp hs).1.trans (mem_Icc.mp hs).2, (mem_Icc.mp hs).1,
      (mem_Icc.mp hs).2⟩
  refine ⟨fun N hN => ?_, ?_, ?_⟩
  · rw [thetaTripleCount_eq_card, Nat.card_eq_zero]
    left
    refine ⟨fun ⟨⟨k, s, p⟩, hy, hw⟩ => ?_⟩
    obtain ⟨h1, h2, -⟩ := key k s p hy
    have : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ h2
    omega
  · rw [thetaTripleCount_eq_card, Nat.card_eq_one_iff_exists]
    have h0 : ((1, 1, 0) : ℕ × ℕ × Partition) ∈ thetaTriples m :=
      mem_thetaTriples.mpr ⟨by simp,
        mem_restrictedPartitions.mpr fun i hi => absurd hi (Multiset.notMem_zero i)⟩
    refine ⟨⟨(1, 1, 0), h0, by simp [thetaTripleWeight, Partition.size]; omega⟩, ?_⟩
    rintro ⟨⟨k, s, p⟩, hy, hw⟩
    obtain ⟨h1, h2, h4, h3⟩ := key k s p hy
    have hk : k = 1 := by nlinarith
    subst hk
    have hs : s = 1 := by omega
    subst hs
    have hp : p.size = 0 := by omega
    have : p = 0 := by
      rw [Partition.size, Multiset.sum_eq_zero_iff] at hp
      refine Multiset.eq_zero_of_forall_notMem fun i hi => ?_
      have := hp i (Multiset.mem_map_of_mem _ hi)
      exact (PNat.ne_zero i) this
    subst this
    rfl
  · rw [thetaTripleCount_eq_card, Nat.card_eq_zero]
    left
    refine ⟨fun ⟨⟨k, s, p⟩, hy, hw⟩ => ?_⟩
    obtain ⟨h1, h2, h4, h3⟩ := key k s p hy
    have hk : k = 1 := by nlinarith
    subst hk
    have hs : s = 1 := by omega
    subst hs
    have hw' : thetaTripleWeight m ℓ (1, 1, p) = ℓ + 1 + p.size := by
      simp only [thetaTripleWeight]
      have : (m + 1) * 1 ^ 2 + ℓ * 1 - m * 1 ^ 2 = ℓ + 1 := by
        simp only [one_pow, mul_one]; omega
      omega
    have hp1 : p.size = 1 := by omega
    obtain ⟨i, hi⟩ : ∃ i, i ∈ p := by
      by_contra h
      push Not at h
      rw [Multiset.eq_zero_of_forall_notMem h] at hp1
      simp [Partition.size] at hp1
    have hle : (i : ℕ) ≤ p.size := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hi)
    have := (mem_restrictedPartitions.mp (mem_thetaTriples.mp hy).2 i hi).1
    omega

/-- `C_{m,ℓ,1}(q)` agrees with the explicit series for `q ≠ 0`. -/
private theorem coeffCq_one_eq_cSeries_of_ne_zero (m ℓ : ℕ) {q : ℂ} (hq0 : q ≠ 0) :
    coeffCq m ℓ 1 q = cSeries m ℓ q := by
  set τ := Complex.log q / (2 * Real.pi * Complex.I)
  have hτ : e τ = q := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [e, show 2 * Real.pi * Complex.I * τ = Complex.log q by
      simp only [τ]; field_simp, Complex.exp_log hq0]
  have hx : e ((0 : ℚ) : ℂ) = 1 := by simp [e]
  rw [← hτ, ← coeffC_zero_eq_cSeries, coeffC_eq_coeffCq, hx]

/-- **The `q`-expansion of `C_{m,ℓ,1}` on the whole disc** [AOS, Propositions 6.1, 6.2]: for
`m ≥ 2` and `|q| < 1` (including `q = 0`), `C_{m,ℓ,1}(q) = ∑_{N ≥ 0} c_N q^N` with `c_N ∈ ℕ` the
number of triples `(k, s, λ)` of weight `N`. -/
theorem hasSum_thetaTripleCount_coeffCq {m : ℕ} (hm : 2 ≤ m) (ℓ : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun N => (thetaTripleCount m ℓ N : ℂ) * q ^ N) (coeffCq m ℓ 1 q) := by
  by_cases hq0 : q ≠ 0
  · rw [coeffCq_one_eq_cSeries_of_ne_zero m ℓ hq0]
    exact hasSum_thetaTripleCount_cSeries hm ℓ hq
  push Not at hq0
  subst hq0
  have hc0 : thetaTripleCount m ℓ 0 = 0 := (thetaTripleCount_leading m ℓ).1 0 (Nat.zero_le _)
  have hz : HasSum (fun N => (thetaTripleCount m ℓ N : ℂ) * (0 : ℂ) ^ N) 0 := by
    refine (hasSum_zero).congr_fun fun N => ?_
    rcases N with _ | N
    · simp [hc0]
    · simp
  convert hz using 1
  -- `C_{m,ℓ,1}(0) = 0`, by continuity
  set K := ∑' N, (thetaTripleCount m ℓ N : ℝ) * (1 / 2) ^ N
  have hK : Summable fun N => (thetaTripleCount m ℓ N : ℝ) * (1 / 2) ^ N := by
    have h := (hasSum_thetaTripleCount_cSeries hm ℓ (q := (1 / 2 : ℂ)) (by norm_num)).summable
    have := (summable_norm_iff (E := ℂ)).mpr h
    refine this.congr fun N => ?_
    rw [norm_mul, norm_pow]
    simp
  have hbound : ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ 1 / 2 → ‖coeffCq m ℓ 1 q‖ ≤ 2 * K * ‖q‖ := by
    intro q hq0 hq2
    have hq1 : ‖q‖ < 1 := by linarith
    have hs := hasSum_thetaTripleCount_cSeries hm ℓ hq1
    rw [coeffCq_one_eq_cSeries_of_ne_zero m ℓ hq0, ← hs.tsum_eq]
    have hn : Summable fun N => ‖(thetaTripleCount m ℓ N : ℂ) * q ^ N‖ :=
      (summable_norm_iff (E := ℂ)).mpr hs.summable
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    have hle : ∀ N, ‖(thetaTripleCount m ℓ N : ℂ) * q ^ N‖ ≤
        2 * ‖q‖ * ((thetaTripleCount m ℓ N : ℝ) * (1 / 2) ^ N) := by
      intro N
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      rcases N with _ | N
      · simp [hc0]
      · have : ‖q‖ ^ (N + 1) ≤ 2 * ‖q‖ * (1 / 2) ^ (N + 1) := by
          rw [pow_succ', pow_succ']
          have := pow_le_pow_left₀ (norm_nonneg q) hq2 N
          nlinarith [norm_nonneg q, pow_nonneg (norm_nonneg q) N]
        nlinarith [(Nat.cast_nonneg (thetaTripleCount m ℓ (N + 1)) : (0 : ℝ) ≤ _)]
    calc ∑' N, ‖(thetaTripleCount m ℓ N : ℂ) * q ^ N‖
        ≤ ∑' N, 2 * ‖q‖ * ((thetaTripleCount m ℓ N : ℝ) * (1 / 2) ^ N) :=
          hn.tsum_le_tsum hle (hK.mul_left _)
      _ = 2 * K * ‖q‖ := by rw [tsum_mul_left]; ring
  have hlim : Tendsto (coeffCq m ℓ 1) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun q : ℂ => 2 * K * ‖q‖) (𝓝[≠] 0) (𝓝 0) := by
      have h1 : Continuous fun q : ℂ => 2 * K * ‖q‖ := continuous_const.mul continuous_norm
      have := (h1.tendsto (0 : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      simpa using this
    refine squeeze_zero_norm' ?_ h0
    have hb : Metric.ball (0 : ℂ) (1 / 2) ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
    have hball : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ∈ Metric.ball (0 : ℂ) (1 / 2) ∧ q ≠ 0 :=
      Filter.Eventually.and hb self_mem_nhdsWithin
    filter_upwards [hball] with q hq
    exact hbound q hq.2 (le_of_lt (mem_ball_zero_iff.mp hq.1))
  have hcont : Tendsto (coeffCq m ℓ 1) (𝓝[≠] 0) (𝓝 (coeffCq m ℓ 1 0)) :=
    ((differentiableOn_coeffCq hm ℓ (by simp)).continuousOn.continuousAt
      (Metric.ball_mem_nhds 0 one_pos)).tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hcont hlim

/-- **[AOS, Proposition 6.2] and the paragraph after it**, all claims together, for `m ≥ 2` and
`0 ≤ ℓ < 2m`:
* the leading term: for `x = e(α)`, `0 ≤ α < 1`, there are `C, T > 0` with
  `|C_{m,ℓ,x}(τ) - x^{ℓ-2} q^{ℓ+1}| ≤ C |q|^{ℓ+3}` for `Im τ ≥ T`;
* `C_{m,ℓ,1}(it) > 0` for real `t > 0`;
* `g_{k,1}(q) = ∑_N #{λ ∈ 𝒫_{2m+1,k} : |λ| = N} q^N` for `|q| < 1`, each count finite;
* `C_{m,ℓ,1}(q) = ∑_N c_N q^N` on `|q| < 1` (and at `q = e(τ)`), where `c_N ∈ ℕ` is the number
  of triples `(k, s, λ)`, `k ≥ 1`, `1 ≤ s ≤ k`, `λ ∈ 𝒫_{2m+1,k}`, with
  `N = (m+1)k² - ms² + ℓs + |λ|`, a finite set; so the coefficients are nonnegative integers;
* `c_N = 0` for `N ≤ ℓ`, `c_{ℓ+1} = 1` and `c_{ℓ+2} = 0`. -/
theorem coeffC_one_spec {m : ℕ} (hm : 2 ≤ m) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    (∀ α : ℚ, 0 ≤ α → α < 1 → ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖coeffC m ℓ α τ - e α ^ ((ℓ : ℤ) - 2) * e τ ^ (ℓ + 1)‖ ≤ C * ‖e τ‖ ^ (ℓ + 3)) ∧
    (∀ t : ℝ, 0 < t → 0 < coeffC m ℓ 0 (Complex.I * t)) ∧
    (∀ k N : ℕ, {p | p ∈ restrictedPartitions m k ∧ p.size = N}.Finite) ∧
    (∀ k : ℕ, ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun N => (restrictedPartitionCount m k N : ℂ) * q ^ N) (gTail m 1 k q)) ∧
    (∀ N : ℕ, {y | y ∈ thetaTriples m ∧ thetaTripleWeight m ℓ y = N}.Finite) ∧
    (∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun N => (thetaTripleCount m ℓ N : ℂ) * q ^ N) (coeffCq m ℓ 1 q)) ∧
    (∀ τ : ℂ, 0 < τ.im →
      HasSum (fun N => (thetaTripleCount m ℓ N : ℂ) * e τ ^ N) (coeffC m ℓ 0 τ)) ∧
    ((∀ N ≤ ℓ, thetaTripleCount m ℓ N = 0) ∧ thetaTripleCount m ℓ (ℓ + 1) = 1 ∧
      thetaTripleCount m ℓ (ℓ + 2) = 0) :=
  ⟨fun _ hα0 hα1 => exists_norm_coeffC_sub_le hm hα0 hα1 hℓ, fun _ ht => coeffC_pos hm hℓ ht,
    fun k N => (finite_restrictedPartitions_size_le m k N).subset fun _ hp => ⟨hp.1, hp.2.le⟩,
    fun k _ hq => hasSum_restrictedPartitionCount hm k hq, finite_thetaTriples_weight m ℓ,
    fun _ hq => hasSum_thetaTripleCount_coeffCq hm ℓ hq,
    fun _ hτ => hasSum_thetaTripleCount hm ℓ hτ,
    thetaTripleCount_leading m ℓ⟩

end HigherDyson3
