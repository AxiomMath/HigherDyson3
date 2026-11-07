/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.DoubleSummand
public import HigherDyson3.Bounds.DenominatorBound
public import HigherDyson3.Divisor.DivisorComplOpen
public import HigherDyson3.Holomorphy.NormalSeriesHolomorphic

/-!
# Normal convergence and holomorphy of the periodization of a Lambert seed

Let `m ≥ 1`, `x = e(α)`, `c = e(β)` with `β ∈ ℚ ∩ [0,1)`, and let `(b_i)` be holomorphic on
the unit disc with `|b_i(q)| ≤ B_Q |q|^{i²}` on `|q| ≤ Q < 1`. For the Lambert seed
`Φ(u) = x⁻² ∑_i b_i / (1 - c q^i u)`, the periodization `ℰ_Φ` converges normally on compact
subsets of `(ℍ × ℂ) \ 𝒟_c` and is holomorphic there [AOS, Lemma 7.4(a)].

On a compact `S ⊆ (ℍ × ℂ) \ 𝒟_c` the reciprocal denominators `|1 - c u q^j|⁻¹` are bounded
uniformly in `j` (`HigherDyson3.denominator_bound`), so the double summands have the Gaussian
majorant of `HigherDyson3.exists_majorant_lambertDoubleSummand`.

## Main results

* `HigherDyson3.seedPeriodization_lambertSeed_normal`: normal convergence on compact subsets.
* `HigherDyson3.seedPeriodization_lambertSeed_eq_tsum_double`: off `𝒟_c`, `ℰ_Φ` is the sum of
  the absolutely summable double series.
* `HigherDyson3.differentiableOn_seedPeriodization_lambertSeed`: holomorphy off `𝒟_c`.
-/

public section

open scoped ENNReal NNReal

namespace HigherDyson3

/-- The Gaussian majorant of the double summands on a compact subset of `(ℍ × ℂ) \ 𝒟_c`. -/
theorem exists_majorant_lambertDoubleSummand_of_subset {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor β) :
    ∃ M : ℤ × ℕ → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧ ∀ k : ℤ × ℕ, ∀ p ∈ S,
      ‖lambertDoubleSummand m α β b k.1 k.2 p.1 p.2‖ ≤ M k := by
  obtain ⟨A, -, hA⟩ := denominator_bound β hβ0 hβ1 S hS hSD
  obtain ⟨M, hM, hM0, hle⟩ := exists_majorant_lambertDoubleSummand hm α β hB S hS
    (hSD.trans Set.sdiff_subset) Set.univ (A := A) fun p hp j _ => hA p hp j
  exact ⟨M, hM, hM0, fun k p hp => hle k (Set.mem_univ _) p hp⟩

/-- A summable majorant of the summands `x^{-2n} q^{mn²} u^{2mn} Φ(q^n u)` of the periodization
of a Lambert seed, uniform on a compact subset of `(ℍ × ℂ) \ 𝒟_c`. -/
theorem exists_majorant_seedPeriodization_lambertSeed {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor β) :
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ n : ℤ, ∀ p ∈ S,
      ‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) *
        lambertSeed (e α) (e β) b (e p.1 ^ n * e p.2) (e p.1)‖ ≤ M n := by
  obtain ⟨M, hM, hM0, hle⟩ :=
    exists_majorant_lambertDoubleSummand_of_subset hm α hβ0 hβ1 hB S hS hSD
  refine ⟨fun n => ∑' i : ℕ, M (n, i), hM.prod, fun n p hp => ?_⟩
  have hrow : Summable fun i : ℕ => M (n, i) := hM.prod_factor n
  have hn : Summable fun i : ℕ => ‖lambertDoubleSummand m α β b n i p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hle (n, i) p hp) hrow
  rw [seedPeriodization_summand_lambertSeed]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun i => hle (n, i) p hp) hrow)

/-- **Normal convergence of the periodization of a Lambert seed** [AOS, Lemma 7.4(a)]. For
`m ≥ 1`, `x = e(α)`, `c = e(β)` with `0 ≤ β < 1` rational, coefficients with a Gaussian bound
`|b_i(q)| ≤ B_Q |q|^{i²}` (`|q| ≤ Q`, `0 < Q < 1`) and a compact `S ⊆ (ℍ × ℂ) \ 𝒟_c`,
`∑_{n ∈ ℤ} sup_{(τ,w) ∈ S} |x^{-2n} q^{mn²} u^{2mn} Φ(q^n u)| < ∞`, where
`Φ(u) = x⁻² ∑_i b_i / (1 - c q^i u)`, `q = e(τ)`, `u = e(w)`. -/
theorem seedPeriodization_lambertSeed_normal {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor β) :
    ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
      e p.2 ^ (2 * (m : ℤ) * n) * lambertSeed (e α) (e β) b (e p.1 ^ n * e p.2) (e p.1)‖₊ :
        ℝ≥0∞) < ∞ := by
  obtain ⟨M, hM, hM0, hle⟩ :=
    exists_majorant_lambertDoubleSummand_of_subset hm α hβ0 hβ1 hB S hS hSD
  calc ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * n) * lambertSeed (e α) (e β) b (e p.1 ^ n * e p.2) (e p.1)‖₊ :
          ℝ≥0∞)
      ≤ ∑' n : ℤ, ∑' i : ℕ, ENNReal.ofReal (M (n, i)) := by
        refine ENNReal.tsum_le_tsum fun n => iSup₂_le fun p hp => ?_
        rw [seedPeriodization_summand_lambertSeed, ← enorm_eq_nnnorm]
        refine (enorm_tsum_le_tsum_enorm).trans (ENNReal.tsum_le_tsum fun i => ?_)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hle (n, i) p hp)
    _ = ∑' k : ℤ × ℕ, ENNReal.ofReal (M k) := ENNReal.tsum_prod.symm
    _ = ENNReal.ofReal (∑' k, M k) := (ENNReal.ofReal_tsum_of_nonneg hM0 hM).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- **The periodization of a Lambert seed as a double series.** Off `𝒟_c` the double
summands are absolutely summable over `ℤ × ℕ` and their sum is `ℰ_Φ(τ,w)`. -/
theorem seedPeriodization_lambertSeed_eq_tsum_double {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor β) :
    Summable (fun k : ℤ × ℕ => ‖lambertDoubleSummand m α β b k.1 k.2 τ w‖) ∧
      seedPeriodization m α (lambertSeed (e α) (e β) b) τ w =
        ∑' k : ℤ × ℕ, lambertDoubleSummand m α β b k.1 k.2 τ w := by
  obtain ⟨M, hM, -, hle⟩ := exists_majorant_lambertDoubleSummand_of_subset hm α hβ0 hβ1 hB
    {(τ, w)} isCompact_singleton (Set.singleton_subset_iff.mpr hτw)
  have hnorm : Summable (fun k : ℤ × ℕ => ‖lambertDoubleSummand m α β b k.1 k.2 τ w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => hle k (τ, w) (Set.mem_singleton _)) hM
  refine ⟨hnorm, ?_⟩
  rw [hnorm.of_norm.tsum_prod' hnorm.of_norm.prod_factor]
  exact tsum_congr fun n => seedPeriodization_summand_lambertSeed m α β b n τ w

/-- Off `𝒟_c`, no denominator `1 - c u q^j` vanishes. -/
lemma one_sub_e_mul_ne_zero_of_not_mem_divisor {β : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {p : ℂ × ℂ} (hp : p ∈ halfPlaneProd \ divisor β) (j : ℤ) :
    1 - e β * e p.2 * e p.1 ^ j ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ := (divisor_char β hβ0 hβ1 (τ := p.1) (w := p.2) hp.1 j).mp h
  exact hp.2 (Set.mem_iUnion₂.mpr ⟨_, b, hb⟩)

/-- **Holomorphy of the periodization of a Lambert seed off `𝒟_c`** [AOS, Lemma 7.4(a)]. For
`m ≥ 1`, `x = e(α)`, `c = e(β)` with `0 ≤ β < 1` rational, and coefficients `b_i` holomorphic
on the unit disc with a Gaussian bound, the set `(ℍ × ℂ) \ 𝒟_c` is open and `ℰ_Φ` is
holomorphic on it. -/
theorem differentiableOn_seedPeriodization_lambertSeed {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2)) :
    IsOpen (halfPlaneProd \ divisor β) ∧
      DifferentiableOn ℂ
        (fun p : ℂ × ℂ => seedPeriodization m α (lambertSeed (e α) (e β) b) p.1 p.2)
        (halfPlaneProd \ divisor β) := by
  have hU := divisor_compl_open β hβ0 hβ1
  refine ⟨hU, ?_⟩
  have hsum : DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∑' k : ℤ × ℕ, lambertDoubleSummand m α β b k.1 k.2 p.1 p.2)
      (halfPlaneProd \ divisor β) :=
    differentiableOn_tsum_of_normal (f := fun (k : ℤ × ℕ) (p : ℂ × ℂ) =>
        lambertDoubleSummand m α β b k.1 k.2 p.1 p.2) hU
      (fun k p hp => (differentiableAt_lambertDoubleSummand m α β hb k.1 k.2 hp.1
        (one_sub_e_mul_ne_zero_of_not_mem_divisor hβ0 hβ1 hp _)).differentiableWithinAt)
      fun K hK hKc => by
        obtain ⟨M, hM, -, hle⟩ :=
          exists_majorant_lambertDoubleSummand_of_subset hm α hβ0 hβ1 hB K hKc hK
        exact ⟨M, hM, hle⟩
  refine hsum.congr fun p hp => ?_
  exact (seedPeriodization_lambertSeed_eq_tsum_double hm α hβ0 hβ1 hB hp).2

end HigherDyson3
