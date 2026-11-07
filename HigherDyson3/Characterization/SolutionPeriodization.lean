/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.SeedDecomposition
public import HigherDyson3.Lambert.Slice
public import HigherDyson3.Lambert.TwistedLaw

/-!
# The periodization of a solution seed for fixed `τ`

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ ∩ [0,1)`, `τ ∈ ℍ` and `q = e(τ)`. For `Y ∈ V` and any
meromorphic continuation `Φ` of its seed `𝒢_Y`, the bilateral periodization
`ℰ_Y(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} Φ(q^n u)` converges normally on compact subsets of
the complement of the orbits `-α + ℤτ + ℤ` and `-k/d + ℤτ + ℤ` (`1 ≤ k ≤ d - 1`), is holomorphic
there, has at most simple poles, and satisfies the twisted law [AOS, Theorem 7.1(ii)(b)].

Off the orbits, `ℰ_Y = a ℰ_{Φ_x} + ∑_k s_k ℰ_{Φ_{ω^k}}`
(`HigherDyson3.seedPeriodization_eq_combination`), a finite combination of periodizations of
Lambert seeds, to each of which [AOS, Lemma 7.4] applies.

## Main results

* `HigherDyson3.solutionPeriodization_normal`: normal convergence on compact sets.
* `HigherDyson3.differentiableOn_solutionPeriodization`: holomorphy off the orbits.
* `HigherDyson3.solutionPeriodization_simple_poles`: at most simple poles.
* `HigherDyson3.solutionPeriodization_twisted_law`: the twisted law.
-/

public section

noncomputable section

open Complex Finset Filter Topology
open scoped ENNReal NNReal

namespace HigherDyson3

variable {m : ℕ} {α : ℚ}

/-- A family of functions dominated on `S` by a summable sequence has finite sum of suprema. -/
lemma tsum_iSup_nnnorm_lt_top {X : Type*} {f : ℤ → X → ℂ} {S : Set X} {M : ℤ → ℝ}
    (hM : Summable M) (hle : ∀ n, ∀ p ∈ S, ‖f n p‖ ≤ M n) :
    ∑' n : ℤ, ⨆ p ∈ S, (‖f n p‖₊ : ℝ≥0∞) < ∞ := by
  calc ∑' n : ℤ, ⨆ p ∈ S, (‖f n p‖₊ : ℝ≥0∞) ≤ ∑' n : ℤ, ENNReal.ofReal |M n| := by
        refine ENNReal.tsum_le_tsum fun n => iSup₂_le fun p hp => ?_
        rw [← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((hle n p hp).trans (le_abs_self _))
    _ = ENNReal.ofReal (∑' n, |M n|) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hM.abs).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Near any `w₀`, off `w₀`, the point `(τ, w)` lies off all the orbits. -/
lemma eventually_mem_diff_solutionDivisor (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (w₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] w₀, (τ, w) ∈ halfPlaneProd \ solutionDivisor m α := by
  have hk : ∀ k ∈ Icc 1 (2 * m), ∀ᶠ w in 𝓝[≠] w₀,
      (τ, w) ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1)) := fun k hk =>
    eventually_mem_diff_divisor (eigenParam_nonneg m k) (eigenParam_lt_one (mem_Icc.mp hk).2)
      hτ w₀
  filter_upwards [eventually_mem_diff_divisor hα0 hα1 hτ w₀, (eventually_all_finset _).mpr hk]
    with w hw hwk
  refine ⟨hτ, ?_⟩
  rw [mem_solutionDivisor, not_or, not_exists]
  exact ⟨hw.2, fun k ⟨hk, hk'⟩ => (hwk k hk).2 hk'⟩

/-- The periodizations of the Lambert seeds of the eigen-solutions, written with `ω^k`, satisfy
[AOS, Lemma 7.4]: a summable majorant on compact subsets off `𝒟_{ω^k}`. -/
lemma exists_majorant_eigenPeriodization (hm : 1 ≤ m) (α : ℚ) {k : ℕ} (hk : k ∈ Icc 1 (2 * m))
    (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSD : S ⊆ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1))) :
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ n : ℤ, ∀ p ∈ S,
      ‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) *
        lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))
          (e p.1 ^ n * e p.2) (e p.1)‖ ≤ M n := by
  rw [omega_pow_eq_e]
  exact exists_majorant_seedPeriodization_lambertSeed hm α (eigenParam_nonneg m k)
    (eigenParam_lt_one (mem_Icc.mp hk).2) (gaussian_bound_lambertCoeff_e α _) S hS hSD

/-- **Normal convergence** [AOS, Theorem 7.1(ii)(b)]. For `Y ∈ V` and a continuation `Φ` of its
seed, `∑_{n ∈ ℤ} sup_{w ∈ K} |x^{-2n} q^{mn²} u^{2mn} Φ(q^n u)| < ∞` for every compact `K`
avoiding the orbits `-α + ℤτ + ℤ`, `-k/d + ℤτ + ℤ`. -/
theorem solutionPeriodization_normal (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m (e α) (e τ))
    {Φ : ℂ → ℂ} (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) (K : Set ℂ) (hK : IsCompact K)
    (hKD : ∀ w ∈ K, (τ, w) ∉ solutionDivisor m α) :
    ∑' n : ℤ, ⨆ w ∈ K, (‖e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
      Φ (e τ ^ n * e w)‖₊ : ℝ≥0∞) < ∞ := by
  have hq1 : ‖e τ‖ < 1 := mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτ)
  obtain ⟨a, s, hs⟩ := exists_lambertSolution_decomposition hm (norm_e_ratCast α) (e_ne_zero τ)
    hq1 hY
  set S : Set (ℂ × ℂ) := {τ} ×ˢ K
  have hSc : IsCompact S := isCompact_singleton.prod hK
  have hSD : S ⊆ halfPlaneProd \ solutionDivisor m α := by
    rintro ⟨τ', w⟩ ⟨hτ', hw⟩
    obtain rfl : τ' = τ := hτ'
    exact ⟨hτ, hKD w hw⟩
  obtain ⟨Mx, hMx, hMxle⟩ := exists_majorant_seedPeriodization_lambertSeed (m := m) (by omega) α
    hα0 hα1 (gaussian_bound_lambertCoeff_e α α) S hSc
    fun p hp => (mem_diff_divisor_of_mem_diff_solutionDivisor (hSD hp)).1
  have hk : ∀ k : ℕ, ∃ M : ℤ → ℝ, Summable M ∧ (k ∈ Icc 1 (2 * m) → ∀ n : ℤ, ∀ p ∈ S,
      ‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) *
        lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))
          (e p.1 ^ n * e p.2) (e p.1)‖ ≤ M n) := by
    intro k
    by_cases hkI : k ∈ Icc 1 (2 * m)
    · obtain ⟨M, hM, hle⟩ := exists_majorant_eigenPeriodization (by omega) α hkI S hSc
        fun p hp => (mem_diff_divisor_of_mem_diff_solutionDivisor (hSD hp)).2 k hkI
      exact ⟨M, hM, fun _ => hle⟩
    · exact ⟨0, summable_zero, fun h => absurd h hkI⟩
  choose Mk hMk hMkle using hk
  refine tsum_iSup_nnnorm_lt_top (M := fun n => ‖a‖ * Mx n + ∑ k ∈ Icc 1 (2 * m), ‖s k‖ * Mk k n)
    ((hMx.mul_left _).add (summable_sum fun k _ => (hMk k).mul_left _)) fun n w hw => ?_
  have hp : (τ, w) ∈ S := ⟨rfl, hw⟩
  rw [seedPeriodization_summand_eq_combination hα0 hα1 (hSD hp) hΦ hs n]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans
    (sum_le_sum fun k hk => ?_)))
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMxle n _ hp) (norm_nonneg _)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hMkle k hk n _ hp) (norm_nonneg _)

/-- The periodization of the Lambert seed `Φ_{ω^k}` is holomorphic in `w` off `𝒟_{ω^k}`. -/
lemma differentiableAt_eigenPeriodization (hm : 1 ≤ m) (α : ℚ) {k : ℕ}
    (hk : k ∈ Icc 1 (2 * m)) {τ w : ℂ}
    (hτw : (τ, w) ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1))) :
    DifferentiableAt ℂ (fun w => seedPeriodization m α
      (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) τ w) w := by
  rw [omega_pow_eq_e]
  exact differentiableAt_seedPeriodization_lambertSeed hm (eigenParam_nonneg m k)
    (eigenParam_lt_one (mem_Icc.mp hk).2) (differentiableOn_lambertCoeff_e α _)
    (gaussian_bound_lambertCoeff_e α _) hτw

/-- The fibre `{w : (τ, w) ∉ 𝒟_x ∪ ⋃_k 𝒟_{ω^k}}` is open for `τ ∈ ℍ`. -/
lemma isOpen_solutionDivisor_fibre_compl (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) : IsOpen {w : ℂ | (τ, w) ∉ solutionDivisor m α} := by
  have h : {w : ℂ | (τ, w) ∉ solutionDivisor m α} =
      (fun w : ℂ => (τ, w)) ⁻¹' (halfPlaneProd \ solutionDivisor m α) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff]
    exact ⟨fun h => ⟨hτ, h⟩, fun h => h.2⟩
  rw [h]
  exact (isOpen_halfPlaneProd_diff_solutionDivisor m hα0 hα1).preimage
    (Continuous.prodMk_right τ)

/-- **Holomorphy off the orbits** [AOS, Theorem 7.1(ii)(b)]. For `Y ∈ V` and a continuation
`Φ` of its seed, the set of `w` off the orbits `-α + ℤτ + ℤ`, `-k/d + ℤτ + ℤ` is open and
`w ↦ ℰ_Y(τ, w)` is holomorphic on it. -/
theorem differentiableOn_solutionPeriodization (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) {Y : ℕ → ℂ}
    (hY : Y ∈ recurrenceSolutions m (e α) (e τ)) {Φ : ℂ → ℂ}
    (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) :
    IsOpen {w : ℂ | (τ, w) ∉ solutionDivisor m α} ∧
      DifferentiableOn ℂ (fun w => seedPeriodization m α (fun u _ => Φ u) τ w)
        {w : ℂ | (τ, w) ∉ solutionDivisor m α} := by
  have hq1 : ‖e τ‖ < 1 := mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτ)
  obtain ⟨a, s, hs⟩ := exists_lambertSolution_decomposition hm (norm_e_ratCast α) (e_ne_zero τ)
    hq1 hY
  have hO := isOpen_solutionDivisor_fibre_compl (m := m) hα0 hα1 hτ
  refine ⟨hO, fun w hw => DifferentiableAt.differentiableWithinAt ?_⟩
  have hτw : (τ, w) ∈ halfPlaneProd \ solutionDivisor m α := ⟨hτ, hw⟩
  obtain ⟨hD, hDk⟩ := mem_diff_divisor_of_mem_diff_solutionDivisor hτw
  have hG : DifferentiableAt ℂ (fun w => a * seedPeriodization m α
      (lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))) τ w +
        ∑ k ∈ Icc 1 (2 * m), s k * seedPeriodization m α
          (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) τ w) w :=
    ((differentiableAt_seedPeriodization_lambertSeed (by omega) hα0 hα1
      (differentiableOn_lambertCoeff_e α α) (gaussian_bound_lambertCoeff_e α α) hD).const_mul
        a).add (DifferentiableAt.fun_sum fun k hk =>
          ((differentiableAt_eigenPeriodization (by omega) α hk (hDk k hk)).const_mul (s k)))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hw] with w' hw'
  exact seedPeriodization_eq_combination hm hα0 hα1 ⟨hτ, hw'⟩ hΦ hs

/-- **At most simple poles** [AOS, Theorem 7.1(ii)(b)]. For `Y ∈ V`, a continuation `Φ` of its
seed and every `w₀ ∈ ℂ`, `(w - w₀) ℰ_Y(τ, w)` agrees on a punctured neighbourhood of `w₀` with
a function analytic at `w₀`. Together with `HigherDyson3.differentiableOn_solutionPeriodization`,
`w ↦ ℰ_Y(τ, w)` is meromorphic with at most simple poles, all on the orbits. -/
theorem solutionPeriodization_simple_poles (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m (e α) (e τ))
    {Φ : ℂ → ℂ} (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) (w₀ : ℂ) :
    ∃ N : ℂ → ℂ, AnalyticAt ℂ N w₀ ∧ ∀ᶠ w in 𝓝[≠] w₀,
      N w = (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w := by
  have hq1 : ‖e τ‖ < 1 := mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτ)
  obtain ⟨a, s, hs⟩ := exists_lambertSolution_decomposition hm (norm_e_ratCast α) (e_ne_zero τ)
    hq1 hY
  obtain ⟨Nx, hNx, hNxe⟩ := exists_analyticAt_sub_mul_seedPeriodization_lambertSeed
    (m := m) (by omega) α hα0 hα1 (differentiableOn_lambertCoeff_e α α)
    (gaussian_bound_lambertCoeff_e α α) hτ w₀
  have hk : ∀ k : ℕ, ∃ N : ℂ → ℂ, k ∈ Icc 1 (2 * m) → AnalyticAt ℂ N w₀ ∧
      ∀ᶠ w in 𝓝 w₀, (τ, w) ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1)) →
        N w = (w - w₀) * seedPeriodization m α
          (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) τ w := by
    intro k
    by_cases hkI : k ∈ Icc 1 (2 * m)
    · rw [omega_pow_eq_e]
      obtain ⟨N, hN, hNe⟩ := exists_analyticAt_sub_mul_seedPeriodization_lambertSeed (m := m)
        (by omega) α (eigenParam_nonneg m k) (eigenParam_lt_one (mem_Icc.mp hkI).2)
        (differentiableOn_lambertCoeff_e α _) (gaussian_bound_lambertCoeff_e α _) hτ w₀
      exact ⟨N, fun _ => ⟨hN, hNe⟩⟩
    · exact ⟨0, fun h => absurd h hkI⟩
  choose Nk hNk using hk
  refine ⟨fun w => a * Nx w + ∑ k ∈ Icc 1 (2 * m), s k * Nk k w,
    (analyticAt_const.mul hNx).add (Finset.analyticAt_fun_sum _ fun k hk =>
      analyticAt_const.mul (hNk k hk).1), ?_⟩
  have hev : ∀ᶠ w in 𝓝[≠] w₀, ∀ k ∈ Icc 1 (2 * m),
      (τ, w) ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1)) →
        Nk k w = (w - w₀) * seedPeriodization m α
          (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) τ w :=
    (eventually_all_finset _).mpr fun k hk => nhdsWithin_le_nhds (hNk k hk).2
  filter_upwards [eventually_mem_diff_solutionDivisor hα0 hα1 hτ w₀, nhdsWithin_le_nhds hNxe,
    hev] with w hw hwx hwk
  obtain ⟨hD, hDk⟩ := mem_diff_divisor_of_mem_diff_solutionDivisor hw
  rw [seedPeriodization_eq_combination hm hα0 hα1 hw hΦ hs, hwx hD, mul_add, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun k hk => by rw [hwk k hk (hDk k hk)]; ring

/-- **The twisted law** [AOS, Theorem 7.1(ii)(b), (1.10)]: for every seed `Φ`, in particular a
continuation of the seed of `Y ∈ V`, and all `a, k ∈ ℤ`,
`ℰ_Y(τ, w + aτ + k) = x^{2a} q^{-ma²} u^{-2ma} ℰ_Y(τ, w)`. -/
theorem solutionPeriodization_twisted_law (m : ℕ) (α : ℚ) (Φ : ℂ → ℂ) (τ w : ℂ) (a k : ℤ) :
    seedPeriodization m α (fun u _ => Φ u) τ (w + a * τ + k) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        seedPeriodization m α (fun u _ => Φ u) τ w :=
  seedPeriodization_twisted_law m α _ τ w a k

/-- **Theorem 7.1(ii)(b)** [AOS, Theorem 7.1(ii)(b)]. Let `m ≥ 2`, `x = e(α)` with
`α ∈ ℚ ∩ [0,1)`, `τ ∈ ℍ`, `q = e(τ)`, `Y ∈ V` and `Φ` a meromorphic continuation of the seed
`𝒢_Y`. Then `w ↦ ℰ_Y(τ, w)` converges normally on compact subsets of the complement of the orbits
`-α + ℤτ + ℤ` and `-k/d + ℤτ + ℤ` (`1 ≤ k ≤ d - 1`), is holomorphic there and meromorphic on `ℂ`
with at most simple poles (at every `w₀`, `(w - w₀) ℰ_Y(τ, w)` agrees on a punctured
neighbourhood of `w₀` with a function analytic at `w₀`), and satisfies the twisted law. -/
theorem solution_periodization (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m (e α) (e τ))
    {Φ : ℂ → ℂ} (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) :
    (∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, (τ, w) ∉ solutionDivisor m α) →
      ∑' n : ℤ, ⨆ w ∈ K, (‖e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
        e w ^ (2 * (m : ℤ) * n) * Φ (e τ ^ n * e w)‖₊ : ℝ≥0∞) < ∞) ∧
    (IsOpen {w : ℂ | (τ, w) ∉ solutionDivisor m α} ∧
      DifferentiableOn ℂ (fun w => seedPeriodization m α (fun u _ => Φ u) τ w)
        {w : ℂ | (τ, w) ∉ solutionDivisor m α}) ∧
    (∀ w₀ : ℂ, ∃ N : ℂ → ℂ, AnalyticAt ℂ N w₀ ∧ ∀ᶠ w in 𝓝[≠] w₀,
      N w = (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w) ∧
    ∀ (w : ℂ) (a k : ℤ), seedPeriodization m α (fun u _ => Φ u) τ (w + a * τ + k) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        seedPeriodization m α (fun u _ => Φ u) τ w :=
  ⟨solutionPeriodization_normal hm hα0 hα1 hτ hY hΦ,
    differentiableOn_solutionPeriodization hm hα0 hα1 hτ hY hΦ,
    solutionPeriodization_simple_poles hm hα0 hα1 hτ hY hΦ,
    fun w a k => solutionPeriodization_twisted_law m α Φ τ w a k⟩

end HigherDyson3
