/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.CoefficientHolomorphy
public import HigherDyson3.Characterization.SolutionPeriodization
public import HigherDyson3.Lambert.JointPoles

/-!
# Holomorphic families of solutions

Let `m ≥ 2` and `x = e(α)` with `α ∈ ℚ ∩ [0,1)`. Suppose `Y(q) ∈ V_{γ(q)}` for `q` in an open
set `Ω ⊆ {0 < |q| < 1}`, with initial values `Y_0, …, Y_{d-2}` and parameter `γ` holomorphic on
`Ω`, and let `Φ(q, ·)` be continuations of the seeds of `Y(q)`. With
`Ω̃ = {τ ∈ ℍ : e(τ) ∈ Ω}`, the periodization `ℰ_Y(τ,w)` converges normally on compact subsets of
`(Ω̃ × ℂ) \ (𝒟_x ∪ ⋃_k 𝒟_{ω^k})` and extends jointly meromorphically to `Ω̃ × ℂ` with at most
simple poles on these orbits [AOS, Theorem 7.1(ii)(c)].

The coefficients of `Y(q) = γ'(q) S(x) + ∑_k s_k(q) Z^{(k)}` are holomorphic on `Ω`
(`HigherDyson3.exists_holomorphic_decomposition`), so
`ℰ_Y = γ'(q) ℰ_{Φ_x} + ∑_k s_k(q) ℰ_{Φ_{ω^k}}` off the orbits is a finite sum of products of
holomorphic functions of `τ` with periodizations of Lambert seeds, to which
[AOS, Lemma 7.4] applies jointly in `(τ, w)`.

## Main results

* `HigherDyson3.solutionFamily_normal`: normal convergence on compact sets.
* `HigherDyson3.differentiableOn_solutionFamily`: joint holomorphy off the orbits.
* `HigherDyson3.solutionFamily_simple_poles`: at most simple poles along each orbit.
-/

public section

noncomputable section

open Complex Finset Filter Topology
open scoped ENNReal NNReal

namespace HigherDyson3

variable {m : ℕ} {α : ℚ}

/-- The domain `Ω̃ × ℂ = {(τ, w) : τ ∈ ℍ, e(τ) ∈ Ω}` is open. -/
lemma isOpen_familyDomain {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsOpen {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} :=
  (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).inter
    (hΩ.preimage (e_differentiable.continuous.comp continuous_fst))

/-- On `(Ω̃ × ℂ) \ (𝒟_x ∪ ⋃_k 𝒟_{ω^k})`, the summands of `ℰ_Y` decompose with coefficients
holomorphic on `Ω`. -/
theorem exists_family_summand_decomposition (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {Ω : Set ℂ} (hΩsub : Ω ⊆ {q | 0 < ‖q‖ ∧ ‖q‖ < 1}) {Y : ℂ → ℕ → ℂ}
    {γ : ℂ → ℂ} (hYmem : ∀ q ∈ Ω, Y q ∈ recurrenceFamily m (e α) q (γ q))
    (hYhol : ∀ j < 2 * m, DifferentiableOn ℂ (fun q => Y q j) Ω)
    (hγ : DifferentiableOn ℂ γ Ω) {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ q ∈ Ω, IsSeedContinuation m (e α) q (Y q) (Φ q)) :
    ∃ g : ℂ → ℂ, ∃ s : ℂ → ℕ → ℂ, DifferentiableOn ℂ g Ω ∧
      (∀ k, DifferentiableOn ℂ (fun q => s q k) Ω) ∧
      ∀ p ∈ {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α,
        (∀ n : ℤ, e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) *
          Φ (e p.1) (e p.1 ^ n * e p.2) =
            g (e p.1) * (e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
              e p.2 ^ (2 * (m : ℤ) * n) * lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))
                (e p.1 ^ n * e p.2) (e p.1)) +
            ∑ k ∈ Icc 1 (2 * m), s (e p.1) k * (e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
              e p.2 ^ (2 * (m : ℤ) * n) * lambertSeed (e α) (omega m ^ k)
                (lambertCoeff m (e α) (omega m ^ k)) (e p.1 ^ n * e p.2) (e p.1))) ∧
        seedPeriodization m α (fun u q => Φ q u) p.1 p.2 =
          g (e p.1) * seedPeriodization m α
            (lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))) p.1 p.2 +
          ∑ k ∈ Icc 1 (2 * m), s (e p.1) k * seedPeriodization m α
            (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) p.1 p.2 := by
  obtain ⟨s, hsd, hs⟩ := exists_holomorphic_decomposition hm (norm_e_ratCast α) hΩsub hYmem
    hYhol hγ
  refine ⟨fun q => if Cx m (e α) = 0 then 0 else γ q, s, ?_, hsd, fun p hp => ?_⟩
  · by_cases h : Cx m (e α) = 0
    · simp only [h, ite_true]; exact differentiableOn_const _
    · simp only [h, ite_false]; exact hγ
  have hτw : p ∈ halfPlaneProd \ solutionDivisor m α := ⟨hp.1.1, hp.2⟩
  have hp' : (p.1, p.2) ∈ halfPlaneProd \ solutionDivisor m α := hτw
  have hΦp := hΦ (e p.1) hp.1.2
  have hsp := hs (e p.1) hp.1.2
  exact ⟨seedPeriodization_summand_eq_combination hα0 hα1 hp' hΦp hsp,
    seedPeriodization_eq_combination hm hα0 hα1 hp' hΦp hsp⟩

/-- **Normal convergence for holomorphic families** [AOS, Theorem 7.1(ii)(c)]. On every compact
`K ⊆ (Ω̃ × ℂ) \ (𝒟_x ∪ ⋃_k 𝒟_{ω^k})`,
`∑_{n ∈ ℤ} sup_K |x^{-2n} q^{mn²} u^{2mn} Φ(q; q^n u)| < ∞`. -/
theorem solutionFamily_normal (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {Ω : Set ℂ} (hΩsub : Ω ⊆ {q | 0 < ‖q‖ ∧ ‖q‖ < 1}) {Y : ℂ → ℕ → ℂ}
    {γ : ℂ → ℂ} (hYmem : ∀ q ∈ Ω, Y q ∈ recurrenceFamily m (e α) q (γ q))
    (hYhol : ∀ j < 2 * m, DifferentiableOn ℂ (fun q => Y q j) Ω)
    (hγ : DifferentiableOn ℂ γ Ω) {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ q ∈ Ω, IsSeedContinuation m (e α) q (Y q) (Φ q)) (K : Set (ℂ × ℂ))
    (hK : IsCompact K) (hKD : K ⊆ {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α) :
    ∑' n : ℤ, ⨆ p ∈ K, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
      e p.2 ^ (2 * (m : ℤ) * n) * Φ (e p.1) (e p.1 ^ n * e p.2)‖₊ : ℝ≥0∞) < ∞ := by
  obtain ⟨g, s, hg, hsd, hdec⟩ := exists_family_summand_decomposition hm hα0 hα1 hΩsub hYmem
    hYhol hγ hΦ
  have hKH : K ⊆ halfPlaneProd \ solutionDivisor m α := fun p hp => ⟨(hKD hp).1.1, (hKD hp).2⟩
  have hcont : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f Ω →
      ∃ C : ℝ, ∀ p ∈ K, ‖f (e p.1)‖ ≤ C := fun {f} hf =>
    hK.exists_bound_of_continuousOn (hf.continuousOn.comp
      (e_differentiable.continuous.comp continuous_fst).continuousOn fun p hp => (hKD hp).1.2)
  obtain ⟨A, hA⟩ := hcont hg
  choose C hC using fun k => hcont (hsd k)
  obtain ⟨Mx, hMx, hMxle⟩ := exists_majorant_seedPeriodization_lambertSeed (m := m) (by omega) α
    hα0 hα1 (gaussian_bound_lambertCoeff_e α α) K hK
    fun p hp => (mem_diff_divisor_of_mem_diff_solutionDivisor (hKH hp)).1
  have hk : ∀ k : ℕ, ∃ M : ℤ → ℝ, Summable M ∧ (k ∈ Icc 1 (2 * m) → ∀ n : ℤ, ∀ p ∈ K,
      ‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) *
        lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))
          (e p.1 ^ n * e p.2) (e p.1)‖ ≤ M n) := by
    intro k
    by_cases hkI : k ∈ Icc 1 (2 * m)
    · obtain ⟨M, hM, hle⟩ := exists_majorant_eigenPeriodization (by omega) α hkI K hK
        fun p hp => (mem_diff_divisor_of_mem_diff_solutionDivisor (hKH hp)).2 k hkI
      exact ⟨M, hM, fun _ => hle⟩
    · exact ⟨0, summable_zero, fun h => absurd h hkI⟩
  choose Mk hMk hMkle using hk
  refine tsum_iSup_nnnorm_lt_top (M := fun n => |A| * |Mx n| +
      ∑ k ∈ Icc 1 (2 * m), |C k| * |Mk k n|)
    ((hMx.abs.mul_left _).add (summable_sum fun k _ => (hMk k).abs.mul_left _)) fun n p hp => ?_
  rw [(hdec p (hKD hp)).1 n]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans
    (sum_le_sum fun k hk => ?_)))
  · rw [norm_mul]
    exact mul_le_mul ((hA p hp).trans (le_abs_self _)) ((hMxle n p hp).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  · rw [norm_mul]
    exact mul_le_mul ((hC k p hp).trans (le_abs_self _))
      ((hMkle k hk n p hp).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)

/-- A function holomorphic on `Ω` composed with `e ∘ fst` is holomorphic at points of
`Ω̃ × ℂ`. -/
lemma differentiableAt_comp_e_fst_of_mem {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {p : ℂ × ℂ} (hp : e p.1 ∈ Ω) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => f (e p.1)) p :=
  (hf.differentiableAt (hΩ.mem_nhds hp)).comp p ((e_differentiable _).comp _ differentiableAt_fst)

/-- **Joint holomorphy for holomorphic families** [AOS, Theorem 7.1(ii)(c)]: `ℰ_Y` is
holomorphic on `(Ω̃ × ℂ) \ (𝒟_x ∪ ⋃_k 𝒟_{ω^k})`, an open set. -/
theorem differentiableOn_solutionFamily (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩsub : Ω ⊆ {q | 0 < ‖q‖ ∧ ‖q‖ < 1}) {Y : ℂ → ℕ → ℂ}
    {γ : ℂ → ℂ} (hYmem : ∀ q ∈ Ω, Y q ∈ recurrenceFamily m (e α) q (γ q))
    (hYhol : ∀ j < 2 * m, DifferentiableOn ℂ (fun q => Y q j) Ω)
    (hγ : DifferentiableOn ℂ γ Ω) {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ q ∈ Ω, IsSeedContinuation m (e α) q (Y q) (Φ q)) :
    IsOpen ({p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => seedPeriodization m α (fun u q => Φ q u) p.1 p.2)
        ({p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α) := by
  obtain ⟨g, s, hg, hsd, hdec⟩ := exists_family_summand_decomposition hm hα0 hα1 hΩsub hYmem
    hYhol hγ hΦ
  have hU : IsOpen ({p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α) := by
    have : {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α =
        {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} ∩ (halfPlaneProd \ solutionDivisor m α) := by
      ext p
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact (isOpen_familyDomain hΩ).inter (isOpen_halfPlaneProd_diff_solutionDivisor m hα0 hα1)
  refine ⟨hU, fun p hp => DifferentiableAt.differentiableWithinAt ?_⟩
  have hpH : p ∈ halfPlaneProd \ solutionDivisor m α := ⟨hp.1.1, hp.2⟩
  obtain ⟨hD, hDk⟩ := mem_diff_divisor_of_mem_diff_solutionDivisor hpH
  obtain ⟨hUx, hDx⟩ := differentiableOn_seedPeriodization_lambertSeed (m := m) (by omega) α
    hα0 hα1 (differentiableOn_lambertCoeff_e α α) (gaussian_bound_lambertCoeff_e α α)
  have hDk' : ∀ k ∈ Icc 1 (2 * m), DifferentiableAt ℂ (fun p : ℂ × ℂ => seedPeriodization m α
      (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) p.1 p.2) p := by
    intro k hk
    rw [omega_pow_eq_e]
    obtain ⟨hUk, hDk''⟩ := differentiableOn_seedPeriodization_lambertSeed (m := m) (by omega) α
      (eigenParam_nonneg m k) (eigenParam_lt_one (mem_Icc.mp hk).2)
      (differentiableOn_lambertCoeff_e α _) (gaussian_bound_lambertCoeff_e α _)
    exact hDk''.differentiableAt (hUk.mem_nhds (hDk k hk))
  have hG : DifferentiableAt ℂ (fun p : ℂ × ℂ => g (e p.1) * seedPeriodization m α
      (lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))) p.1 p.2 +
      ∑ k ∈ Icc 1 (2 * m), s (e p.1) k * seedPeriodization m α
        (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) p.1 p.2) p :=
    ((differentiableAt_comp_e_fst_of_mem hΩ hg hp.1.2).mul
      (hDx.differentiableAt (hUx.mem_nhds hD))).add (DifferentiableAt.fun_sum fun k hk =>
        (differentiableAt_comp_e_fst_of_mem hΩ (hsd k) hp.1.2).mul (hDk' k hk))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hp] with p' hp'
  exact (hdec p' hp').2

/-- **At most simple poles for holomorphic families** [AOS, Theorem 7.1(ii)(c)]. Let `β = α` or
`β = k/d` with `1 ≤ k ≤ d - 1`, and let `p₀ = (τ₀, w₀)` lie on the component
`L_{a,b} = {w = -β + aτ + b}` of `𝒟_{e(β)}` with `τ₀ ∈ Ω̃`. Then near `p₀`, off the orbits,
`(w + β - aτ - b) ℰ_Y(τ,w)` agrees with a function holomorphic near `p₀`. Together with
`HigherDyson3.differentiableOn_solutionFamily`, `ℰ_Y` is jointly meromorphic on `Ω̃ × ℂ` with at
most simple poles along the orbits. -/
theorem solutionFamily_simple_poles (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩsub : Ω ⊆ {q | 0 < ‖q‖ ∧ ‖q‖ < 1}) {Y : ℂ → ℕ → ℂ}
    {γ : ℂ → ℂ} (hYmem : ∀ q ∈ Ω, Y q ∈ recurrenceFamily m (e α) q (γ q))
    (hYhol : ∀ j < 2 * m, DifferentiableOn ℂ (fun q => Y q j) Ω)
    (hγ : DifferentiableOn ℂ γ Ω) {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ q ∈ Ω, IsSeedContinuation m (e α) q (Y q) (Φ q)) {β : ℚ}
    (hβ : β = α ∨ ∃ k ∈ Icc 1 (2 * m), β = (k : ℚ) / (2 * m + 1)) {a b : ℤ} {p₀ : ℂ × ℂ}
    (hp₀ : p₀ ∈ divisorComponent β a b) (hp₀Ω : e p₀.1 ∈ Ω) :
    ∃ N : ℂ × ℂ → ℂ, (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ N p) ∧
      ∀ᶠ p in 𝓝 p₀, p ∉ solutionDivisor m α →
        N p = (p.2 + β - a * p.1 - b) * seedPeriodization m α (fun u q => Φ q u) p.1 p.2 := by
  obtain ⟨g, s, hg, hsd, hdec⟩ := exists_family_summand_decomposition hm hα0 hα1 hΩsub hYmem
    hYhol hγ hΦ
  have hβ01 : 0 ≤ β ∧ β < 1 := by
    rcases hβ with rfl | ⟨k, hk, rfl⟩
    · exact ⟨hα0, hα1⟩
    · exact ⟨eigenParam_nonneg m k, eigenParam_lt_one (mem_Icc.mp hk).2⟩
  obtain ⟨Nx, hNxd, hNxe⟩ := exists_differentiableAt_sub_mul_seedPeriodization_lambertSeed
    (m := m) (by omega) α hα0 hα1 (differentiableOn_lambertCoeff_e α α)
    (gaussian_bound_lambertCoeff_e α α) hβ01.1 hβ01.2 hp₀
  have hk : ∀ k : ℕ, ∃ N : ℂ × ℂ → ℂ, k ∈ Icc 1 (2 * m) →
      (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ N p) ∧
      ∀ᶠ p in 𝓝 p₀, p ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1)) →
        N p = (p.2 + β - a * p.1 - b) * seedPeriodization m α
          (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) p.1 p.2 := by
    intro k
    by_cases hkI : k ∈ Icc 1 (2 * m)
    · rw [omega_pow_eq_e]
      obtain ⟨N, hNd, hNe⟩ := exists_differentiableAt_sub_mul_seedPeriodization_lambertSeed
        (m := m) (by omega) α (eigenParam_nonneg m k) (eigenParam_lt_one (mem_Icc.mp hkI).2)
        (differentiableOn_lambertCoeff_e α _) (gaussian_bound_lambertCoeff_e α _) hβ01.1
        hβ01.2 hp₀
      exact ⟨N, fun _ => ⟨hNd, hNe⟩⟩
    · exact ⟨0, fun h => absurd h hkI⟩
  choose Nk hNk using hk
  have hDom := isOpen_familyDomain hΩ
  have hp₀D : p₀ ∈ {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} := ⟨hp₀.1, hp₀Ω⟩
  refine ⟨fun p => g (e p.1) * Nx p + ∑ k ∈ Icc 1 (2 * m), s (e p.1) k * Nk k p, ?_, ?_⟩
  · filter_upwards [hDom.mem_nhds hp₀D, hNxd, (eventually_all_finset _).mpr fun k hk =>
      (hNk k hk).1] with p hp hpx hpk
    exact ((differentiableAt_comp_e_fst_of_mem hΩ hg hp.2).mul hpx).add
      (DifferentiableAt.fun_sum fun k hk =>
        (differentiableAt_comp_e_fst_of_mem hΩ (hsd k) hp.2).mul (hpk k hk))
  · filter_upwards [hDom.mem_nhds hp₀D, hNxe, (eventually_all_finset _).mpr fun k hk =>
      (hNk k hk).2] with p hp hpx hpk hpS
    have hpH : p ∈ halfPlaneProd \ solutionDivisor m α := ⟨hp.1, hpS⟩
    obtain ⟨hD, hDk⟩ := mem_diff_divisor_of_mem_diff_solutionDivisor hpH
    rw [(hdec p ⟨hp, hpS⟩).2, hpx hD, mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun k hk => by rw [hpk k hk (hDk k hk)]; ring

/-- **Theorem 7.1(ii)(c)** [AOS, Theorem 7.1(ii)(c)]. Let `m ≥ 2`, `x = e(α)` with
`α ∈ ℚ ∩ [0,1)`, `Ω ⊆ {0 < |q| < 1}` open, `Y(q) ∈ V_{γ(q)}` for `q ∈ Ω` with `Y_0, …, Y_{d-2}`
and `γ` holomorphic on `Ω`, and `Φ(q, ·)` continuations of the seeds of `Y(q)`. With
`Ω̃ = {τ ∈ ℍ : e(τ) ∈ Ω}`, `ℰ_Y` converges normally on compact subsets of
`(Ω̃ × ℂ) \ (𝒟_x ∪ ⋃_k 𝒟_{ω^k})`, is holomorphic there, and has at most simple poles along these
orbits: near each point `p₀` of a component `L_{a,b} = {w = -β + aτ + b}` of one of the orbits,
`β ∈ {α} ∪ {k/d}`, `(w + β - aτ - b) ℰ_Y` agrees off the orbits with a function holomorphic near
`p₀`. -/
theorem solution_periodization_family (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hΩsub : Ω ⊆ {q | 0 < ‖q‖ ∧ ‖q‖ < 1}) {Y : ℂ → ℕ → ℂ}
    {γ : ℂ → ℂ} (hYmem : ∀ q ∈ Ω, Y q ∈ recurrenceFamily m (e α) q (γ q))
    (hYhol : ∀ j < 2 * m, DifferentiableOn ℂ (fun q => Y q j) Ω)
    (hγ : DifferentiableOn ℂ γ Ω) {Φ : ℂ → ℂ → ℂ}
    (hΦ : ∀ q ∈ Ω, IsSeedContinuation m (e α) q (Y q) (Φ q)) :
    (∀ K : Set (ℂ × ℂ), IsCompact K →
      K ⊆ {p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α →
      ∑' n : ℤ, ⨆ p ∈ K, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * n) * Φ (e p.1) (e p.1 ^ n * e p.2)‖₊ : ℝ≥0∞) < ∞) ∧
    (IsOpen ({p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => seedPeriodization m α (fun u q => Φ q u) p.1 p.2)
        ({p : ℂ × ℂ | 0 < p.1.im ∧ e p.1 ∈ Ω} \ solutionDivisor m α)) ∧
    ∀ β : ℚ, (β = α ∨ ∃ k ∈ Icc 1 (2 * m), β = (k : ℚ) / (2 * m + 1)) →
      ∀ (a b : ℤ) (p₀ : ℂ × ℂ), p₀ ∈ divisorComponent β a b → e p₀.1 ∈ Ω →
        ∃ N : ℂ × ℂ → ℂ, (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ N p) ∧
          ∀ᶠ p in 𝓝 p₀, p ∉ solutionDivisor m α →
            N p = (p.2 + β - a * p.1 - b) *
              seedPeriodization m α (fun u q => Φ q u) p.1 p.2 :=
  ⟨fun K hK hKD => solutionFamily_normal hm hα0 hα1 hΩsub hYmem hYhol hγ hΦ K hK hKD,
    differentiableOn_solutionFamily hm hα0 hα1 hΩ hΩsub hYmem hYhol hγ hΦ,
    fun _ hβ _ _ _ hp₀ hp₀Ω =>
      solutionFamily_simple_poles hm hα0 hα1 hΩ hΩsub hYmem hYhol hγ hΦ hβ hp₀ hp₀Ω⟩

end HigherDyson3
