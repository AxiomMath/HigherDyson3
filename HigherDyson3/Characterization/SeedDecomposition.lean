/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Orbits
public import HigherDyson3.Characterization.RatioEstimates
public import HigherDyson3.Characterization.SeedContinuation
public import HigherDyson3.Lambert.Convergence

/-!
# Decomposition of a solution seed into Lambert seeds

Let `m ≥ 2`, `x = e(α)` and `0 < |q| < 1`. Every `Y ∈ V` is `a S(x) + ∑_{k=1}^{d-1} s_k Z^{(k)}`
[AOS, Lemma 7.3(c)], so on the unit disc its seed is the combination
`Ψ = a Φ_x + ∑_k s_k Φ_{ω^k}` of the Lambert seeds `Φ_c(u) = x⁻² ∑_i b_i(c) / (1 - c q^i u)`
[AOS, (7.15)]. Every meromorphic continuation `Φ` of the seed agrees with `Ψ` off the pole set
`{x⁻¹ q^{-i}, ω^{-k} q^{-i}}` by the identity theorem: both are holomorphic on the complement
of this countable closed set, which is connected and contains the unit disc. Consequently, off
the orbits `𝒟_x ∪ ⋃_k 𝒟_{ω^k}`, the periodization of `Φ` is the corresponding combination
`a ℰ_{Φ_x} + ∑_k s_k ℰ_{Φ_{ω^k}}` of periodizations of Lambert seeds [AOS, (7.16)].

## Main results

* `HigherDyson3.exists_lambertSolution_decomposition`: the decomposition of `Y`.
* `HigherDyson3.eqOn_seedContinuation_combination`: `Φ = Ψ` off the pole set.
* `HigherDyson3.seedPeriodization_eq_combination`: the decomposition of `ℰ_Y` off the orbits.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ}

/-- **The decomposition** `Y = a S(x) + ∑_{k=1}^{d-1} s_k S(ω^k)` of a solution of the
recurrence [AOS, Lemma 7.3(c)], with `S(x) = X(x;q)/G_d(x;q)`. -/
theorem exists_lambertSolution_decomposition (hm : 2 ≤ m) {x q : ℂ} (hx : ‖x‖ = 1)
    (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m x q) :
    ∃ (a : ℂ) (s : ℕ → ℂ), ∀ j : ℕ, Y j = a * lambertSolution m x x q j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m x (omega m ^ k) q j := by
  obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hY
  obtain ⟨s, hs⟩ := exists_decomposition hm hx hq0 hq1 hγ
  refine ⟨if Cx m x = 0 then 0 else γ, s, fun j => ?_⟩
  rw [hs]
  by_cases h : Cx m x = 0 <;>
    simp [h, Finset.sum_apply, eigenSolution, lambertSolution_self hm hx hq1]

/-- On the unit disc, the seed of `Y = a S(x) + ∑_k s_k S(ω^k)` is the combination
`a Φ_x + ∑_k s_k Φ_{ω^k}` of Lambert seeds [AOS, (7.15)]. -/
theorem sequenceSeed_eq_combination {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {Y : ℕ → ℂ} {a : ℂ} {s : ℕ → ℂ}
    (hY : ∀ j : ℕ, Y j = a * lambertSolution m x x q j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m x (omega m ^ k) q j)
    {u : ℂ} (hu : ‖u‖ < 1) :
    sequenceSeed x Y u = a * lambertSeed x x (lambertCoeff m x x) u q +
      ∑ k ∈ Icc 1 (2 * m), s k *
        lambertSeed x (omega m ^ k) (lambertCoeff m x (omega m ^ k)) u q := by
  have h1 := summable_lambertSolution_mul (m := m) hx hx hq0 hq1 hu
  have h2 := fun k => summable_lambertSolution_mul (m := m) hx (norm_omega_pow m k) hq0 hq1 hu
  simp only [← sequenceSeed_lambertSolution hx hx hq1 hu,
    ← sequenceSeed_lambertSolution hx (norm_omega_pow m _) hq1 hu, sequenceSeed]
  have hY' : (fun j : ℕ => Y j * (x * u) ^ j) = fun j : ℕ =>
      a * (lambertSolution m x x q j * (x * u) ^ j) + ∑ k ∈ Icc 1 (2 * m),
        s k * (lambertSolution m x (omega m ^ k) q j * (x * u) ^ j) := by
    funext j
    rw [hY, add_mul, sum_mul]
    congr 1
    · ring
    · exact sum_congr rfl fun k _ => by ring
  rw [hY', Summable.tsum_add (h1.mul_left a)
      (summable_sum (s := Icc 1 (2 * m)) fun k _ => (h2 k).mul_left (s k)),
    Summable.tsum_finsetSum fun k _ => (h2 k).mul_left (s k), tsum_mul_left, mul_add, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun k _ => by rw [tsum_mul_left]; ring

/-- The combination `a Φ_x + ∑_k s_k Φ_{ω^k}` is holomorphic off the pole set. -/
theorem differentiableOn_lambertSeed_combination {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (a : ℂ) (s : ℕ → ℂ) :
    DifferentiableOn ℂ (fun u => a * lambertSeed x x (lambertCoeff m x x) u q +
      ∑ k ∈ Icc 1 (2 * m), s k *
        lambertSeed x (omega m ^ k) (lambertCoeff m x (omega m ^ k)) u q)
      (seedPoleSet m x q)ᶜ := by
  intro u hu
  refine DifferentiableAt.differentiableWithinAt ?_
  have hdiff : ∀ c : ℂ, ‖c‖ = 1 → (∀ i : ℕ, c * q ^ i * u ≠ 1) →
      DifferentiableAt ℂ (fun u => lambertSeed x c (lambertCoeff m x c) u q) u :=
    fun c hc hcu => differentiableAt_lambertSeed (summable_norm_lambertCoeff hx hc hq1) hq1 hcu
  refine ((hdiff x hx fun i hi => hu ?_).const_mul a).add
    (DifferentiableAt.fun_sum fun k hk =>
      ((hdiff _ (norm_omega_pow m k) fun i hi => hu ?_).const_mul (s k)))
  · exact Or.inl ⟨i, (mul_pow_mul_eq_one_iff (ne_zero_of_norm_eq_one hx) hq0 i u).mp hi⟩
  · exact Or.inr ⟨i, k, hk, (mul_pow_mul_eq_one_iff
      (ne_zero_of_norm_eq_one (norm_omega_pow m k)) hq0 i u).mp hi⟩

/-- **The continuation is the Lambert combination off the pole set.** If `Φ` continues the
seed of `Y = a S(x) + ∑_k s_k S(ω^k)`, then `Φ = a Φ_x + ∑_k s_k Φ_{ω^k}` on the complement of
`{x⁻¹ q^{-i}, ω^{-k} q^{-i}}`. -/
theorem eqOn_seedContinuation_combination {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) {Y : ℕ → ℂ} {Φ : ℂ → ℂ} (hΦ : IsSeedContinuation m x q Y Φ) {a : ℂ}
    {s : ℕ → ℂ}
    (hY : ∀ j : ℕ, Y j = a * lambertSolution m x x q j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m x (omega m ^ k) q j) :
    Set.EqOn Φ (fun u => a * lambertSeed x x (lambertCoeff m x x) u q +
      ∑ k ∈ Icc 1 (2 * m), s k *
        lambertSeed x (omega m ^ k) (lambertCoeff m x (omega m ^ k)) u q)
      (seedPoleSet m x q)ᶜ := by
  have hU : IsOpen (seedPoleSet m x q)ᶜ := (isClosed_seedPoleSet hx hq0 hq1).isOpen_compl
  have hball := ball_subset_compl_seedPoleSet (m := m) hx hq0 hq1
  refine (hΦ.1.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    ((differentiableOn_lambertSeed_combination hx hq0 hq1 a s).analyticOnNhd hU)
    (isPreconnected_compl_seedPoleSet m x q) (hball (Metric.mem_ball_self one_pos)) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with u hu
  rw [mem_ball_zero_iff] at hu
  rw [hΦ.2.1 u hu, sequenceSeed_eq_combination hx hq0 hq1 hY hu]

/-- The Lambert coefficients `b_i(e(β))` satisfy the hypotheses of [AOS, Lemma 7.4]. -/
lemma differentiableOn_lambertCoeff_e (α β : ℚ) (i : ℕ) :
    DifferentiableOn ℂ (lambertCoeff m (e α) (e β) i) (Metric.ball 0 1) :=
  differentiableOn_lambertCoeff _ (norm_e_ratCast β).le i

/-- The Gaussian bound of the Lambert coefficients `b_i(e(β))`. -/
lemma gaussian_bound_lambertCoeff_e (α β : ℚ) :
    ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q →
      ‖lambertCoeff m (e α) (e β) i q‖ ≤ B * ‖q‖ ^ (i ^ 2) :=
  exists_gaussian_bound_lambertCoeff m (norm_e_ratCast α) (norm_e_ratCast β)

/-- Off `𝒟_c`, the series of the periodization of the Lambert seed `Φ_c` converges
absolutely. -/
lemma summable_seedPeriodization_lambertCoeff (hm : 1 ≤ m) (α : ℚ) {β : ℚ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor β) :
    Summable fun n : ℤ => e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
      lambertSeed (e α) (e β) (lambertCoeff m (e α) (e β)) (e τ ^ n * e w) (e τ) := by
  obtain ⟨M, hM, hle⟩ := exists_majorant_seedPeriodization_lambertSeed hm α hβ0 hβ1
    (gaussian_bound_lambertCoeff_e α β) {(τ, w)} isCompact_singleton
    (Set.singleton_subset_iff.mpr hτw)
  exact Summable.of_norm_bounded hM fun n => hle n (τ, w) rfl

lemma mem_diff_divisor_of_mem_diff_solutionDivisor {α : ℚ} {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd \ solutionDivisor m α) :
    p ∈ halfPlaneProd \ divisor α ∧
      ∀ k ∈ Icc 1 (2 * m), p ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1)) := by
  obtain ⟨h1, h2⟩ := not_mem_divisor_of_not_mem_solutionDivisor hp.2
  exact ⟨⟨hp.1, h1⟩, fun k hk => ⟨hp.1, h2 k hk⟩⟩

/-- Off the orbits, the `n`-th summand of `ℰ_Y` is the combination of the `n`-th summands of the
periodizations of the Lambert seeds. -/
theorem seedPeriodization_summand_eq_combination {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ solutionDivisor m α) {Y : ℕ → ℂ}
    {Φ : ℂ → ℂ} (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) {a : ℂ} {s : ℕ → ℂ}
    (hY : ∀ j : ℕ, Y j = a * lambertSolution m (e α) (e α) (e τ) j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m (e α) (omega m ^ k) (e τ) j) (n : ℤ) :
    e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) * Φ (e τ ^ n * e w) =
      a * (e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
        lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α)) (e τ ^ n * e w) (e τ)) +
      ∑ k ∈ Icc 1 (2 * m), s k * (e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
        e w ^ (2 * (m : ℤ) * n) * lambertSeed (e α) (omega m ^ k)
          (lambertCoeff m (e α) (omega m ^ k)) (e τ ^ n * e w) (e τ)) := by
  have hq1 : ‖e τ‖ < 1 := mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτw.1)
  rw [eqOn_seedContinuation_combination (norm_e_ratCast α) (e_ne_zero τ) hq1 hΦ hY
    (not_mem_seedPoleSet hα0 hα1 hτw n), mul_add, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun k _ => by ring

/-- **The decomposition of the periodization** [AOS, (7.16)]. If `Φ` continues the seed of
`Y = a S(x) + ∑_k s_k S(ω^k)` at `q = e(τ)`, then off the orbits
`ℰ_Y(τ,w) = a ℰ_{Φ_x}(τ,w) + ∑_k s_k ℰ_{Φ_{ω^k}}(τ,w)`. -/
theorem seedPeriodization_eq_combination (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ solutionDivisor m α) {Y : ℕ → ℂ}
    {Φ : ℂ → ℂ} (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) {a : ℂ} {s : ℕ → ℂ}
    (hY : ∀ j : ℕ, Y j = a * lambertSolution m (e α) (e α) (e τ) j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m (e α) (omega m ^ k) (e τ) j) :
    seedPeriodization m α (fun u _ => Φ u) τ w =
      a * seedPeriodization m α (lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))) τ w +
        ∑ k ∈ Icc 1 (2 * m), s k * seedPeriodization m α
          (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) τ w := by
  obtain ⟨hD, hDk⟩ := mem_diff_divisor_of_mem_diff_solutionDivisor hτw
  have h1 := summable_seedPeriodization_lambertCoeff (m := m) (by omega) α hα0 hα1 hD
  have h2 : ∀ k ∈ Icc 1 (2 * m), Summable fun n : ℤ => e α ^ (-2 * n) *
      e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
      lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))
        (e τ ^ n * e w) (e τ) := by
    intro k hk
    rw [omega_pow_eq_e]
    exact summable_seedPeriodization_lambertCoeff (by omega) α (eigenParam_nonneg m k)
      (eigenParam_lt_one (mem_Icc.mp hk).2) (hDk k hk)
  have hL := seedPeriodization_summand_eq_combination hα0 hα1 hτw hΦ hY
  unfold seedPeriodization
  simp only
  rw [tsum_congr hL, (h1.mul_left a).tsum_add (summable_sum fun k hk => (h2 k hk).mul_left (s k)),
    Summable.tsum_finsetSum fun k hk => (h2 k hk).mul_left (s k), tsum_mul_left]
  congr 1
  exact sum_congr rfl fun k _ => tsum_mul_left

end HigherDyson3
