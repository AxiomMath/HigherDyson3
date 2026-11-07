/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.SolutionSpace

/-!
# The seed of a solution of the recurrence

For `m ≥ 2`, `|x| = 1`, `0 < |q| < 1` and `Y ∈ V`, the seed `𝒢_Y(u) = x^{-2} ∑_j Y_j (xu)^j`
converges for `|u| < 1` and extends to a meromorphic function on `ℂ` with at most simple poles,
all in `{x^{-1} q^{-i}, ω^{-k} q^{-i} : i ≥ 0, 1 ≤ k ≤ d - 1}` [AOS, Theorem 7.1(ii)(a)].

The proof decomposes `Y = γ' X/G_d + ∑_k s_k Z^{(k)}` [AOS, Lemma 7.3(c)] and continues the seed
of each summand by its Lambert-type seed [AOS, Lemma 7.2(d)], see [AOS, (7.15)].

## Main results

* `HigherDyson3.summable_seed_of_mem`: convergence of `𝒢_Y` on `|u| < 1`.
* `HigherDyson3.exists_isSeedContinuation`: the meromorphic continuation.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ} {x c q : ℂ}

/-- The Lambert-type solutions are bounded: `|S_j(c)| ≤ 1 + B'_{|q|}/(1 - |q|)` for `j ≥ 0`. -/
theorem norm_lambertSolution_le (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (j : ℕ) : ‖lambertSolution m x c q j‖ ≤ 1 + hRatioBound m ‖q‖ / (1 - ‖q‖) := by
  have hl := div_ne_zero_of_norm hx hc
  have h := norm_lambertSolution_sub_le (m := m) (norm_nonneg q) hq1 hx hc hq0 le_rfl j
  have hB : 0 ≤ hRatioBound m ‖q‖ / (1 - ‖q‖) :=
    div_nonneg (hRatioBound_nonneg (norm_nonneg q) hq1) (by linarith)
  have hp : ‖q‖ ^ (j + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hq1.le
  have hj : lambertSolution m x c q j =
      (c / x) ^ j * ((c / x) ^ (-(j : ℤ)) * lambertSolution m x c q j - 1) + (c / x) ^ j := by
    rw [mul_sub, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hl, add_neg_cancel, zpow_zero,
      one_mul, mul_one, sub_add_cancel]
  rw [hj]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_pow, norm_div_eq_one hx hc, one_pow, one_mul]
  nlinarith

/-- The seed series of `S(c)` converges absolutely for `|u| < 1`. -/
theorem summable_lambertSolution_mul (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) {u : ℂ} (hu : ‖u‖ < 1) :
    Summable fun j : ℕ => lambertSolution m x c q j * (x * u) ^ j := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg u) hu).mul_left
      (1 + hRatioBound m ‖q‖ / (1 - ‖q‖))) fun j => ?_
  rw [norm_mul, norm_pow, norm_mul, hx, one_mul]
  exact mul_le_mul_of_nonneg_right (norm_lambertSolution_le hx hc hq0 hq1 j) (by positivity)

/-- The decomposition of [AOS, Lemma 7.3(c)], with the Dyson sequence written as `S(x)`. -/
private theorem exists_lambert_decomposition (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m x q) :
    ∃ (a : ℂ) (s : ℕ → ℂ), ∀ j : ℕ, Y j = a * lambertSolution m x x q j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m x (omega m ^ k) q j := by
  obtain ⟨γ, hγ⟩ := Set.mem_iUnion.mp hY
  obtain ⟨s, hs⟩ := exists_decomposition hm hx hq0 hq1 hγ
  refine ⟨if Cx m x = 0 then 0 else γ, s, fun j => ?_⟩
  rw [hs]
  by_cases h : Cx m x = 0 <;>
    simp [h, Finset.sum_apply, eigenSolution, lambertSolution_self hm hx hq1]

/-- **Theorem 7.1(ii)(a), convergence.** For `Y ∈ V` and `|u| < 1` the seed series
`∑_j Y_j (xu)^j` converges [AOS, Theorem 7.1(ii)(a)]. -/
theorem summable_seed_of_mem (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m x q) {u : ℂ} (hu : ‖u‖ < 1) :
    Summable fun j : ℕ => Y j * (x * u) ^ j := by
  obtain ⟨a, s, hs⟩ := exists_lambert_decomposition hm hx hq0 hq1 hY
  have h := ((summable_lambertSolution_mul (m := m) hx hx hq0 hq1 hu).mul_left a).add
    (summable_sum (s := Icc 1 (2 * m)) fun k _ =>
      ((summable_lambertSolution_mul (m := m) hx (norm_omega_pow m k) hq0 hq1 hu).mul_left (s k)))
  refine h.congr fun j => ?_
  rw [hs, add_mul, sum_mul]
  congr 1
  · ring
  · exact sum_congr rfl fun k _ => by ring

/-- **Theorem 7.1(ii)(a), continuation.** For `Y ∈ V` the seed `𝒢_Y` extends to a meromorphic
function on `ℂ` with at most simple poles, all contained in
`{x^{-1} q^{-i}, ω^{-k} q^{-i} : i ≥ 0, 1 ≤ k ≤ d - 1}` [AOS, Theorem 7.1(ii)(a)]. -/
theorem exists_isSeedContinuation (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m x q) :
    ∃ Φ : ℂ → ℂ, IsSeedContinuation m x q Y Φ := by
  obtain ⟨a, s, hs⟩ := exists_lambert_decomposition hm hx hq0 hq1 hY
  have hx0 := ne_zero_of_norm_eq_one hx
  set L : ℂ → ℂ → ℂ := fun c u => lambertSeed x c (lambertCoeff m x c) u q with hL
  refine ⟨fun u => a * L x u + ∑ k ∈ Icc 1 (2 * m), s k * L (omega m ^ k) u, ?_, ?_, ?_⟩
  · -- holomorphy off the pole set
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    have hdiff : ∀ c : ℂ, ‖c‖ = 1 → (∀ i : ℕ, c * q ^ i * u ≠ 1) →
        DifferentiableAt ℂ (fun u => L c u) u := fun c hc hcu =>
      differentiableAt_lambertSeed (summable_norm_lambertCoeff hx hc hq1) hq1 hcu
    refine ((hdiff x hx fun i hi => hu ?_).const_mul a).add
      (DifferentiableAt.fun_sum fun k hk =>
        ((hdiff _ (norm_omega_pow m k) fun i hi => hu ?_).const_mul (s k)))
    · exact Or.inl ⟨i, (mul_pow_mul_eq_one_iff hx0 hq0 i u).mp hi⟩
    · exact Or.inr ⟨i, k, hk,
        (mul_pow_mul_eq_one_iff (ne_zero_of_norm_eq_one (norm_omega_pow m k)) hq0 i u).mp hi⟩
  · -- agreement with the seed on the unit disc
    intro u hu
    have h1 := summable_lambertSolution_mul (m := m) hx hx hq0 hq1 hu
    have h2 := fun k => summable_lambertSolution_mul (m := m) hx (norm_omega_pow m k) hq0 hq1 hu
    simp only [hL, ← sequenceSeed_lambertSolution hx hx hq1 hu,
      ← sequenceSeed_lambertSolution hx (norm_omega_pow m _) hq1 hu, sequenceSeed]
    have hY' : (fun j : ℕ => Y j * (x * u) ^ j) = fun j : ℕ =>
        a * (lambertSolution m x x q j * (x * u) ^ j) + ∑ k ∈ Icc 1 (2 * m),
          s k * (lambertSolution m x (omega m ^ k) q j * (x * u) ^ j) := by
      funext j
      rw [hs, add_mul, sum_mul]
      congr 1
      · ring
      · exact sum_congr rfl fun k _ => by ring
    rw [hY', Summable.tsum_add (h1.mul_left a)
        (summable_sum (s := Icc 1 (2 * m)) fun k _ => (h2 k).mul_left (s k)),
      Summable.tsum_finsetSum fun k _ => (h2 k).mul_left (s k), tsum_mul_left, mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun k _ => by rw [tsum_mul_left]; ring
  · -- at most simple poles
    intro p _
    have hlim : ∀ c : ℂ, ‖c‖ = 1 → ∃ l : ℂ,
        Tendsto (fun u => (u - p) * L c u) (𝓝[≠] p) (𝓝 l) := fun c hc =>
      exists_tendsto_sub_mul_lambertSeed (summable_norm_lambertCoeff hx hc hq1)
        (ne_zero_of_norm_eq_one hc) hq0 hq1 p
    obtain ⟨l₀, h₀⟩ := hlim x hx
    choose l hl using fun k : ℕ => hlim (omega m ^ k) (norm_omega_pow m k)
    refine ⟨a * l₀ + ∑ k ∈ Icc 1 (2 * m), s k * l k, ?_⟩
    have := (h₀.const_mul a).add
      (tendsto_finsetSum (Icc 1 (2 * m)) fun k _ => (hl k).const_mul (s k))
    refine this.congr fun u => ?_
    rw [mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun k _ => by ring

/-- **Theorem 7.1(ii)(a).** For `Y ∈ V` the seed `𝒢_Y(u)` converges for `|u| < 1` and extends to
a meromorphic function on `ℂ` with at most simple poles, all contained in
`{x^{-1} q^{-i}, ω^{-k} q^{-i} : i ≥ 0, 1 ≤ k ≤ d - 1}` [AOS, Theorem 7.1(ii)(a)]. -/
theorem solution_seed_continuation (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {Y : ℕ → ℂ} (hY : Y ∈ recurrenceSolutions m x q) :
    (∀ u : ℂ, ‖u‖ < 1 → Summable fun j : ℕ => Y j * (x * u) ^ j) ∧
      ∃ Φ : ℂ → ℂ, IsSeedContinuation m x q Y Φ :=
  ⟨fun _ hu => summable_seed_of_mem hm hx hq0 hq1 hY hu,
    exists_isSeedContinuation hm hx hq0 hq1 hY⟩

end HigherDyson3
