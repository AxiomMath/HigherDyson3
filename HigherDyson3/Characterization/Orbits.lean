/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.SolutionSpace
public import HigherDyson3.Divisor.DivisorChar
public import HigherDyson3.Divisor.DivisorComplOpen
public import HigherDyson3.Lambert.DoubleSummand

/-!
# The pole orbits of the periodized solution seeds

For `x = e(α)` and `ω = e(1/d)`, the periodizations of the seeds of solutions of the recurrence
can only be singular along the orbits `𝒟_x ∪ ⋃_{k=1}^{d-1} 𝒟_{ω^k}` [AOS, Theorem 7.1(ii)];
since `ω^k = e(k/d)`, the orbit `𝒟_{ω^k}` is `divisor (k/d)`, and their union is
`solutionDivisor`. This file proves the facts about the pole set `{x⁻¹ q^{-i}, ω^{-k} q^{-i}}` of
the seeds used to continue the seed identities from the unit disc: it is countable and closed, its
complement is connected and contains the unit disc, and `q^n u` lies in it only when `(τ, w)`
lies on an orbit.

## Main results

* `HigherDyson3.mem_solutionDivisor`: membership in the union of the orbits.
* `HigherDyson3.omega_pow_eq_e`: `ω^k = e(k/d)`.
* `HigherDyson3.mem_solutionDivisor_of_mem_seedPoleSet`.
* `HigherDyson3.isClosed_seedPoleSet`, `HigherDyson3.isPreconnected_compl_seedPoleSet`,
  `HigherDyson3.ball_subset_compl_seedPoleSet`.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

/-- Membership in `𝒟_x ∪ ⋃_k 𝒟_{ω^k}`. -/
lemma mem_solutionDivisor {m : ℕ} {α : ℚ} {p : ℂ × ℂ} :
    p ∈ solutionDivisor m α ↔
      p ∈ divisor α ∨ ∃ k ∈ Icc 1 (2 * m), p ∈ divisor ((k : ℚ) / (2 * m + 1)) := by
  simp [solutionDivisor]

/-- `ω^k = e(k/d)`. -/
lemma omega_pow_eq_e (m k : ℕ) : omega m ^ k = e (((k : ℚ) / (2 * m + 1) : ℚ) : ℂ) := by
  unfold omega
  rw [e_pow]
  congr 1
  push_cast
  ring

/-- `0 ≤ k/d`. -/
lemma eigenParam_nonneg (m k : ℕ) : 0 ≤ (k : ℚ) / (2 * m + 1) := by positivity

/-- `k/d < 1` for `k ≤ 2m`. -/
lemma eigenParam_lt_one {m k : ℕ} (hk : k ≤ 2 * m) : (k : ℚ) / (2 * m + 1) < 1 := by
  rw [div_lt_one (by positivity)]
  exact_mod_cast Nat.lt_succ_of_le hk

lemma not_mem_divisor_of_not_mem_solutionDivisor {m : ℕ} {α : ℚ} {p : ℂ × ℂ}
    (hp : p ∉ solutionDivisor m α) :
    p ∉ divisor α ∧ ∀ k ∈ Icc 1 (2 * m), p ∉ divisor ((k : ℚ) / (2 * m + 1)) := by
  simp only [solutionDivisor, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hp
  exact ⟨hp.1, fun k hk => hp.2 k hk⟩

/-- `(ℍ × ℂ) \ (𝒟_x ∪ ⋃_k 𝒟_{ω^k})` is open. -/
theorem isOpen_halfPlaneProd_diff_solutionDivisor (m : ℕ) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) : IsOpen (halfPlaneProd \ solutionDivisor m α) := by
  have h : halfPlaneProd \ solutionDivisor m α = (halfPlaneProd \ divisor α) ∩
      ⋂ k ∈ Icc 1 (2 * m), (halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1))) := by
    ext p
    simp only [solutionDivisor, Set.mem_sdiff, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, not_or, not_exists]
    constructor
    · rintro ⟨hH, hα, hk⟩
      exact ⟨⟨hH, hα⟩, fun k hk' => ⟨hH, hk k hk'⟩⟩
    · rintro ⟨⟨hH, hα⟩, hk⟩
      exact ⟨hH, hα, fun k hk' => (hk k hk').2⟩
  rw [h]
  refine (divisor_compl_open α hα0 hα1).inter (isOpen_biInter_finset fun k hk => ?_)
  exact divisor_compl_open _ (eigenParam_nonneg m k) (eigenParam_lt_one (mem_Icc.mp hk).2)

/-- If `q^n u = c⁻¹ q^{-i}`, then `1 - c u q^{n+i} = 0`. -/
lemma one_sub_mul_eq_zero_of_eq {c q u : ℂ} (hc : c ≠ 0) (hq : q ≠ 0) {n : ℤ} {i : ℕ}
    (h : q ^ n * u = c⁻¹ * q ^ (-(i : ℤ))) : 1 - c * u * q ^ (n + i) = 0 := by
  have : c * u * q ^ (n + i) = c * (q ^ n * u) * q ^ (i : ℤ) := by rw [zpow_add₀ hq]; ring
  rw [this, h, zpow_neg, mul_inv_cancel_left₀ hc, inv_mul_cancel₀ (zpow_ne_zero _ hq),
    sub_self]

/-- **The pole set and the orbits.** For `τ ∈ ℍ`, `q = e(τ)`, `u = e(w)` and `n ∈ ℤ`, if `q^n u`
lies in `{x⁻¹ q^{-i}, ω^{-k} q^{-i}}`, then `(τ, w)` lies on `𝒟_x ∪ ⋃_k 𝒟_{ω^k}`. -/
theorem mem_solutionDivisor_of_mem_seedPoleSet {m : ℕ} {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτ : τ ∈ upperHalfPlaneSet) {n : ℤ}
    (h : e τ ^ n * e w ∈ seedPoleSet m (e α) (e τ)) : (τ, w) ∈ solutionDivisor m α := by
  rcases h with ⟨i, hi⟩ | ⟨i, k, hk, hi⟩
  · have h0 := one_sub_mul_eq_zero_of_eq (e_ne_zero _) (e_ne_zero _) hi
    obtain ⟨b, hb⟩ := (divisor_char α hα0 hα1 hτ (n + i)).mp h0
    exact Or.inl (Set.mem_iUnion₂.mpr ⟨_, b, hb⟩)
  · rw [omega_pow_eq_e] at hi
    have h0 := one_sub_mul_eq_zero_of_eq (e_ne_zero _) (e_ne_zero _) hi
    obtain ⟨b, hb⟩ := (divisor_char _ (eigenParam_nonneg m k)
      (eigenParam_lt_one (mem_Icc.mp hk).2) hτ (n + i)).mp h0
    exact Or.inr (Set.mem_biUnion hk (Set.mem_iUnion₂.mpr ⟨_, b, hb⟩))

/-- Off the orbits, no `q^n u` lies in the pole set. -/
theorem not_mem_seedPoleSet {m : ℕ} {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) {τ w : ℂ}
    (hτw : (τ, w) ∈ halfPlaneProd \ solutionDivisor m α) (n : ℤ) :
    e τ ^ n * e w ∉ seedPoleSet m (e α) (e τ) := fun h =>
  hτw.2 (mem_solutionDivisor_of_mem_seedPoleSet hα0 hα1 hτw.1 h)

/-- The points of the pole set have modulus `|q|^{-i}`. -/
lemma exists_norm_eq_of_mem_seedPoleSet {m : ℕ} {x q s : ℂ} (hx : ‖x‖ = 1)
    (hs : s ∈ seedPoleSet m x q) : ∃ i : ℕ, ‖s‖ = ‖q‖⁻¹ ^ i := by
  rcases hs with ⟨i, rfl⟩ | ⟨i, k, -, rfl⟩
  · exact ⟨i, by rw [norm_mul, norm_inv, hx, inv_one, one_mul, norm_zpow, zpow_neg,
      zpow_natCast, inv_pow]⟩
  · exact ⟨i, by rw [norm_mul, norm_inv, norm_omega_pow, inv_one, one_mul, norm_zpow, zpow_neg,
      zpow_natCast, inv_pow]⟩

/-- The pole set is countable. -/
theorem seedPoleSet_countable (m : ℕ) (x q : ℂ) : (seedPoleSet m x q).Countable := by
  refine ((Set.countable_range fun i : ℕ => x⁻¹ * q ^ (-(i : ℤ))).union
    (Set.countable_range fun p : ℕ × ℕ => (omega m ^ p.2)⁻¹ * q ^ (-(p.1 : ℤ)))).mono ?_
  rintro s (⟨i, rfl⟩ | ⟨i, k, -, rfl⟩)
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨(i, k), rfl⟩

/-- The unit disc misses the pole set. -/
theorem ball_subset_compl_seedPoleSet {m : ℕ} {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) : Metric.ball (0 : ℂ) 1 ⊆ (seedPoleSet m x q)ᶜ := by
  intro u hu hs
  obtain ⟨i, hi⟩ := exists_norm_eq_of_mem_seedPoleSet hx hs
  have h1 : 1 ≤ ‖q‖⁻¹ := (one_le_inv₀ (norm_pos_iff.mpr hq0)).mpr hq1.le
  rw [mem_ball_zero_iff, hi] at hu
  exact absurd (one_le_pow₀ h1 (n := i)) (not_le.mpr hu)

/-- The pole set meets every disc about `0` in a finite set. -/
lemma finite_seedPoleSet_inter_closedBall {m : ℕ} {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (R : ℝ) : (seedPoleSet m x q ∩ Metric.closedBall 0 R).Finite := by
  have h1 : 1 < ‖q‖⁻¹ := (one_lt_inv₀ (norm_pos_iff.mpr hq0)).mpr hq1
  obtain ⟨N, hN⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop R).exists_forall_of_atTop
  refine (((Set.finite_Iio N).image fun i : ℕ => x⁻¹ * q ^ (-(i : ℤ))).union
    (((Set.finite_Iio N).prod (Finset.Icc 1 (2 * m)).finite_toSet).image
      fun p : ℕ × ℕ => (omega m ^ p.2)⁻¹ * q ^ (-(p.1 : ℤ)))).subset ?_
  rintro s ⟨hs, hsR⟩
  obtain ⟨j, hj⟩ := exists_norm_eq_of_mem_seedPoleSet hx hs
  have hjN : j < N := by
    by_contra hc
    have := hN j (not_lt.mp hc)
    rw [mem_closedBall_zero_iff, hj] at hsR
    linarith
  rcases hs with ⟨i, rfl⟩ | ⟨i, k, hk, rfl⟩
  · refine Or.inl ⟨i, ?_, rfl⟩
    have hij : i = j := by
      have := hj
      rw [norm_mul, norm_inv, hx, inv_one, one_mul, norm_zpow, zpow_neg, zpow_natCast,
        ← inv_pow] at this
      exact pow_right_injective₀ (by positivity) h1.ne' this
    exact hij ▸ hjN
  · refine Or.inr ⟨(i, k), ⟨?_, hk⟩, rfl⟩
    have hij : i = j := by
      have := hj
      rw [norm_mul, norm_inv, norm_omega_pow, inv_one, one_mul, norm_zpow, zpow_neg,
        zpow_natCast, ← inv_pow] at this
      exact pow_right_injective₀ (by positivity) h1.ne' this
    exact hij ▸ hjN

/-- The pole set is closed. -/
theorem isClosed_seedPoleSet {m : ℕ} {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    IsClosed (seedPoleSet m x q) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro u hu
  set F := seedPoleSet m x q ∩ Metric.closedBall 0 (‖u‖ + 1)
  have hFo : IsOpen Fᶜ := (finite_seedPoleSet_inter_closedBall hx hq0 hq1 _).isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hFo u fun h => hu h.1
  refine ⟨min ε 1, lt_min hε one_pos, fun v hv hvS => ?_⟩
  have hv1 : dist v u < 1 := lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_right _ _)
  have hvε : v ∈ Metric.ball u ε :=
    Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hv) (min_le_left _ _))
  refine hball hvε ⟨hvS, ?_⟩
  rw [mem_closedBall_zero_iff]
  have := norm_le_norm_add_norm_sub' v u
  rw [dist_eq_norm] at hv1
  linarith

/-- The complement of the pole set is connected. -/
theorem isPreconnected_compl_seedPoleSet (m : ℕ) (x q : ℂ) :
    IsPreconnected (seedPoleSet m x q)ᶜ :=
  ((seedPoleSet_countable m x q).isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat)).isConnected.isPreconnected

end HigherDyson3
