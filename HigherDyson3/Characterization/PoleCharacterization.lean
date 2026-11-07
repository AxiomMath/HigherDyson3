/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.EigenResidue
public import HigherDyson3.Characterization.Limit
public import HigherDyson3.Characterization.SolutionPeriodization

/-!
# The Dyson seed is characterized by the location of the poles

Let `m ≥ 2`, `x = e(α)` with `α ∈ ℚ ∩ [0,1)`, `τ ∈ ℍ` and `q = e(τ) ∉ Ξ_m`. For `Y ∈ V` and any
continuation `Φ` of its seed, the poles of `w ↦ ℰ_Y(τ, w)` lie on the orbit `-α + ℤτ + ℤ` if
and only if `Y` is a scalar multiple of `X^{(m)}(x;q)`; and for each `k` with `ω^k ≠ x` the
eigen-solution `Z^{(k)} ∈ V_0` is not a multiple of `X^{(m)}(x;q)` and its periodization has
genuine simple poles exactly on the orbit `-k/d + ℤτ + ℤ` [AOS, Theorem 7.1(ii)(d)].

Write `Y = a S(x) + ∑_k s_k Z^{(k)}` [AOS, Lemma 7.3(c)]. For `ω^k ≠ x`, the point `w_k = -k/d`
lies on `𝒟_{ω^k}` and on none of the other orbits, so near `w_k` only `s_k ℰ^{(k)}` can be
singular and `(w - w_k) ℰ_Y(τ, w) → -s_k ρ^{(k)}(τ)/(2πi)`. Off `Ξ_m`, `ρ^{(k)}(τ) ≠ 0`
[AOS, Lemma 7.5], so a removable singularity at `w_k` forces `s_k = 0`, and then
`Y = (a + ∑_{ω^k = x} s_k) S(x)` with `S(x) = X^{(m)}(x;q)/G_d(x;q)`.

## Main results

* `HigherDyson3.solutionPeriodization_poles_iff`: the characterization.
* `HigherDyson3.exists_eigenSolution_poles`: the eigen-solutions with poles on one other orbit.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ} {α : ℚ}

/-- The point `-β` lies on the orbit `-β' + ℤτ + ℤ` only if `β = β'`, for `β, β' ∈ [0,1)`. -/
lemma eq_of_neg_mem_divisor {β β' : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ'0 : 0 ≤ β')
    (hβ'1 : β' < 1) {τ : ℂ} (hτ : 0 < τ.im) (h : (τ, -(β : ℂ)) ∈ divisor β') : β = β' := by
  obtain ⟨a, b, -, hw⟩ := Set.mem_iUnion₂.mp h
  simp only at hw
  have him : (a : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im hw
    simp only [neg_im, ratCast_im, neg_zero, add_im, mul_im, intCast_re, intCast_im, zero_mul,
      add_zero] at this
    linarith
  have ha : a = 0 := by
    have := (mul_eq_zero.mp him).resolve_right hτ.ne'
    exact_mod_cast this
  subst ha
  have hb : ((β' - β : ℚ) : ℂ) = ((b : ℚ) : ℂ) := by
    push_cast
    linear_combination hw
  have hb' : (β' - β : ℚ) = b := by exact_mod_cast hb
  have h1 : (b : ℚ) < 1 := by linarith
  have h2 : -1 < (b : ℚ) := by linarith
  have h3 : b < 1 := by exact_mod_cast h1
  have h4 : -1 < b := by exact_mod_cast h2
  have hb0 : b = 0 := by omega
  rw [hb0, Int.cast_zero, sub_eq_zero] at hb'
  exact hb'.symm

/-- The point `-β` lies on the orbit `-β + ℤτ + ℤ`. -/
lemma neg_mem_divisor (β : ℚ) {τ : ℂ} (hτ : 0 < τ.im) : (τ, -(β : ℂ)) ∈ divisor β :=
  Set.mem_iUnion₂.mpr ⟨0, 0, hτ, by simp⟩

lemma eigenParam_injOn {k k' : ℕ} (h : (k : ℚ) / (2 * m + 1) = (k' : ℚ) / (2 * m + 1)) :
    k = k' := by
  have : (2 * m + 1 : ℚ) ≠ 0 := by positivity
  rw [div_left_inj' this] at h
  exact_mod_cast h

/-- For `ω^k ≠ x = e(α)`, the parameters `α` and `k/d` differ. -/
lemma ne_eigenParam_of_ne {k : ℕ} (hkx : omega m ^ k ≠ e α) : α ≠ (k : ℚ) / (2 * m + 1) :=
  fun h => hkx (by rw [omega_pow_eq_e, ← h])

/-- The periodization of `Φ_{ω^k}` is analytic in `w` off `𝒟_{ω^k}`. -/
lemma analyticAt_eigenPeriodization (hm : 1 ≤ m) (α : ℚ) {k : ℕ} (hk : k ∈ Icc 1 (2 * m))
    {τ w₀ : ℂ} (hτw : (τ, w₀) ∈ halfPlaneProd \ divisor ((k : ℚ) / (2 * m + 1))) :
    AnalyticAt ℂ (fun w => seedPeriodization m α
      (lambertSeed (e α) (omega m ^ k) (lambertCoeff m (e α) (omega m ^ k))) τ w) w₀ := by
  rw [omega_pow_eq_e]
  exact analyticAt_seedPeriodization_lambertSeed hm (eigenParam_nonneg m k)
    (eigenParam_lt_one (mem_Icc.mp hk).2) (differentiableOn_lambertCoeff_e α _)
    (gaussian_bound_lambertCoeff_e α _) hτw

/-- If `f` is analytic at `w₀`, then `(w - w₀) f(w) → 0` as `w → w₀`, `w ≠ w₀`. -/
lemma tendsto_sub_mul_of_analyticAt {f : ℂ → ℂ} {w₀ : ℂ} (hf : AnalyticAt ℂ f w₀) :
    Tendsto (fun w => (w - w₀) * f w) (𝓝[≠] w₀) (𝓝 0) := by
  have h : Tendsto (fun w => (w - w₀) * f w) (𝓝 w₀) (𝓝 ((w₀ - w₀) * f w₀)) :=
    ((continuous_id.sub continuous_const).continuousAt.mul hf.continuousAt).tendsto
  rw [sub_self, zero_mul] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Characterization by the location of the poles** [AOS, Theorem 7.1(ii)(d)]. Let
`q = e(τ) ∉ Ξ_m`, `Y ∈ V` and `Φ` a continuation of its seed. Then `ℰ_Y(τ, ·)` has no poles off
the orbit `-α + ℤτ + ℤ` (at every `w₀` off it, `ℰ_Y(τ, ·)` agrees on a punctured neighbourhood
with a function analytic at `w₀`) if and only if `Y = c X^{(m)}(x;q)` for some `c ∈ ℂ`. -/
theorem solutionPeriodization_poles_iff (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (hq : e τ ∉ exceptionalSet m) {Y : ℕ → ℂ}
    (hY : Y ∈ recurrenceSolutions m (e α) (e τ)) {Φ : ℂ → ℂ}
    (hΦ : IsSeedContinuation m (e α) (e τ) Y Φ) :
    (∀ w₀ : ℂ, (τ, w₀) ∉ divisor α → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
      ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w) ↔
      ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ) := by
  have hx : ‖e (α : ℂ)‖ = 1 := norm_e_ratCast α
  have hq0 : e τ ≠ 0 := e_ne_zero τ
  have hq1 : ‖e τ‖ < 1 := mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτ)
  have hG : GProduct m (e α) (e τ) ≠ 0 := GProduct_ne_zero hm hx.le hq1
  constructor
  · intro hF
    obtain ⟨a, s, hs⟩ := exists_lambertSolution_decomposition hm hx hq0 hq1 hY
    have hs0 : ∀ k ∈ Icc 1 (2 * m), omega m ^ k ≠ e α → s k = 0 := by
      intro k hk hkx
      set β : ℚ := (k : ℚ) / (2 * m + 1) with hβ
      have hβ0 : 0 ≤ β := eigenParam_nonneg m k
      have hβ1 : β < 1 := eigenParam_lt_one (mem_Icc.mp hk).2
      set w₀ : ℂ := -(β : ℂ) with hw₀
      have hw₀α : (τ, w₀) ∉ divisor α := fun h =>
        ne_eigenParam_of_ne hkx (eq_of_neg_mem_divisor hβ0 hβ1 hα0 hα1 hτ h).symm
      obtain ⟨F, hFa, hFe⟩ := hF w₀ hw₀α
      have h0 : Tendsto (fun w => (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w)
          (𝓝[≠] w₀) (𝓝 0) := by
        refine (tendsto_sub_mul_of_analyticAt hFa).congr' ?_
        filter_upwards [hFe] with w hw
        rw [hw]
      have hρ : lambertResidue m α (e β) (lambertCoeff m (e α) (e β)) τ ≠ 0 := by
        have := lambertResidue_eigen_ne_zero m α hτ hq hk
        rwa [omega_pow_eq_e] at this
      have hxlim : Tendsto (fun w => (w - w₀) * seedPeriodization m α
          (lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))) τ w) (𝓝[≠] w₀) (𝓝 0) :=
        tendsto_sub_mul_of_analyticAt (analyticAt_seedPeriodization_lambertSeed (by omega)
          hα0 hα1 (differentiableOn_lambertCoeff_e α α) (gaussian_bound_lambertCoeff_e α α)
          ⟨hτ, hw₀α⟩)
      have hklim : ∀ k' ∈ Icc 1 (2 * m), Tendsto (fun w => (w - w₀) * seedPeriodization m α
          (lambertSeed (e α) (omega m ^ k') (lambertCoeff m (e α) (omega m ^ k'))) τ w)
          (𝓝[≠] w₀) (𝓝 (if k' = k then
            -(lambertResidue m α (e β) (lambertCoeff m (e α) (e β)) τ /
              (2 * Real.pi * Complex.I)) else 0)) := by
        intro k' hk'
        by_cases hkk : k' = k
        · subst hkk
          rw [ite_eq_left rfl, omega_pow_eq_e]
          have hres := seedPeriodization_lambertSeed_residue (m := m) (by omega) α hβ0 hβ1
            (differentiableOn_lambertCoeff_e (m := m) α β)
            (gaussian_bound_lambertCoeff_e (m := m) α β) hτ 0 0
          simp only [Int.cast_zero, zero_mul, add_zero, mul_zero, zpow_zero,
            mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hres
          refine (hres.comp (tendsto_sub_nhdsNE w₀)).congr fun w => ?_
          have hw : -(β : ℂ) + (w - w₀) = w := by rw [hw₀]; ring
          simp only [Function.comp, hw]
          rfl
        · rw [ite_eq_right hkk]
          refine tendsto_sub_mul_of_analyticAt (analyticAt_eigenPeriodization (by omega) α hk'
            ⟨hτ, fun h => hkk ?_⟩)
          exact (eigenParam_injOn (eq_of_neg_mem_divisor hβ0 hβ1 (eigenParam_nonneg m k')
            (eigenParam_lt_one (mem_Icc.mp hk').2) hτ h)).symm
      have hres : Tendsto (fun w => (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w)
          (𝓝[≠] w₀) (𝓝 (s k * -(lambertResidue m α (e β) (lambertCoeff m (e α) (e β)) τ /
            (2 * Real.pi * Complex.I)))) := by
        have hsum := (hxlim.const_mul a).add (tendsto_finsetSum (Icc 1 (2 * m)) fun k' hk' =>
          (hklim k' hk').const_mul (s k'))
        simp only [mul_zero, zero_add, mul_ite, sum_ite_eq', hk, ite_true] at hsum
        refine hsum.congr' ?_
        filter_upwards [eventually_mem_diff_solutionDivisor hα0 hα1 hτ w₀] with w hw
        rw [seedPeriodization_eq_combination hm hα0 hα1 hw hΦ hs, mul_add, mul_sum]
        congr 1
        · ring
        · exact sum_congr rfl fun k' _ => by ring
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have := tendsto_nhds_unique hres h0
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (neg_ne_zero.mpr (div_ne_zero hρ h2))
    refine ⟨(a + ∑ k ∈ Icc 1 (2 * m), if omega m ^ k = e α then s k else 0) /
      GProduct m (e α) (e τ), ?_⟩
    funext j
    have hterm : ∀ k ∈ Icc 1 (2 * m), s k * lambertSolution m (e α) (omega m ^ k) (e τ) j =
        (if omega m ^ k = e α then s k else 0) * lambertSolution m (e α) (e α) (e τ) j := by
      intro k hk
      by_cases h : omega m ^ k = e α
      · rw [ite_eq_left h, h]
      · rw [ite_eq_right h, hs0 k hk h, zero_mul, zero_mul]
    rw [hs j, sum_congr rfl hterm, ← sum_mul, lambertSolution_self hm hx hq1]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨c, hc⟩ w₀ hw₀
    have hs : ∀ j : ℕ, Y j = c * GProduct m (e α) (e τ) * lambertSolution m (e α) (e α) (e τ) j +
        ∑ k ∈ Icc 1 (2 * m), (0 : ℕ → ℂ) k * lambertSolution m (e α) (omega m ^ k) (e τ) j := by
      intro j
      rw [hc, lambertSolution_self hm hx hq1]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, sum_const_zero, add_zero]
      field_simp
    refine ⟨fun w => c * GProduct m (e α) (e τ) * seedPeriodization m α
      (lambertSeed (e α) (e α) (lambertCoeff m (e α) (e α))) τ w,
      analyticAt_const.mul (analyticAt_seedPeriodization_lambertSeed (by omega) hα0 hα1
        (differentiableOn_lambertCoeff_e α α) (gaussian_bound_lambertCoeff_e α α) ⟨hτ, hw₀⟩),
      ?_⟩
    filter_upwards [eventually_mem_diff_solutionDivisor hα0 hα1 hτ w₀] with w hw
    rw [seedPeriodization_eq_combination hm hα0 hα1 hw hΦ hs]
    simp

/-- **The eigen-solutions** [AOS, Theorem 7.1(ii)(d)]. Let `q = e(τ) ∉ Ξ_m` and
`1 ≤ k ≤ d - 1` with `ω^k ≠ x`. The eigen-solution `Y = Z^{(k)}` lies in `V_0`, is not a scalar
multiple of `X^{(m)}(x;q)`, its seed has a continuation, and for every continuation `Φ` the
periodization `w ↦ ℰ_Y(τ, w)` has a genuine simple pole at every point of the orbit
`-k/d + ℤτ + ℤ` (`(w - w₀) ℰ_Y(τ, w)` tends to a nonzero limit) and no pole elsewhere. -/
theorem exists_eigenSolution_poles (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (hq : e τ ∉ exceptionalSet m) {k : ℕ}
    (hk : k ∈ Icc 1 (2 * m)) (hkx : omega m ^ k ≠ e α) :
    ∃ Y : ℕ → ℂ, Y ∈ recurrenceFamily m (e α) (e τ) 0 ∧
      (¬ ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ)) ∧
      (∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ) ∧
      ∀ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ → ∀ w₀ : ℂ,
        ((τ, w₀) ∈ divisor ((k : ℚ) / (2 * m + 1)) → ∃ L : ℂ, L ≠ 0 ∧
          Tendsto (fun w => (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w)
            (𝓝[≠] w₀) (𝓝 L)) ∧
        ((τ, w₀) ∉ divisor ((k : ℚ) / (2 * m + 1)) → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
          ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w) := by
  have hx : ‖e (α : ℂ)‖ = 1 := norm_e_ratCast α
  have hq0 : e τ ≠ 0 := e_ne_zero τ
  have hq1 : ‖e τ‖ < 1 := mem_ball_zero_iff.mp (e_mem_ball_of_im_pos hτ)
  have hmem := eigenSolution_mem (m := m) hx hq0 hq1 hk
  refine ⟨eigenSolution m (e α) (e τ) k, hmem, ?_, exists_isSeedContinuation hm hx hq0 hq1
    (Set.mem_iUnion.mpr ⟨0, hmem⟩), fun Φ hΦ w₀ => ?_⟩
  · rintro ⟨c, hc⟩
    set l : ℂ := omega m ^ k / e α with hl
    have hl1 : ‖l‖ = 1 := by rw [hl, norm_div, norm_omega_pow, hx, div_one]
    have hlne : l ≠ 1 := fun h => hkx (by rw [hl, div_eq_one_iff_eq (e_ne_zero _)] at h; exact h)
    have hX : Tendsto (fun j : ℕ => c * XSeries m (e α) j (e τ)) atTop
        (𝓝 (c * GProduct m (e α) (e τ))) := by
      have hG : GProduct m (e α) (e τ) ≠ 0 := GProduct_ne_zero hm hx.le hq1
      have := (tendsto_dysonSequence hm hx hq0 hq1).const_mul (c * GProduct m (e α) (e τ))
      rw [mul_one] at this
      refine this.congr fun j => ?_
      field_simp
    have hS := tendsto_lambertSolution_sub_pow (m := m) hx (norm_omega_pow m k) hq0 hq1
    have hpow : Tendsto (fun j : ℕ => l ^ j) atTop (𝓝 (c * GProduct m (e α) (e τ))) := by
      have := hX.sub hS
      rw [sub_zero] at this
      refine this.congr fun j => ?_
      have hj := congrFun hc j
      simp only [eigenSolution, Pi.smul_apply, smul_eq_mul] at hj
      rw [← hj, hl]
      ring
    set L := c * GProduct m (e α) (e τ)
    have hshift : Tendsto (fun j : ℕ => l ^ (j + 1)) atTop (𝓝 L) :=
      hpow.comp (tendsto_add_atTop_nat 1)
    have hmul : Tendsto (fun j : ℕ => l ^ (j + 1)) atTop (𝓝 (l * L)) := by
      refine (hpow.const_mul l).congr fun j => ?_
      ring
    have hL : L = l * L := tendsto_nhds_unique hshift hmul
    have hL0 : L = 0 := by
      have : (1 - l) * L = 0 := by linear_combination hL
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hlne))
    have hnorm := (continuous_norm.tendsto _).comp hpow
    rw [hL0, norm_zero] at hnorm
    have : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
      hnorm.congr fun j => by simp [Function.comp, norm_pow, hl1]
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)
  · set β : ℚ := (k : ℚ) / (2 * m + 1) with hβ
    have hβ0 : 0 ≤ β := eigenParam_nonneg m k
    have hβ1 : β < 1 := eigenParam_lt_one (mem_Icc.mp hk).2
    have hs : ∀ j : ℕ, eigenSolution m (e α) (e τ) k j =
        0 * lambertSolution m (e α) (e α) (e τ) j + ∑ k' ∈ Icc 1 (2 * m),
          (if k' = k then 1 else 0) * lambertSolution m (e α) (omega m ^ k') (e τ) j := by
      intro j
      simp [eigenSolution, hk]
    have hE : ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w =
        seedPeriodization m α (lambertSeed (e α) (e β) (lambertCoeff m (e α) (e β))) τ w := by
      filter_upwards [eventually_mem_diff_solutionDivisor hα0 hα1 hτ w₀] with w hw
      rw [seedPeriodization_eq_combination hm hα0 hα1 hw hΦ hs, ← omega_pow_eq_e]
      simp [hk]
    refine ⟨fun hw₀ => ?_, fun hw₀ => ?_⟩
    · have hρ : lambertResidue m α (e β) (lambertCoeff m (e α) (e β)) τ ≠ 0 := by
        have := lambertResidue_eigen_ne_zero m α hτ hq hk
        rwa [omega_pow_eq_e] at this
      obtain ⟨L, hL, hlim⟩ := exists_tendsto_sub_mul_seedPeriodization_lambertSeed (m := m)
        (by omega) α hβ0 hβ1 (differentiableOn_lambertCoeff_e α β)
        (gaussian_bound_lambertCoeff_e α β) hτ hρ hw₀
      refine ⟨L, hL, hlim.congr' ?_⟩
      filter_upwards [hE] with w hw
      rw [hw]
    · exact ⟨_, analyticAt_seedPeriodization_lambertSeed (by omega) hβ0 hβ1
        (differentiableOn_lambertCoeff_e α β) (gaussian_bound_lambertCoeff_e α β) ⟨hτ, hw₀⟩, hE⟩

/-- **Theorem 7.1(ii)(d)** [AOS, Theorem 7.1(ii)(d)]. Let `m ≥ 2`, `x = e(α)` with
`α ∈ ℚ ∩ [0,1)`, `τ ∈ ℍ` and `q = e(τ) ∉ Ξ_m`. For every `Y ∈ V` and every continuation `Φ` of
its seed, the poles of `w ↦ ℰ_Y(τ, w)` are contained in the orbit `-α + ℤτ + ℤ` if and only if
`Y = c X^{(m)}(x;q)` for some `c ∈ ℂ`. For every `1 ≤ k ≤ d - 1` with `ω^k ≠ x` there is
`Y ∈ V_0`, not a scalar multiple of `X^{(m)}(x;q)`, whose seed has a continuation and whose
periodization has simple poles exactly on the orbit `-k/d + ℤτ + ℤ`. -/
theorem solution_pole_characterization (hm : 2 ≤ m) (hα0 : 0 ≤ α) (hα1 : α < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (hq : e τ ∉ exceptionalSet m) :
    (∀ Y : ℕ → ℂ, Y ∈ recurrenceSolutions m (e α) (e τ) → ∀ Φ : ℂ → ℂ,
      IsSeedContinuation m (e α) (e τ) Y Φ →
      ((∀ w₀ : ℂ, (τ, w₀) ∉ divisor α → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
        ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w) ↔
        ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ))) ∧
    ∀ k ∈ Icc 1 (2 * m), omega m ^ k ≠ e α →
      ∃ Y : ℕ → ℂ, Y ∈ recurrenceFamily m (e α) (e τ) 0 ∧
        (¬ ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ)) ∧
        (∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ) ∧
        ∀ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ → ∀ w₀ : ℂ,
          ((τ, w₀) ∈ divisor ((k : ℚ) / (2 * m + 1)) → ∃ L : ℂ, L ≠ 0 ∧
            Tendsto (fun w => (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w)
              (𝓝[≠] w₀) (𝓝 L)) ∧
          ((τ, w₀) ∉ divisor ((k : ℚ) / (2 * m + 1)) → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
            ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w) :=
  ⟨fun _ hY _ hΦ => solutionPeriodization_poles_iff hm hα0 hα1 hτ hq hY hΦ,
    fun _ hk hkx => exists_eigenSolution_poles hm hα0 hα1 hτ hq hk hkx⟩

end HigherDyson3
