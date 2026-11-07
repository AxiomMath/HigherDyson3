/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-!
# Lambert-type series

For an absolutely summable sequence `(a_n)` and `0 < |q| < 1`, the Lambert-type series
`L(t) = ∑_{n ≥ 0} a_n / (1 - c t q^n)` is holomorphic at every `t₀` with `c t₀ q^n ≠ 1` for all
`n`, and has at most a simple pole at each `t₀ = (c q^{n₀})⁻¹`, where `(t - t₀) L(t)` tends to
`-t₀ a_{n₀}`. This is the meromorphic structure used in [AOS, Lemma 3.1, Lemma 7.2(d)].

## Main results

* `HigherDyson3.differentiableAt_lambertSeries`
* `HigherDyson3.tendsto_sub_mul_lambertSeries`
-/

public section

namespace HigherDyson3

open Filter Topology

/-- A uniform lower bound for the nonvanishing denominators `1 - c t q^n` near a point `t₀`. -/
theorem exists_ball_norm_one_sub_ge {c q t₀ : ℂ} (hq : ‖q‖ < 1) :
    ∃ r > 0, ∃ δ > 0, ∀ t ∈ Metric.ball t₀ r, ∀ n : ℕ, c * t₀ * q ^ n ≠ 1 →
      δ ≤ ‖1 - c * t * q ^ n‖ := by
  -- beyond `N` the terms `c t q^n` are small on the unit ball around `t₀`
  have hlim : Tendsto (fun n : ℕ => ‖c‖ * (‖t₀‖ + 1) * ‖q‖ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul
      (‖c‖ * (‖t₀‖ + 1))
  obtain ⟨N, hN⟩ :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  -- the finitely many remaining denominators are bounded below at `t₀`
  set f : ℕ → ℝ := fun n => if c * t₀ * q ^ n = 1 then 1 else ‖1 - c * t₀ * q ^ n‖ with hf
  set δ₀ : ℝ := (Finset.range (N + 1)).inf' ⟨0, by simp⟩ f with hδ₀def
  have hδ₀ : 0 < δ₀ := by
    rw [hδ₀def]
    refine (Finset.lt_inf'_iff _).2 fun n _ => ?_
    simp only [hf]
    split_ifs with h
    · norm_num
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
  refine ⟨min 1 (δ₀ / (2 * (‖c‖ + 1))), by positivity, min (δ₀ / 2) (1 / 2), by positivity, ?_⟩
  intro t ht n hn0
  rw [Metric.mem_ball] at ht
  have hr1 : dist t t₀ < 1 := lt_of_lt_of_le ht (min_le_left _ _)
  have hr2 : dist t t₀ < δ₀ / (2 * (‖c‖ + 1)) := lt_of_lt_of_le ht (min_le_right _ _)
  have hqn : ‖q‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
  by_cases hn : N ≤ n
  · -- small terms
    have htn : ‖t‖ ≤ ‖t₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' t t₀
      rw [dist_eq_norm] at hr1
      linarith
    have hsmall : ‖c * t * q ^ n‖ ≤ 1 / 2 := by
      rw [norm_mul, norm_mul, norm_pow]
      have := (hN n hn).le
      calc ‖c‖ * ‖t‖ * ‖q‖ ^ n ≤ ‖c‖ * (‖t₀‖ + 1) * ‖q‖ ^ n := by gcongr
        _ ≤ 1 / 2 := this
    have : 1 / 2 ≤ ‖1 - c * t * q ^ n‖ := by
      have := norm_sub_norm_le (1 : ℂ) (c * t * q ^ n)
      rw [norm_one] at this
      linarith
    exact (min_le_right _ _).trans this
  · -- one of the finitely many
    have hmem : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
    have hδn : δ₀ ≤ ‖1 - c * t₀ * q ^ n‖ := by
      have := Finset.inf'_le f hmem
      simpa [hf, hn0] using this
    have hdiff : ‖c * t * q ^ n - c * t₀ * q ^ n‖ ≤ δ₀ / 2 := by
      have : c * t * q ^ n - c * t₀ * q ^ n = c * (t - t₀) * q ^ n := by ring
      rw [this, norm_mul, norm_mul, norm_pow, ← dist_eq_norm]
      have hc : ‖c‖ * dist t t₀ ≤ δ₀ / 2 := by
        have h2 : (‖c‖ + 1) * dist t t₀ ≤ (‖c‖ + 1) * (δ₀ / (2 * (‖c‖ + 1))) := by
          gcongr
        have h3 : (‖c‖ + 1) * (δ₀ / (2 * (‖c‖ + 1))) = δ₀ / 2 := by
          field_simp
        nlinarith [dist_nonneg (x := t) (y := t₀), norm_nonneg c]
      calc ‖c‖ * dist t t₀ * ‖q‖ ^ n ≤ ‖c‖ * dist t t₀ * 1 := by gcongr
        _ ≤ δ₀ / 2 := by linarith
    have : δ₀ / 2 ≤ ‖1 - c * t * q ^ n‖ := by
      have h := norm_sub_norm_le (1 - c * t₀ * q ^ n) (1 - c * t * q ^ n)
      have : (1 - c * t₀ * q ^ n) - (1 - c * t * q ^ n) = c * t * q ^ n - c * t₀ * q ^ n := by
        ring
      rw [this] at h
      linarith
    exact (min_le_left _ _).trans this

/-- Near a point `t₀`, the terms of a Lambert-type series whose denominators do not vanish at
`t₀` are uniformly dominated by `‖a_n‖ / δ`. -/
theorem exists_ball_lambertSeries_bound {a : ℕ → ℂ} {c q t₀ : ℂ} (hq : ‖q‖ < 1)
    (ht₀ : ∀ n : ℕ, a n ≠ 0 → c * t₀ * q ^ n ≠ 1) :
    ∃ r > 0, ∃ δ > 0, ∀ t ∈ Metric.ball t₀ r, ∀ n : ℕ,
      ‖a n / (1 - c * t * q ^ n)‖ ≤ ‖a n‖ / δ ∧
        (a n ≠ 0 → 1 - c * t * q ^ n ≠ 0) := by
  obtain ⟨r, hr, δ, hδ, hb⟩ := exists_ball_norm_one_sub_ge (c := c) (t₀ := t₀) hq
  refine ⟨r, hr, δ, hδ, fun t ht n => ?_⟩
  by_cases han : a n = 0
  · simp [han]
  have h := hb t ht n (ht₀ n han)
  refine ⟨?_, fun _ h0 => ?_⟩
  · rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ h
  · rw [h0, norm_zero] at h
    linarith

/-- **Holomorphy of a Lambert-type series** off its poles: if `∑ ‖a_n‖ < ∞` and `‖q‖ < 1`, then
`t ↦ ∑_n a_n / (1 - c t q^n)` is complex differentiable at every `t₀` with `c t₀ q^n ≠ 1` whenever
`a_n ≠ 0`. -/
theorem differentiableAt_lambertSeries {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {c q t₀ : ℂ}
    (hq : ‖q‖ < 1) (ht₀ : ∀ n : ℕ, a n ≠ 0 → c * t₀ * q ^ n ≠ 1) :
    DifferentiableAt ℂ (fun t => ∑' n, a n / (1 - c * t * q ^ n)) t₀ := by
  obtain ⟨r, hr, δ, hδ, hb⟩ := exists_ball_lambertSeries_bound hq ht₀
  have hdiff :
      DifferentiableOn ℂ (fun t => ∑' n, a n / (1 - c * t * q ^ n)) (Metric.ball t₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n => ‖a n‖ / δ)
      (ha.div_const δ) (fun n => ?_) Metric.isOpen_ball (fun n t ht => (hb t ht n).1)
    by_cases han : a n = 0
    · simp only [han, zero_div]
      exact differentiableOn_const _
    · exact DifferentiableOn.div (differentiableOn_const _) (by fun_prop)
        (fun t ht => (hb t ht n).2 han)
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-- The terms of a Lambert-type series are summable at every point where no denominator of a
nonzero term vanishes. -/
theorem summable_lambertSeries {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {c q t : ℂ}
    (hq : ‖q‖ < 1) (ht : ∀ n : ℕ, a n ≠ 0 → c * t * q ^ n ≠ 1) :
    Summable (fun n => a n / (1 - c * t * q ^ n)) := by
  obtain ⟨r, hr, δ, hδ, hb⟩ := exists_ball_lambertSeries_bound hq ht
  exact Summable.of_norm_bounded (ha.div_const δ) (fun n => (hb t (Metric.mem_ball_self hr) n).1)

/-- **At most a simple pole.** If `∑ ‖a_n‖ < ∞`, `0 < ‖q‖ < 1` and `c ≠ 0`, then at
`t₀ = (c q^{n₀})⁻¹` the function `(t - t₀) ∑_n a_n / (1 - c t q^n)` tends to `-t₀ a_{n₀}`. -/
theorem tendsto_sub_mul_lambertSeries {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) {c q : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hc : c ≠ 0) (n₀ : ℕ) :
    Tendsto (fun t => (t - (c * q ^ n₀)⁻¹) * ∑' n, a n / (1 - c * t * q ^ n))
      (𝓝[≠] (c * q ^ n₀)⁻¹) (𝓝 (-(c * q ^ n₀)⁻¹ * a n₀)) := by
  set t₀ := (c * q ^ n₀)⁻¹ with ht₀
  have hcq : c * q ^ n₀ ≠ 0 := mul_ne_zero hc (pow_ne_zero _ hq0)
  -- the series without its `n₀`-th term
  set b : ℕ → ℂ := Function.update a n₀ 0 with hbdef
  have hbn₀ : b n₀ = 0 := by simp [hbdef]
  have hbne : ∀ n, n ≠ n₀ → b n = a n := fun n h => by simp [hbdef, Function.update_of_ne h]
  have hb : Summable (fun n => ‖b n‖) := by
    refine ha.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    by_cases h : n = n₀
    · subst h; simp [hbn₀]
    · rw [hbne n h]
  have hpoles : ∀ n : ℕ, n ≠ n₀ → c * t₀ * q ^ n ≠ 1 := by
    intro n hn h
    have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have h' : q ^ n = q ^ n₀ := by
      rw [ht₀] at h
      field_simp at h
      linear_combination h
    have := congrArg norm h'
    rw [norm_pow, norm_pow] at this
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact absurd this (ne_of_gt (pow_lt_pow_right_of_lt_one₀ hqnorm hq hlt))
    · exact absurd this (ne_of_lt (pow_lt_pow_right_of_lt_one₀ hqnorm hq hlt))
  have hbpoles : ∀ n, b n ≠ 0 → c * t₀ * q ^ n ≠ 1 := by
    intro n hn
    by_cases h : n = n₀
    · subst h; exact absurd hbn₀ hn
    · exact hpoles n h
  -- the regular part is continuous at `t₀`
  have hreg : ContinuousAt (fun t => ∑' n, b n / (1 - c * t * q ^ n)) t₀ :=
    (differentiableAt_lambertSeries hb hq hbpoles).continuousAt
  -- near `t₀`, the function is `-t₀ a_{n₀}` plus `(t - t₀)` times the regular part
  obtain ⟨r, hr, δ, hδ, hbound⟩ := exists_ball_lambertSeries_bound hq hbpoles
  have heq : ∀ᶠ t in 𝓝[≠] t₀, -(t₀ * a n₀) + (t - t₀) * ∑' n, b n / (1 - c * t * q ^ n) =
      (t - t₀) * ∑' n, a n / (1 - c * t * q ^ n) := by
    have hball : Metric.ball t₀ r ∈ 𝓝[≠] t₀ :=
      mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    filter_upwards [hball, self_mem_nhdsWithin] with t ht htne
    have hsum : Summable (fun n => b n / (1 - c * t * q ^ n)) :=
      Summable.of_norm_bounded (hb.div_const δ) (fun n => (hbound t ht n).1)
    have hsplit : ∑' n, a n / (1 - c * t * q ^ n) =
        ∑' n, b n / (1 - c * t * q ^ n) + a n₀ / (1 - c * t * q ^ n₀) := by
      have hab : ∀ n, a n / (1 - c * t * q ^ n) =
          b n / (1 - c * t * q ^ n) + (if n = n₀ then a n₀ / (1 - c * t * q ^ n₀) else 0) := by
        intro n
        by_cases h : n = n₀
        · subst h; simp [hbn₀]
        · simp [h, hbne n h]
      rw [tsum_congr hab, Summable.tsum_add hsum (summable_of_ne_finset_zero (s := {n₀})
        (fun n hn => by simp at hn; simp [hn])), tsum_ite_eq]
    have hden : 1 - c * t * q ^ n₀ = -(c * q ^ n₀) * (t - t₀) := by
      rw [ht₀]; field_simp; ring
    have htt : t - t₀ ≠ 0 := sub_ne_zero.mpr htne
    have hterm : (t - t₀) * (a n₀ / (-(c * q ^ n₀) * (t - t₀))) = -(t₀ * a n₀) := by
      calc (t - t₀) * (a n₀ / (-(c * q ^ n₀) * (t - t₀))) = -(c * q ^ n₀)⁻¹ * a n₀ := by
            field_simp
        _ = -(t₀ * a n₀) := by rw [ht₀]; ring
    rw [hsplit, mul_add, hden, hterm]
    ring
  have hlim : Tendsto (fun t => -(t₀ * a n₀) + (t - t₀) * ∑' n, b n / (1 - c * t * q ^ n))
      (𝓝[≠] t₀) (𝓝 (-(t₀ * a n₀) + 0 * ∑' n, b n / (1 - c * t₀ * q ^ n))) := by
    refine tendsto_const_nhds.add (Tendsto.mul ?_ (hreg.tendsto.mono_left nhdsWithin_le_nhds))
    have : Tendsto (fun t : ℂ => t - t₀) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
      (continuous_id.sub continuous_const).tendsto t₀
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [zero_mul, add_zero] at hlim
  rw [show -t₀ * a n₀ = -(t₀ * a n₀) by ring]
  exact hlim.congr' heq

end HigherDyson3
