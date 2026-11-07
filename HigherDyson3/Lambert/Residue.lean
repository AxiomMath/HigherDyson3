/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.SimplePoles
public import HigherDyson3.Kernel.KernelResidue
public import HigherDyson3.LocalFacts.PuncturedOffDivisor

/-!
# Residues of the periodization of a Lambert seed

Let `m ≥ 1`, `x = e(α)`, `c = e(β)` with `β ∈ ℚ ∩ [0,1)`, and let `(b_i)` be holomorphic on
the unit disc with a Gaussian bound. The residue function
`ρ_Φ(τ) = x⁻² ∑_i x^{2i} c^{2mi} q^{mi²} b_i(q)` is holomorphic on `ℍ`, and the residue of
`ℰ_Φ(τ, ·)` at `w = -β + aτ + k` is `-ρ_Φ(τ)/(2πi) x^{2a} c^{2ma} q^{-ma²}`
[AOS, Lemma 7.4(b)]. Consequently the points of the orbit `-β + ℤτ + ℤ` are genuine simple poles
where `ρ_Φ(τ) ≠ 0`, and removable singularities where `ρ_Φ(τ) = 0` [AOS, Lemma 7.4(c)].

Near `w₀ = -β + aτ + k`, `ℰ_Φ = R_a + N_a / (1 - e(w - w₀))`
(`HigherDyson3.seedPeriodization_lambertSeed_eq_regular_add`), with `R_a` holomorphic near
`(τ, w₀)` and `N_a` holomorphic on `ℍ × ℂ`. The residue is `-N_a(τ, w₀)/(2πi)`, and a direct
computation with `e(w₀) = c⁻¹ q^a` gives `N_a(τ, w₀) = x^{2a} c^{2ma} q^{-ma²} ρ_Φ(τ)`. If this
vanishes, `N_a(τ, w)/(1 - e(w - w₀))` has a limit at `w₀`.

## Main results

* `HigherDyson3.differentiableOn_lambertResidue`: `ρ_Φ` is holomorphic on `ℍ`.
* `HigherDyson3.seedPeriodization_lambertSeed_residue`: the residue formula.
* `HigherDyson3.seedPeriodization_lambertSeed_pole_genuine`,
  `HigherDyson3.seedPeriodization_lambertSeed_pole_removable`: the dichotomy.
-/

public section

noncomputable section

open Complex Filter Topology

namespace HigherDyson3

/-- The terms `x^{2i} c^{2mi} q^{mi²} b_i(q)` of the residue function have a summable majorant
on every disc `|q| ≤ Q`, `Q < 1`, when `|c| = 1`. -/
theorem exists_majorant_lambertResidue_term (m : ℕ) (α : ℚ) {c : ℂ} (hc : ‖c‖ = 1)
    {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ i : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q →
      ‖e α ^ (2 * i) * c ^ (2 * m * i) * q ^ (m * i ^ 2) * b i q‖ ≤ M i := by
  obtain ⟨B, hB0, hBb⟩ := exists_gaussian_bound_of_le hB hQ1
  refine ⟨fun i => B * Q ^ i, (summable_geometric_of_lt_one hQ0 hQ1).mul_left B,
    fun i q hq => ?_⟩
  have hi : i ≤ m * i ^ 2 + i ^ 2 := le_add_left (Nat.le_self_pow two_ne_zero i)
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_e_ratCast, hc, one_pow,
    one_pow, one_mul, one_mul]
  calc ‖q‖ ^ (m * i ^ 2) * ‖b i q‖ ≤ ‖q‖ ^ (m * i ^ 2) * (B * ‖q‖ ^ (i ^ 2)) := by
        gcongr; exact hBb i q hq
    _ = B * ‖q‖ ^ (m * i ^ 2 + i ^ 2) := by ring
    _ ≤ B * Q ^ i := by
        gcongr
        exact (pow_le_pow_left₀ (norm_nonneg _) hq _).trans
          (pow_le_pow_of_le_one hQ0 hQ1.le hi)

/-- **Holomorphy of the residue series** in `q`: for `|c| = 1`, the series
`∑_i x^{2i} c^{2mi} q^{mi²} b_i(q)` is holomorphic on the unit disc. -/
theorem differentiableOn_lambertResidueSeries (m : ℕ) (α : ℚ) {c : ℂ} (hc : ‖c‖ = 1)
    {b : ℕ → ℂ → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2)) :
    DifferentiableOn ℂ (fun q => ∑' i : ℕ, e α ^ (2 * i) * c ^ (2 * m * i) * q ^ (m * i ^ 2) *
      b i q) (Metric.ball 0 1) := by
  intro q₀ hq₀
  rw [mem_ball_zero_iff] at hq₀
  set r : ℝ := (‖q₀‖ + 1) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hq₀r : ‖q₀‖ < r := by rw [hr]; linarith
  obtain ⟨M, hM, hle⟩ := exists_majorant_lambertResidue_term m α hc hB hr0 hr1
  have hD : DifferentiableOn ℂ (fun q => ∑' i : ℕ, e α ^ (2 * i) * c ^ (2 * m * i) *
      q ^ (m * i ^ 2) * b i q) (Metric.ball 0 r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hM (fun i => ?_) Metric.isOpen_ball
      (fun i q hq => hle i q (by rw [mem_ball_zero_iff] at hq; exact hq.le))
    exact ((differentiableOn_const _).mul (differentiableOn_pow _)).mul
      ((hb i).mono (Metric.ball_subset_ball hr1.le))
  exact (hD.differentiableAt (Metric.isOpen_ball.mem_nhds
    (mem_ball_zero_iff.mpr hq₀r))).differentiableWithinAt

/-- **Holomorphy of the residue function** [AOS, Lemma 7.4(b)]. For `x = e(α)`, `c = e(β)` and
coefficients `b_i` holomorphic on the unit disc with a Gaussian bound, the residue function
`ρ_Φ(τ) = x⁻² ∑_i x^{2i} c^{2mi} q^{mi²} b_i(q)` is holomorphic on `ℍ`. -/
theorem differentiableOn_lambertResidue (m : ℕ) (α β : ℚ) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2)) :
    DifferentiableOn ℂ (lambertResidue m α (e β) b) upperHalfPlaneSet := by
  unfold lambertResidue
  refine DifferentiableOn.const_mul ?_ _
  exact (differentiableOn_lambertResidueSeries m α (norm_e_ratCast β) hb hB).comp
    e_differentiable.differentiableOn fun τ hτ => e_mem_ball_of_im_pos hτ

/-- At `w₀ = -β + aτ + k`, the singular numerator is `x^{2a} c^{2ma} q^{-ma²} ρ_Φ(τ)`. -/
theorem lambertSingularNumerator_eq_lambertResidue (m : ℕ) (α β : ℚ) (b : ℕ → ℂ → ℂ)
    (τ : ℂ) (a k : ℤ) :
    lambertSingularNumerator m α b a τ (-(β : ℂ) + a * τ + k) =
      e α ^ (2 * a) * e β ^ (2 * (m : ℤ) * a) * e τ ^ (-(m : ℤ) * a ^ 2) *
        lambertResidue m α (e β) b τ := by
  rw [lambertSingularNumerator_eq]
  unfold lambertResidue
  rw [show ∀ C S : ℂ, C * ((e α ^ 2)⁻¹ * S) = (e α ^ 2)⁻¹ * (C * S) from fun _ _ => by ring]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [e_zpow, e_pow, e_mul_e, ← mul_assoc]
  congr 1
  exact e_eq_e_of_eq_add_int (-2 * m * (a + i) * k) (by push_cast; ring)

/-- `c u q^{-a} = e(w - w₀)` for `w₀ = -β + aτ + k`. -/
lemma e_mul_e_mul_zpow_eq (β : ℚ) (τ w : ℂ) (a k : ℤ) :
    e β * e w * e τ ^ (-a) = e (w - (-(β : ℂ) + a * τ + k)) := by
  rw [kernelSimplePole_e_mul _ _ _ a k]
  congr 1
  ring

/-- Near `w₀ = -β + aτ + k`, off `w₀`, the point `(τ, w)` lies off `𝒟_c` and in `Ω_{a,k}`. -/
lemma eventually_mem_off_divisor {β : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {τ : ℂ}
    (hτ : τ ∈ upperHalfPlaneSet) (a k : ℤ) :
    ∀ᶠ w in 𝓝[≠] (-(β : ℂ) + a * τ + k), (τ, w) ∈ halfPlaneProd \ divisor β := by
  obtain ⟨δ, hδ, hoff⟩ := punctured_off_divisor β hβ0 hβ1 hτ (-(β : ℂ) + a * τ + k)
  have hball : {-(β : ℂ) + a * τ + k}ᶜ ∩ Metric.ball (-(β : ℂ) + a * τ + k) δ ∈
      𝓝[≠] (-(β : ℂ) + a * τ + k) :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hball] with w hw
  have hw0 : 0 < ‖w - (-(β : ℂ) + a * τ + k)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw.1)
  have hwδ : ‖w - (-(β : ℂ) + a * τ + k)‖ < δ := by simpa [dist_eq_norm] using hw.2
  simpa using hoff _ hw0 hwδ

/-- **The residues** [AOS, Lemma 7.4(b), (7.12)]. For `m ≥ 1`, `x = e(α)`, `c = e(β)` with
`0 ≤ β < 1` rational, coefficients `b_i` holomorphic on the unit disc with a Gaussian bound,
`τ ∈ ℍ`, `q = e(τ)` and `a, k ∈ ℤ`,
`ε ℰ_Φ(τ, -β + aτ + k + ε) → -(ρ_Φ(τ)/2πi) x^{2a} c^{2ma} q^{-ma²}` as `ε → 0`, `ε ≠ 0`. -/
theorem seedPeriodization_lambertSeed_residue {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (a k : ℤ) :
    Tendsto (fun ε : ℂ => ε * seedPeriodization m α (lambertSeed (e α) (e β) b) τ
        (-(β : ℂ) + a * τ + k + ε)) (𝓝[≠] 0)
      (𝓝 (-(lambertResidue m α (e β) b τ / (2 * Real.pi * Complex.I)) * e α ^ (2 * a) *
        e β ^ (2 * (m : ℤ) * a) * e τ ^ (-(m : ℤ) * a ^ 2))) := by
  set w₀ : ℂ := -(β : ℂ) + a * τ + k with hw₀
  set g : ℂ → ℂ := fun ε => ε * lambertRegularPart m α β b a τ (w₀ + ε) +
    lambertSingularNumerator m α b a τ (w₀ + ε) * expQuotient ε with hg
  have hp₀ := kernelResidue_mem_divisorNbhd β hτ a k
  have hline : Continuous fun ε : ℂ => (τ, w₀ + ε) := by fun_prop
  have hopen : IsOpen halfPlaneProd :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)
  have hgc : ContinuousAt g 0 := by
    have hR : ContinuousAt (fun p : ℂ × ℂ => lambertRegularPart m α β b a p.1 p.2) (τ, w₀) :=
      ((differentiableOn_lambertRegularPart hm α hβ0 hβ1 hb hB a k).differentiableAt
        ((divisorNbhd_isOpen β hβ0 hβ1 a k).mem_nhds hp₀)).continuousAt
    have hN : ContinuousAt (fun p : ℂ × ℂ => lambertSingularNumerator m α b a p.1 p.2)
        (τ, w₀) :=
      ((differentiableOn_lambertSingularNumerator α hb hB a).differentiableAt
        (hopen.mem_nhds hp₀.1)).continuousAt
    have hΦ : ContinuousAt expQuotient 0 :=
      (expQuotient_differentiableOn.2.differentiableAt
        (expQuotient_differentiableOn.1.mem_nhds (by simp))).continuousAt
    exact (continuousAt_id.mul (hR.comp_of_eq hline.continuousAt (by rw [add_zero]))).add
      ((hN.comp_of_eq hline.continuousAt (by rw [add_zero])).mul hΦ)
  have hg0 : g 0 = -(lambertResidue m α (e β) b τ / (2 * Real.pi * Complex.I)) *
      e α ^ (2 * a) * e β ^ (2 * (m : ℤ) * a) * e τ ^ (-(m : ℤ) * a ^ 2) := by
    have hΦ0 : expQuotient 0 = -1 / (2 * Real.pi * Complex.I) := by simp [expQuotient]
    simp only [hg, zero_mul, zero_add, add_zero, hw₀]
    rw [lambertSingularNumerator_eq_lambertResidue, hΦ0]
    ring
  have hoff : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), (τ, w₀ + ε) ∈ halfPlaneProd \ divisor β := by
    have h := eventually_mem_off_divisor hβ0 hβ1 hτ a k
    have ht : Tendsto (fun ε : ℂ => w₀ + ε) (𝓝[≠] 0) (𝓝[≠] w₀) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 : Tendsto (fun ε : ℂ => w₀ + ε) (𝓝 0) (𝓝 (w₀ + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        rw [add_zero] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simpa using hε
    exact ht.eventually h
  have heq : g =ᶠ[𝓝[≠] 0] fun ε => ε * seedPeriodization m α (lambertSeed (e α) (e β) b) τ
      (w₀ + ε) := by
    filter_upwards [hoff, self_mem_nhdsWithin] with ε hε hε0
    have hε0 : ε ≠ 0 := hε0
    have hxu : e β * e (w₀ + ε) * e τ ^ (-a) = e ε := by
      rw [e_mul_e_mul_zpow_eq β τ (w₀ + ε) a k]
      congr 1
      rw [hw₀]
      ring
    have hΦ : expQuotient ε = ε / (1 - e ε) := by
      rw [expQuotient, ite_eq_right_of_eq_false _ _ (eq_false hε0)]
    simp only [hg]
    rw [seedPeriodization_lambertSeed_eq_regular_add hm α hβ0 hβ1 hB a hε, hxu, hΦ]
    ring
  have ht : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hgc.tendsto.mono_left nhdsWithin_le_nhds
  rw [hg0] at ht
  exact ht.congr' heq

/-- **Genuine simple poles where `ρ_Φ(τ) ≠ 0`** [AOS, Lemma 7.4(c)]: every point of the orbit
`-β + ℤτ + ℤ` is a simple pole of `ℰ_Φ(τ, ·)`. -/
theorem seedPeriodization_lambertSeed_pole_genuine {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : lambertResidue m α (e β) b τ ≠ 0) (a k : ℤ) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun ε : ℂ => ε * seedPeriodization m α
      (lambertSeed (e α) (e β) b) τ (-(β : ℂ) + a * τ + k + ε)) (𝓝[≠] 0) (𝓝 L) := by
  refine ⟨_, ?_, seedPeriodization_lambertSeed_residue hm α hβ0 hβ1 hb hB hτ a k⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hρ h2))
    (zpow_ne_zero _ (e_ne_zero _))) (zpow_ne_zero _ (e_ne_zero _))) (zpow_ne_zero _ (e_ne_zero _))

/-- **Removable singularities where `ρ_Φ(τ) = 0`** [AOS, Lemma 7.4(c)]: `ℰ_Φ(τ, w)` has a limit
as `w → -β + aτ + k`, `w ≠ -β + aτ + k`. -/
theorem seedPeriodization_lambertSeed_pole_removable {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : lambertResidue m α (e β) b τ = 0) (a k : ℤ) :
    ∃ L : ℂ, Tendsto (fun w => seedPeriodization m α (lambertSeed (e α) (e β) b) τ w)
      (𝓝[≠] (-(β : ℂ) + a * τ + k)) (𝓝 L) := by
  set w₀ : ℂ := -(β : ℂ) + a * τ + k with hw₀
  set h : ℂ → ℂ := fun w => lambertSingularNumerator m α b a τ w with hh
  set G : ℂ → ℂ := fun w => lambertRegularPart m α β b a τ w +
    dslope h w₀ w * expQuotient (w - w₀) with hG
  have hp₀ := kernelResidue_mem_divisorNbhd β hτ a k
  have hline : Continuous fun w : ℂ => (τ, w) := by fun_prop
  have hopen : IsOpen halfPlaneProd :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)
  have hh0 : h w₀ = 0 := by
    simp only [hh, hw₀]
    rw [lambertSingularNumerator_eq_lambertResidue, hρ, mul_zero]
  have hhd : DifferentiableAt ℂ h w₀ :=
    ((differentiableOn_lambertSingularNumerator α hb hB a).differentiableAt
      (hopen.mem_nhds hp₀.1)).comp w₀ ((differentiableAt_const τ).prodMk differentiableAt_id)
  have hGc : ContinuousAt G w₀ := by
    have hR : ContinuousAt (fun p : ℂ × ℂ => lambertRegularPart m α β b a p.1 p.2) (τ, w₀) :=
      ((differentiableOn_lambertRegularPart hm α hβ0 hβ1 hb hB a k).differentiableAt
        ((divisorNbhd_isOpen β hβ0 hβ1 a k).mem_nhds hp₀)).continuousAt
    have hΦ : ContinuousAt (fun w => expQuotient (w - w₀)) w₀ := by
      have : ContinuousAt expQuotient (w₀ - w₀) := by
        rw [sub_self]
        exact (expQuotient_differentiableOn.2.differentiableAt
          (expQuotient_differentiableOn.1.mem_nhds (by simp))).continuousAt
      exact ContinuousAt.comp (g := expQuotient) (f := fun w : ℂ => w - w₀) this (by fun_prop)
    exact (hR.comp hline.continuousAt).add
      ((continuousAt_dslope_same.mpr hhd).mul hΦ)
  refine ⟨G w₀, (hGc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  filter_upwards [eventually_mem_off_divisor hβ0 hβ1 hτ a k, self_mem_nhdsWithin] with w hw hw0
  have hw0 : w - w₀ ≠ 0 := sub_ne_zero.mpr hw0
  have hΦ : expQuotient (w - w₀) = (w - w₀) / (1 - e (w - w₀)) := by
    rw [expQuotient, ite_eq_right_of_eq_false _ _ (eq_false hw0)]
  have hsl : h w = (w - w₀) * dslope h w₀ w := by
    have := sub_smul_dslope h w₀ w
    rw [smul_eq_mul, hh0, sub_zero] at this
    exact this.symm
  simp only [hG]
  rw [seedPeriodization_lambertSeed_eq_regular_add hm α hβ0 hβ1 hB a hw,
    e_mul_e_mul_zpow_eq β τ w a k, hΦ, ← hw₀]
  change _ = _ + h w / _
  rw [hsl]
  ring

end HigherDyson3
