/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Holomorphy.ParametricIntegral

/-!
# Removable singularities along a line in `ℂ × ℂ`

Let `N` be holomorphic on an open `V ⊆ ℂ × ℂ` and vanish on `V ∩ {w = β}`. Then
`N = (w - β) N₁` on `V` with `N₁` holomorphic on `V`. Off the line, `N₁ = N / (w - β)`; on it,
`N₁(τ, β) = ∂_w N(τ, β)`. Near a point of the line, `N₁` is the Cauchy integral
`N₁(τ, w) = (2πi)⁻¹ ∮_{|z - β| = R} N(τ, z) / ((z - β)(z - w)) dz`, holomorphic in `(τ, w)` as
a parametric integral (`HigherDyson3.differentiableOn_intervalIntegral_prod`).

We also record the gluing of local holomorphic extensions of a function given on a dense
subset.

## Main results

* `HigherDyson3.exists_differentiableOn_eq_sub_mul`: the division `N = (w - β) N₁`.
* `HigherDyson3.exists_differentiableOn_extension`: gluing local holomorphic extensions.
-/

public section

open Metric Filter Topology Set Complex

namespace HigherDyson3

/-- The Cauchy integral `∮_{|z - β| = R} (z - w)⁻¹ N(τ, z) / (z - β) dz` is holomorphic in
`(τ, w)` on a polydisc `ball τ₀ r × ball β r` whose product with the circle lies in the domain
of `N`. -/
private lemma differentiableOn_cauchyIntegral {V : Set (ℂ × ℂ)} {N : ℂ × ℂ → ℂ}
    (hN : DifferentiableOn ℂ N V) {τ₀ β : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hV : ∀ τ ∈ ball τ₀ r, ∀ z ∈ sphere β R, (τ, z) ∈ V) :
    DifferentiableOn ℂ
      (fun p : ℂ × ℂ => ∮ z in C(β, R), (z - p.2)⁻¹ • (N (p.1, z) / (z - β)))
      (ball τ₀ r ×ˢ ball β r) := by
  have hR : 0 < R := hr.trans hrR
  have hsph : ∀ θ : ℝ, circleMap β R θ ∈ sphere β R := circleMap_mem_sphere β hR.le
  have hne : ∀ θ : ℝ, ∀ w ∈ ball β r, circleMap β R θ - w ≠ 0 := by
    intro θ w hw h
    have h1 := hsph θ
    rw [sub_eq_zero.mp h, mem_sphere] at h1
    rw [mem_ball] at hw
    linarith
  have hne' : ∀ θ : ℝ, circleMap β R θ - β ≠ 0 := by
    intro θ h
    have h1 := hsph θ
    rw [sub_eq_zero.mp h, mem_sphere, dist_self] at h1
    linarith
  have hc1 : Continuous (circleMap β R) := continuous_circleMap β R
  have hc0 : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  simp only [circleIntegral, deriv_circleMap, smul_eq_mul]
  refine differentiableOn_intervalIntegral_prod (isOpen_ball.prod isOpen_ball)
    Real.two_pi_pos.le ?_ fun θ _ => ?_
  · have hNc : ContinuousOn (fun q : (ℂ × ℂ) × ℝ => N (q.1.1, circleMap β R q.2))
        ((ball τ₀ r ×ˢ ball β r) ×ˢ Icc 0 (2 * Real.pi)) :=
      hN.continuousOn.comp (by fun_prop) fun q hq => hV _ hq.1.1 _ (hsph _)
    have hinv : ContinuousOn (fun q : (ℂ × ℂ) × ℝ => (circleMap β R q.2 - q.1.2)⁻¹)
        ((ball τ₀ r ×ˢ ball β r) ×ˢ Icc 0 (2 * Real.pi)) :=
      ContinuousOn.inv₀ (by fun_prop) fun q hq => hne q.2 q.1.2 hq.1.2
    exact ContinuousOn.mul (by fun_prop) (hinv.mul (hNc.div (by fun_prop) fun q _ => hne' q.2))
  · have h1 : DifferentiableOn ℂ (fun p : ℂ × ℂ => (circleMap β R θ - p.2)⁻¹)
        (ball τ₀ r ×ˢ ball β r) :=
      DifferentiableOn.inv (by fun_prop) fun p hp => hne θ p.2 hp.2
    have hcomp : DifferentiableOn ℂ (fun p : ℂ × ℂ => N (p.1, circleMap β R θ))
        (ball τ₀ r ×ˢ ball β r) :=
      hN.comp (s := ball τ₀ r ×ˢ ball β r) (by fun_prop)
        fun p (hp : p ∈ ball τ₀ r ×ˢ ball β r) => hV _ hp.1 _ (hsph θ)
    have h2 : DifferentiableOn ℂ
        (fun p : ℂ × ℂ => N (p.1, circleMap β R θ) / (circleMap β R θ - β))
        (ball τ₀ r ×ˢ ball β r) := by
      intro p hp
      simpa only [div_eq_mul_inv] using (hcomp p hp).mul_const (circleMap β R θ - β)⁻¹
    exact (differentiableOn_const _).mul (h1.mul h2)

/-- **Division by the equation of a line.** Let `V ⊆ ℂ × ℂ` be open and let `N` be holomorphic
on `V` with `N(τ, β) = 0` whenever `(τ, β) ∈ V`. Then there is `N₁` holomorphic on `V` with
`N = (w - β) N₁` on `V`. -/
theorem exists_differentiableOn_eq_sub_mul {V : Set (ℂ × ℂ)} (hV : IsOpen V) {β : ℂ}
    {N : ℂ × ℂ → ℂ} (hN : DifferentiableOn ℂ N V) (hN0 : ∀ p ∈ V, p.2 = β → N p = 0) :
    ∃ N₁ : ℂ × ℂ → ℂ, DifferentiableOn ℂ N₁ V ∧ ∀ p ∈ V, N p = (p.2 - β) * N₁ p := by
  set N₁ : ℂ × ℂ → ℂ := fun p =>
    if p.2 = β then deriv (fun w => N (p.1, w)) β else N p / (p.2 - β) with hN₁
  refine ⟨N₁, fun p₀ hp₀ => ?_, fun p hp => ?_⟩
  swap
  · by_cases hpβ : p.2 = β
    · rw [hN0 p hp hpβ, hpβ, sub_self, zero_mul]
    · simp only [hN₁, ite_eq_right hpβ]
      field_simp [sub_ne_zero.mpr hpβ]
  have hNat : ∀ p ∈ V, DifferentiableAt ℂ N p := fun p hp => hN.differentiableAt (hV.mem_nhds hp)
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hp₀β : p₀.2 = β
  · -- near the line: the Cauchy integral
    obtain ⟨τ₀, w₀⟩ := p₀
    simp only at hp₀β
    subst hp₀β
    obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.mp hV _ hp₀
    set r := ε / 4 with hr
    have r0 : 0 < r := by positivity
    have hmem : ∀ τ ∈ ball τ₀ r, ∀ z, dist z w₀ < 3 * r → (τ, z) ∈ V := by
      intro τ hτ z hz
      apply hε
      rw [mem_ball, Prod.dist_eq]
      rw [mem_ball] at hτ
      exact max_lt (by simp only; linarith) (by simp only; linarith)
    set U := ball τ₀ r ×ˢ ball w₀ r with hU
    have hUn : U ∈ 𝓝 (τ₀, w₀) := (isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨mem_ball_self r0, mem_ball_self r0⟩
    have hK := differentiableOn_cauchyIntegral hN (τ₀ := τ₀) (β := w₀) r0
      (show r < 2 * r by linarith) fun τ hτ z hz => hmem τ hτ z (by
        rw [mem_sphere] at hz; linarith)
    refine (((hK.differentiableAt hUn).const_smul (2 * Real.pi * I)⁻¹)).congr_of_eventuallyEq ?_
    filter_upwards [hUn] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    set g : ℂ → ℂ := dslope (fun w => N (p.1, w)) w₀ with hg
    have hslice : DifferentiableOn ℂ (fun w => N (p.1, w)) (ball w₀ (3 * r)) :=
      hN.comp (by fun_prop) fun z hz => hmem p.1 hp1 z hz
    have hgd : DifferentiableOn ℂ g (ball w₀ (3 * r)) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds w₀ (by positivity))).mpr hslice
    have h0 : N (p.1, w₀) = 0 := hN0 _ (hmem p.1 hp1 w₀ (by rw [dist_self]; positivity)) rfl
    have hcl : closedBall w₀ (2 * r) ⊆ ball w₀ (3 * r) := closedBall_subset_ball (by linarith)
    have hcauchy :=
      Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (s := ∅) countable_empty (ball_subset_ball (by linarith) hp2 : p.2 ∈ ball w₀ (2 * r))
      (hgd.continuousOn.mono hcl) fun z hz => hgd.differentiableAt
        (isOpen_ball.mem_nhds (hcl (ball_subset_closedBall hz.1)))
    have hcongr : (∮ z in C(w₀, 2 * r), (z - p.2)⁻¹ • g z) =
        ∮ z in C(w₀, 2 * r), (z - p.2)⁻¹ • (N (p.1, z) / (z - w₀)) := by
      refine circleIntegral.integral_congr (by positivity) fun z hz => ?_
      have hz0 : z ≠ w₀ := by
        rintro rfl
        rw [mem_sphere, dist_self] at hz
        linarith
      simp only [hg, dslope_of_ne _ hz0, slope_def_field, h0, sub_zero]
    rw [hcongr] at hcauchy
    rw [Pi.smul_apply, hcauchy, hg]
    by_cases hpw : p.2 = w₀
    · simp only [hN₁, ite_eq_left hpw, hpw, dslope_same]
    · simp only [hN₁, ite_eq_right hpw, dslope_of_ne _ hpw, slope_def_field, h0, sub_zero]
  · -- off the line: the quotient
    have hopen : IsOpen {p : ℂ × ℂ | p.2 ≠ β} := isOpen_ne_fun continuous_snd continuous_const
    have hd : DifferentiableAt ℂ (fun p : ℂ × ℂ => p.2 - β) p₀ := by fun_prop
    refine ((hNat p₀ hp₀).mul (hd.inv (sub_ne_zero.mpr hp₀β))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hp₀β] with p hp
    simp only [hN₁, ite_eq_right (show ¬p.2 = β from hp), div_eq_mul_inv]
    rfl

/-- **Gluing local holomorphic extensions.** Let `U ⊆ ℂ × ℂ` be open with `U ⊆ closure Ω`,
and let `G` admit, near every point of `U`, a holomorphic function agreeing with it on `Ω`.
Then `G` agrees on `Ω` with a function holomorphic on `U`. -/
theorem exists_differentiableOn_extension {U Ω : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hdense : U ⊆ closure Ω) {G : ℂ × ℂ → ℂ}
    (hloc : ∀ p ∈ U, ∃ V ∈ 𝓝 p, ∃ E : ℂ × ℂ → ℂ, DifferentiableOn ℂ E V ∧
      ∀ q ∈ V ∩ Ω, E q = G q) :
    ∃ G' : ℂ × ℂ → ℂ, DifferentiableOn ℂ G' U ∧ ∀ q ∈ Ω, G' q = G q := by
  classical
  set G' : ℂ × ℂ → ℂ := fun q => if q ∈ Ω then G q else limUnder (𝓝[Ω] q) G with hG'
  refine ⟨G', fun p hp => ?_, fun q hq => by simp only [hG', ite_eq_left hq]⟩
  obtain ⟨V, hV, E, hE, hEG⟩ := hloc p hp
  have hW : interior V ∩ U ∈ 𝓝 p := inter_mem (interior_mem_nhds.mpr hV) (hU.mem_nhds hp)
  have heq : ∀ q ∈ interior V ∩ U, G' q = E q := by
    rintro q ⟨hqV, hqU⟩
    by_cases hqΩ : q ∈ Ω
    · simp only [hG', ite_eq_left hqΩ]
      exact (hEG q ⟨interior_subset hqV, hqΩ⟩).symm
    · simp only [hG', ite_eq_right hqΩ]
      have : (𝓝[Ω] q).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense hqU)
      have hVq : V ∈ 𝓝 q := mem_interior_iff_mem_nhds.mp hqV
      have hEc : ContinuousAt E q := (hE.differentiableAt hVq).continuousAt
      refine Tendsto.limUnder_eq ?_
      refine (hEc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [nhdsWithin_le_nhds hVq, self_mem_nhdsWithin] with x hxV hxΩ
      exact hEG x ⟨hxV, hxΩ⟩
  exact ((hE.differentiableAt hV).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem hW heq)).differentiableWithinAt

/-- **Residues along a line.** Suppose that near `(τ, c)`, off a set `D` meeting a neighbourhood
`V` of `(τ, c)` only on the line `w = c`, one has `(w - c) H = N` with `N` continuous at
`(τ, c)`. Then `ε H(τ, c + ε) → N(τ, c)` as `ε → 0`, `ε ≠ 0`. -/
theorem tendsto_mul_of_eq_sub_mul {H N : ℂ × ℂ → ℂ} {D V : Set (ℂ × ℂ)} {τ c : ℂ}
    (hV : V ∈ 𝓝 (τ, c)) (hVD : ∀ q ∈ V, q.2 ≠ c → q ∉ D) (hN : ContinuousAt N (τ, c))
    (hNH : ∀ q ∈ V, q ∉ D → N q = (q.2 - c) * H q) :
    Tendsto (fun ε : ℂ => ε * H (τ, c + ε)) (𝓝[≠] 0) (𝓝 (N (τ, c))) := by
  have hline : Tendsto (fun ε : ℂ => ((τ, c + ε) : ℂ × ℂ)) (𝓝 0) (𝓝 (τ, c)) := by
    have : Continuous fun ε : ℂ => ((τ, c + ε) : ℂ × ℂ) := by fun_prop
    simpa using this.tendsto 0
  have hlim : Tendsto (fun ε : ℂ => N (τ, c + ε)) (𝓝[≠] 0) (𝓝 (N (τ, c))) :=
    (hN.tendsto.comp hline).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (hline.eventually_mem hV), self_mem_nhdsWithin]
    with ε hεV hε0
  have hε0 : ε ≠ 0 := hε0
  rw [hNH _ hεV (hVD _ hεV (by simpa using hε0))]
  simp

end HigherDyson3
