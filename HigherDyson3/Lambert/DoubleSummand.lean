/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.Definitions
public import HigherDyson3.Bounds.CompactQUBounds
public import HigherDyson3.Bounds.GaussianSummable

/-!
# The double series of the periodization of a Lambert seed

Let `x = e(α)`, `c = e(β)` and let `(b_i)` be functions of `q` with a Gaussian bound
`|b_i(q)| ≤ B_Q |q|^{i²}` on `|q| ≤ Q < 1`. Expanding the Lambert seed
`Φ(u) = x⁻² ∑_i b_i / (1 - c q^i u)` inside the periodization `ℰ_Φ` gives the double series
`ℰ_Φ(τ,w) = ∑_{n ∈ ℤ} ∑_{i ≥ 0} x⁻² x^{-2n} q^{mn²} u^{2mn} b_i(q) / (1 - c u q^{n+i})`
[AOS, proof of Lemma 7.4]. This file defines its summands and proves the Gaussian majorant
`A B_Q Q^{mn² + i²} V^{|n|}` on compact sets where the denominators are bounded away from zero.

## Main results

* `HigherDyson3.lambertDoubleSummand`: the summand of the double series.
* `HigherDyson3.seedPeriodization_summand_lambertSeed`: the `n`-th summand of `ℰ_Φ` is the sum
  over `i` of the double summands.
* `HigherDyson3.exists_majorant_lambertDoubleSummand`: the summable majorant.
* `HigherDyson3.differentiableAt_lambertDoubleSummand`: the summands are holomorphic where their
  denominator does not vanish.
-/

public section

noncomputable section

open Complex

namespace HigherDyson3

/-- The double summand `x⁻² x^{-2n} q^{mn²} u^{2mn} b_i(q) / (1 - c u q^{n+i})` of the
periodization of the Lambert seed `x⁻² ∑_i b_i / (1 - c q^i u)`, with `x = e(α)`, `c = e(β)`,
`q = e(τ)` and `u = e(w)`. -/
def lambertDoubleSummand (m : ℕ) (α β : ℚ) (b : ℕ → ℂ → ℂ) (n : ℤ) (i : ℕ) (τ w : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
    b i (e τ) / (1 - e β * e w * e τ ^ (n + i))

/-- The defining formula of `HigherDyson3.lambertDoubleSummand`. -/
lemma lambertDoubleSummand_eq (m : ℕ) (α β : ℚ) (b : ℕ → ℂ → ℂ) (n : ℤ) (i : ℕ) (τ w : ℂ) :
    lambertDoubleSummand m α β b n i τ w =
      (e α ^ 2)⁻¹ * e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
        b i (e τ) / (1 - e β * e w * e τ ^ (n + i)) := (rfl)

/-- `e(z) ≠ 0`. -/
lemma e_ne_zero (z : ℂ) : e z ≠ 0 := Complex.exp_ne_zero _

/-- `e(z)^n = e(nz)` for `n ∈ ℤ`. -/
lemma e_zpow (z : ℂ) (n : ℤ) : e z ^ n = e (n * z) := by
  unfold e
  rw [← Complex.exp_int_mul]
  ring_nf

/-- `e(z)^n = e(nz)` for `n ∈ ℕ`. -/
lemma e_pow (z : ℂ) (n : ℕ) : e z ^ n = e (n * z) := by
  rw [← zpow_natCast, e_zpow]
  norm_cast

/-- `e(z) e(y) = e(z + y)`. -/
lemma e_mul_e (z y : ℂ) : e z * e y = e (z + y) := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

/-- `e(z) = e(y)` when `z - y` is an integer. -/
lemma e_eq_e_of_eq_add_int {z y : ℂ} (n : ℤ) (h : z = y + n) : e z = e y := by
  unfold e
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨n, by rw [h]; ring⟩

/-- `e(k) = 1` for `k ∈ ℤ`. -/
lemma e_intCast_eq_one (k : ℤ) : e (k : ℂ) = 1 := by
  unfold e
  rw [show 2 * (Real.pi : ℂ) * I * k = k * (2 * Real.pi * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- `|e(α)| = 1` for rational `α`. -/
lemma norm_e_ratCast (α : ℚ) : ‖e (α : ℂ)‖ = 1 := by
  have hcast : ((α : ℝ) : ℂ) = (α : ℂ) := Complex.ofReal_ratCast α
  unfold e
  rw [← hcast, Complex.norm_exp]
  simp

/-- The `n`-th summand of the periodization of a Lambert seed is the sum over `i` of the
double summands. -/
theorem seedPeriodization_summand_lambertSeed (m : ℕ) (α β : ℚ) (b : ℕ → ℂ → ℂ) (n : ℤ)
    (τ w : ℂ) :
    e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
        lambertSeed (e α) (e β) b (e τ ^ n * e w) (e τ) =
      ∑' i : ℕ, lambertDoubleSummand m α β b n i τ w := by
  have hq : e τ ≠ 0 := e_ne_zero τ
  unfold lambertSeed
  rw [← mul_assoc, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [lambertDoubleSummand_eq]
  rw [zpow_add₀ hq, zpow_natCast]
  have : e β * e τ ^ i * (e τ ^ n * e w) = e β * e w * (e τ ^ n * e τ ^ i) := by ring
  rw [this]
  ring

/-- If `0 < r`, `r ≤ c` and `r⁻¹ ≤ c`, then `r ^ z ≤ c ^ |z|` for every `z ∈ ℤ`. -/
lemma zpow_le_pow_natAbs {r c : ℝ} (hr : 0 < r) (hrc : r ≤ c) (hrc' : r⁻¹ ≤ c) (z : ℤ) :
    r ^ z ≤ c ^ z.natAbs := by
  rcases Int.natAbs_eq z with h | h
  · rw [h, zpow_natCast, Int.natAbs_natCast]
    exact pow_le_pow_left₀ hr.le hrc _
  · rw [h, zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hrc' _

/-- A Gaussian bound `|b_i(q)| ≤ B |q|^{i²}` on `|q| ≤ Q` for some `0 < Q < 1` gives one with a
nonnegative constant on every smaller disc. -/
lemma exists_gaussian_bound_of_le {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {Q : ℝ} (hQ1 : Q < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2) := by
  obtain ⟨B, hB⟩ := hB (max Q (1 / 2)) (by positivity) (max_lt hQ1 (by norm_num))
  refine ⟨max B 0, le_max_right _ _, fun i q hq => ?_⟩
  exact (hB i q (hq.trans (le_max_left _ _))).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- **Gaussian majorant of the double summands.** Let `S ⊆ ℍ × ℂ` be compact and `I ⊆ ℤ` a set
of indices on which the reciprocal denominators `|1 - c u q^j|⁻¹` are bounded by `A` over `S`.
Then the double summands with `n + i ∈ I` have a summable majorant on `ℤ × ℕ`, uniformly on
`S`. -/
theorem exists_majorant_lambertDoubleSummand {m : ℕ} (hm : 1 ≤ m) (α β : ℚ)
    {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) (I : Set ℤ) {A : ℝ}
    (hA : ∀ p ∈ S, ∀ j ∈ I, ‖1 - e β * e p.2 * e p.1 ^ j‖⁻¹ ≤ A) :
    ∃ M : ℤ × ℕ → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧ ∀ k : ℤ × ℕ, k.1 + k.2 ∈ I → ∀ p ∈ S,
      ‖lambertDoubleSummand m α β b k.1 k.2 p.1 p.2‖ ≤ M k := by
  obtain ⟨Q₀, Q, a₀, b₀, -, -, hQ1, ha₀, hab, hbd⟩ := compact_q_u_bounds S hS hSH
  set Q' := max Q 0 with hQ'
  have hQ0 : 0 ≤ Q' := le_max_right _ _
  have hQ1' : Q' < 1 := max_lt hQ1 one_pos
  have hq : ∀ p ∈ S, ‖e p.1‖ ≤ Q' := fun p hp => le_max_of_le_left (hbd p hp).2.1
  obtain ⟨B, hB0, hBb⟩ := exists_gaussian_bound_of_le hB hQ1'
  set A' := max A 0
  set c := max b₀ a₀⁻¹ with hc
  have hc1 : 1 ≤ c := by
    rcases le_or_gt 1 b₀ with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_lt_inv₀ ha₀).mpr (hab.trans_lt h)).le
  set V := c ^ (2 * m) with hV
  have hV1 : 1 ≤ V := one_le_pow₀ hc1
  have hG := gaussian_summable (m := m) hm hQ0 hQ1' hV1
  have hK : Summable fun k : ℕ => Q' ^ (k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => pow_nonneg hQ0 _)
      (fun k => pow_le_pow_of_le_one hQ0 hQ1'.le (Nat.le_self_pow two_ne_zero k))
      (summable_geometric_of_lt_one hQ0 hQ1')
  refine ⟨fun k => A' * B * (Q' ^ (m * k.1.natAbs ^ 2) * V ^ k.1.natAbs * Q' ^ (k.2 ^ 2)),
    ((hG.mul_of_nonneg hK (fun n => by positivity) (fun k => by positivity)).mul_left
      (A' * B)).congr fun k => by ring,
    fun k => by positivity, fun ⟨n, i⟩ hI p hp => ?_⟩
  obtain ⟨ha, hb'⟩ := (hbd p hp).2.2
  have hu0 : 0 < ‖e p.2‖ := ha₀.trans_le ha
  have hexp : (m : ℤ) * n ^ 2 = ((m * n.natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs]
  have hu : ‖e p.2‖ ^ (2 * (m : ℤ) * n) ≤ V ^ n.natAbs := by
    refine (zpow_le_pow_natAbs (c := c) hu0 (le_max_of_le_left hb')
      (le_max_of_le_right (inv_anti₀ ha₀ ha)) _).trans_eq ?_
    rw [hV, ← pow_mul]
    congr 1
    rw [Int.natAbs_mul, Int.natAbs_mul]
    simp
  have hqp := hq p hp
  have hbi : ‖b i (e p.1)‖ ≤ B * Q' ^ (i ^ 2) :=
    (hBb i _ hqp).trans (by gcongr)
  have hd : ‖1 - e β * e p.2 * e p.1 ^ (n + i)‖⁻¹ ≤ A' := (hA p hp _ hI).trans (le_max_left _ _)
  simp only [lambertDoubleSummand_eq]
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv,
    norm_pow, norm_zpow, norm_zpow, norm_zpow, norm_e_ratCast, hexp, zpow_natCast]
  simp only [one_pow, inv_one, one_zpow, one_mul]
  calc ‖e p.1‖ ^ (m * n.natAbs ^ 2) * ‖e p.2‖ ^ (2 * (m : ℤ) * n) * ‖b i (e p.1)‖ *
        ‖1 - e β * e p.2 * e p.1 ^ (n + i)‖⁻¹
      ≤ Q' ^ (m * n.natAbs ^ 2) * V ^ n.natAbs * (B * Q' ^ (i ^ 2)) * A' := by
        gcongr
    _ = A' * B * (Q' ^ (m * n.natAbs ^ 2) * V ^ n.natAbs * Q' ^ (i ^ 2)) := by ring

/-- `e` maps the upper half-plane into the open unit disc. -/
lemma e_mem_ball_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : e τ ∈ Metric.ball (0 : ℂ) 1 :=
  mem_ball_zero_iff.mpr (compactQUBounds_norm_e_lt_one hτ)

/-- `e` is entire. -/
lemma e_differentiable : Differentiable ℂ e := fun z => by unfold e; fun_prop

/-- For `b_i` holomorphic on the unit disc, `τ ↦ b_i(e(τ))` is holomorphic at every point of
`ℍ`, as a function on `ℂ × ℂ` of the first coordinate. -/
lemma differentiableAt_comp_e_fst {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    {p : ℂ × ℂ} (hp : 0 < p.1.im) : DifferentiableAt ℂ (fun p : ℂ × ℂ => f (e p.1)) p := by
  refine DifferentiableAt.comp (𝕜 := ℂ) (g := f) p ?_ ((e_differentiable _).comp _
    differentiableAt_fst)
  exact hf.differentiableAt (Metric.isOpen_ball.mem_nhds (e_mem_ball_of_im_pos hp))

/-- The double summands are holomorphic at every point of `ℍ × ℂ` where their denominator
does not vanish. -/
theorem differentiableAt_lambertDoubleSummand (m : ℕ) (α β : ℚ) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1)) (n : ℤ) (i : ℕ) {p : ℂ × ℂ}
    (hp : 0 < p.1.im) (hden : 1 - e β * e p.2 * e p.1 ^ (n + i) ≠ 0) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => lambertDoubleSummand m α β b n i p.1 p.2) p := by
  have hfst : DifferentiableAt ℂ (fun p : ℂ × ℂ => e p.1) p :=
    (e_differentiable _).comp _ differentiableAt_fst
  have hsnd : DifferentiableAt ℂ (fun p : ℂ × ℂ => e p.2) p :=
    (e_differentiable _).comp _ differentiableAt_snd
  simp only [lambertDoubleSummand_eq, div_eq_mul_inv]
  refine DifferentiableAt.mul (((((differentiableAt_const _).mul
    (differentiableAt_const _)).mul (hfst.zpow (Or.inl (e_ne_zero _)))).mul
      (hsnd.zpow (Or.inl (e_ne_zero _)))).mul (differentiableAt_comp_e_fst (hb i) hp)) ?_
  exact ((differentiableAt_const _).sub (((differentiableAt_const _).mul hsnd).mul
    (hfst.zpow (Or.inl (e_ne_zero _))))).inv hden

end HigherDyson3
