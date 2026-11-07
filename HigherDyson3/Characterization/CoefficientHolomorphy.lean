/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.SeedDecomposition

/-!
# Holomorphic dependence of the decomposition coefficients on `q`

Let `m ≥ 2` and `|x| = 1`. Each `S_j(c)`, `|c| = 1`, `j ≥ 0`, is holomorphic in `q` on the unit
disc: the series `λ^j ∑_i λ^{2i} q^{i² + ij} h_i(c)` converges normally there
[AOS, proof of Theorem 7.1(ii)(c)]. The `(d-1) × (d-1)` matrix
`M(q) = (Z^{(k)}_j)_{0 ≤ j ≤ d-2, 1 ≤ k ≤ d-1}` is invertible for `0 < |q| < 1`
[AOS, Lemma 7.3(a),(b)], so if `Y(q) ∈ V_{γ(q)}` has initial values `Y_0, …, Y_{d-2}` and
parameter `γ` holomorphic on an open `Ω ⊆ {0 < |q| < 1}`, then by Cramer's rule the coefficients
`s_k(q)` of the decomposition `Y = γ' S(x) + ∑_k s_k Z^{(k)}` are holomorphic on `Ω`.

## Main results

* `HigherDyson3.differentiableOn_lambertSolution`: `q ↦ S_j(c)` is holomorphic on the disc.
* `HigherDyson3.differentiableOn_det`: the determinant of a holomorphic matrix is holomorphic.
* `HigherDyson3.det_eigenWindow_ne_zero`: `M(q)` is invertible.
* `HigherDyson3.exists_holomorphic_decomposition`: holomorphic decomposition coefficients.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ}

/-- `S_j(c) = λ^j ∑_i λ^{2i} q^{i² + ij} h_i(c)` with natural exponents, for `j ≥ 0`. -/
lemma lambertSolution_natCast (x c q : ℂ) (j : ℕ) :
    lambertSolution m x c q j =
      (c / x) ^ j * ∑' i : ℕ, (c / x) ^ (2 * i) * q ^ (i ^ 2 + i * j) * hRatio m c q i := by
  unfold lambertSolution
  rw [zpow_natCast]
  congr 1

/-- **Holomorphy of `S_j(c)` in `q`.** For `|x| = |c| = 1` and `j ≥ 0`, `q ↦ S_j(c)` is
holomorphic on the unit disc. -/
theorem differentiableOn_lambertSolution {x c : ℂ} (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (j : ℕ) :
    DifferentiableOn ℂ (fun q => lambertSolution m x c q j) (Metric.ball 0 1) := by
  intro q₀ hq₀
  rw [mem_ball_zero_iff] at hq₀
  set r : ℝ := (‖q₀‖ + 1) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hq₀r : ‖q₀‖ < r := by rw [hr]; linarith
  have hl : ‖c / x‖ = 1 := by rw [norm_div, hc, hx, div_one]
  have hD : DifferentiableOn ℂ (fun q => ∑' i : ℕ, (c / x) ^ (2 * i) * q ^ (i ^ 2 + i * j) *
      hRatio m c q i) (Metric.ball 0 r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (hRatioBound m r)) (fun i => ?_)
      Metric.isOpen_ball (fun i q hq => ?_)
    · exact ((differentiableOn_const _).mul (differentiableOn_pow _)).mul
        ((differentiableOn_hRatio (m := m) hc.le i).mono (Metric.ball_subset_ball hr1.le))
    · have hq : ‖q‖ ≤ r := (mem_ball_zero_iff.mp hq).le
      rw [norm_mul, norm_mul, norm_pow, hl, one_pow, one_mul, norm_pow, mul_comm]
      refine mul_le_mul (norm_hRatio_le hr0 hr1 hc.le hq i) ?_ (by positivity)
        (hRatioBound_nonneg hr0 hr1)
      refine (pow_le_pow_left₀ (norm_nonneg _) hq _).trans (pow_le_pow_of_le_one hr0 hr1.le ?_)
      nlinarith [Nat.le_self_pow two_ne_zero i]
  have hDa := hD.differentiableAt (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq₀r))
  simp only [lambertSolution_natCast]
  exact ((differentiableAt_const _).mul hDa).differentiableWithinAt

/-- **The determinant of a holomorphic matrix is holomorphic.** -/
theorem differentiableOn_det {n : Type*} [Fintype n] [DecidableEq n] {U : Set ℂ}
    {f : ℂ → Matrix n n ℂ} (hf : ∀ i j, DifferentiableOn ℂ (fun q => f q i j) U) :
    DifferentiableOn ℂ (fun q => (f q).det) U := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact DifferentiableOn.fun_sum fun σ _ =>
    (differentiableOn_const _).mul (DifferentiableOn.fun_finsetProd fun i _ => hf _ _)

/-- The matrix `M(q) = (Z^{(k)}_j)_{0 ≤ j ≤ d-2, 1 ≤ k ≤ d-1}` of initial values of the
eigen-solutions, indexed by `Fin (d - 1)`. -/
abbrev eigenWindow (m : ℕ) (x q : ℂ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  Matrix.of fun t i : Fin (2 * m) => eigenSolution m x q (i + 1) t

/-- **`M(q)` is invertible** [AOS, Lemma 7.3(a),(b)]: its columns, the initial windows of the
eigen-solutions, are linearly independent. -/
theorem det_eigenWindow_ne_zero (hm : 2 ≤ m) {x q : ℂ} (hx : ‖x‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) : (eigenWindow m x q).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hv0
  have hli := Fintype.linearIndependent_iff.mp (linearIndependent_window hm hx hq0 hq1 0)
  funext i
  refine hli v ?_ i
  funext t
  have := congrFun hv t
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, window_apply, zero_add, smul_eq_mul,
    Pi.zero_apply]
  rw [← this]
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- The decomposition `Y = γ' S(x) + ∑_k s_k S(ω^k)` with `γ' = γ` if `C_x ≠ 0` and `γ' = 0`
otherwise [AOS, Lemma 7.3(c)]. -/
theorem exists_lambertSolution_decomposition_of_mem (hm : 2 ≤ m) {x q γ : ℂ} (hx : ‖x‖ = 1)
    (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {Y : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ) :
    ∃ s : ℕ → ℂ, ∀ j : ℕ, Y j = (if Cx m x = 0 then 0 else γ) * lambertSolution m x x q j +
      ∑ k ∈ Icc 1 (2 * m), s k * lambertSolution m x (omega m ^ k) q j := by
  obtain ⟨s, hs⟩ := exists_decomposition hm hx hq0 hq1 hY
  refine ⟨s, fun j => ?_⟩
  rw [hs]
  by_cases h : Cx m x = 0 <;>
    simp [h, Finset.sum_apply, eigenSolution, lambertSolution_self hm hx hq1]

/-- **Holomorphic decomposition coefficients** [AOS, proof of Theorem 7.1(ii)(c)]. If
`Y(q) ∈ V_{γ(q)}` for `q` in an open `Ω ⊆ {0 < |q| < 1}`, with `Y_0, …, Y_{d-2}` and `γ`
holomorphic on `Ω`, then there are coefficients `s_k(q)` holomorphic on `Ω` with
`Y(q) = γ'(q) S(x) + ∑_k s_k(q) S(ω^k)`, `γ' = γ` if `C_x ≠ 0` and `γ' = 0` otherwise. -/
theorem exists_holomorphic_decomposition (hm : 2 ≤ m) {x : ℂ} (hx : ‖x‖ = 1) {Ω : Set ℂ}
    (hΩsub : Ω ⊆ {q | 0 < ‖q‖ ∧ ‖q‖ < 1}) {Y : ℂ → ℕ → ℂ} {γ : ℂ → ℂ}
    (hYmem : ∀ q ∈ Ω, Y q ∈ recurrenceFamily m x q (γ q))
    (hYhol : ∀ j < 2 * m, DifferentiableOn ℂ (fun q => Y q j) Ω)
    (hγ : DifferentiableOn ℂ γ Ω) :
    ∃ s : ℂ → ℕ → ℂ, (∀ k, DifferentiableOn ℂ (fun q => s q k) Ω) ∧
      ∀ q ∈ Ω, ∀ j : ℕ, Y q j = (if Cx m x = 0 then 0 else γ q) * lambertSolution m x x q j +
        ∑ k ∈ Icc 1 (2 * m), s q k * lambertSolution m x (omega m ^ k) q j := by
  have hΩball : Ω ⊆ Metric.ball 0 1 := fun q hq => mem_ball_zero_iff.mpr (hΩsub hq).2
  set a : ℂ → ℂ := fun q => if Cx m x = 0 then 0 else γ q with ha
  have had : DifferentiableOn ℂ a Ω := by
    by_cases h : Cx m x = 0
    · simp only [ha, h, ite_true]; exact differentiableOn_const _
    · simp only [ha, h, ite_false]; exact hγ
  set v : ℂ → Fin (2 * m) → ℂ := fun q t => Y q t - a q * lambertSolution m x x q t with hv
  set s₀ : ℂ → Fin (2 * m) → ℂ :=
    fun q => (eigenWindow m x q).det⁻¹ • (eigenWindow m x q).cramer (v q) with hs₀
  have hdet : ∀ q ∈ Ω, (eigenWindow m x q).det ≠ 0 := fun q hq =>
    det_eigenWindow_ne_zero hm hx (norm_pos_iff.mp (hΩsub hq).1) (hΩsub hq).2
  have hentry : ∀ (k : ℕ) (t : ℕ), DifferentiableOn ℂ
      (fun q => eigenSolution m x q k t) Ω := fun k t =>
    (differentiableOn_lambertSolution hx (norm_omega_pow m k) t).mono hΩball
  have hvd : ∀ t, DifferentiableOn ℂ (fun q => v q t) Ω := fun t =>
    (hYhol t t.2).sub (had.mul ((differentiableOn_lambertSolution hx hx t).mono hΩball))
  have hs₀d : ∀ i, DifferentiableOn ℂ (fun q => s₀ q i) Ω := by
    intro i
    simp only [hs₀, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
    refine DifferentiableOn.mul ?_ (differentiableOn_det fun t j => ?_)
    · exact (differentiableOn_det fun t j => hentry _ _).inv hdet
    · simp only [Matrix.updateCol_apply]
      split_ifs
      · exact hvd t
      · exact hentry _ _
  refine ⟨fun q k => if hk : 1 ≤ k ∧ k ≤ 2 * m then s₀ q ⟨k - 1, by omega⟩ else 0,
    fun k => ?_, fun q hq j => ?_⟩
  · by_cases hk : 1 ≤ k ∧ k ≤ 2 * m
    · simp only [hk, and_self, dite_true]
      exact hs₀d _
    · simp only [hk, dite_false]
      exact differentiableOn_const _
  obtain ⟨s, hs⟩ := exists_lambertSolution_decomposition_of_mem hm hx
    (norm_pos_iff.mp (hΩsub hq).1) (hΩsub hq).2 (hYmem q hq)
  -- the coefficients `s` solve `M(q) s = v(q)`, hence agree with Cramer's solution
  have hMs : (eigenWindow m x q).mulVec (fun i : Fin (2 * m) => s (i + 1)) = v q := by
    funext t
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hv]
    rw [hs t, add_sub_cancel_left, sum_Icc_one_eq_sum_fin]
    exact sum_congr rfl fun i _ => by simp [eigenSolution, mul_comm]
  have hMs₀ : (eigenWindow m x q).mulVec (s₀ q) = v q := by
    simp only [hs₀, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul,
      inv_mul_cancel₀ (hdet q hq), one_smul]
  have hinj : Function.Injective (eigenWindow m x q).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (hdet q hq)))
  have heq : (fun i : Fin (2 * m) => s (i + 1)) = s₀ q := hinj (hMs.trans hMs₀.symm)
  rw [hs j]
  congr 1
  rw [sum_Icc_one_eq_sum_fin, sum_Icc_one_eq_sum_fin]
  refine sum_congr rfl fun i _ => ?_
  have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ 2 * m := ⟨by omega, by omega⟩
  simp only [hi, and_self, dite_true, add_tsub_cancel_right, Fin.eta]
  rw [← congrFun heq i]

end HigherDyson3
