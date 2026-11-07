/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Characterization.LambertSolutions
public import HigherDyson3.Characterization.CesaroUniqueness

/-!
# The solution space of the finite recurrence

For `m ≥ 2`, `|x| = 1` and `0 < |q| < 1`, the solution family `V_γ` of the recurrence
`∑_{r=0}^{d-1} x^r Y_{j+r-2} - q^{j-1} Y_j = C_x γ` is an affine space over the
`(d-1)`-dimensional space `V_0`, any `d - 1` consecutive values determine a solution, and the
eigen-solutions `Z^{(k)} = (S_j(ω^k))_j`, `1 ≤ k ≤ d - 1`, form a basis of `V_0`
[AOS, Lemma 7.3].

## Main results

* `HigherDyson3.window_bijective`: [AOS, Lemma 7.3(a)], bijectivity of
  `Y ↦ (Y_J, …, Y_{J+d-2})`.
* `HigherDyson3.finrank_recurrenceKernel`: `dim V_0 = d - 1`.
* `HigherDyson3.eigenSolution_mem`, `HigherDyson3.eq_zero_of_sum_eigenSolution_eq_zero`,
  `HigherDyson3.exists_eq_sum_eigenSolution`: [AOS, Lemma 7.3(b)].
* `HigherDyson3.exists_decomposition`, `HigherDyson3.decomposition_unique`: [AOS, Lemma 7.3(c)].
* `HigherDyson3.Cx_eq_zero_iff`: `C_x = 0` iff `x = ω^{k₀}` with `1 ≤ k₀ ≤ d - 1`.
-/

public section

noncomputable section

open Complex Finset Filter Topology

namespace HigherDyson3

variable {m : ℕ} {x q : ℂ}

/-! ### The root of unity `ω` -/

theorem isPrimitiveRoot_omega (m : ℕ) : IsPrimitiveRoot (omega m) (2 * m + 1) := by
  have h := Complex.isPrimitiveRoot_exp (2 * m + 1) (by omega)
  convert h using 2
  rw [omega, e]
  push_cast
  congr 1
  ring

theorem norm_omega_pow (m k : ℕ) : ‖omega m ^ k‖ = 1 := by
  rw [norm_pow, (isPrimitiveRoot_omega m).norm'_eq_one (by omega), one_pow]

theorem omega_pow_ne_one {k : ℕ} (hk : k ∈ Icc 1 (2 * m)) : omega m ^ k ≠ 1 := by
  rw [mem_Icc] at hk
  intro h
  have := (isPrimitiveRoot_omega m).dvd_of_pow_eq_one k h
  have := Nat.le_of_dvd (by omega) this
  omega

/-- `C_{ω^k} = 0` for `1 ≤ k ≤ d - 1`. -/
theorem Cx_omega_pow {k : ℕ} (hk : k ∈ Icc 1 (2 * m)) : Cx m (omega m ^ k) = 0 := by
  have h1 : Cx m (omega m ^ k) * (1 - omega m ^ k) = 1 - (omega m ^ k) ^ (2 * m + 1) :=
    geom_sum_mul_neg _ _
  rw [← pow_mul, mul_comm k, pow_mul, (isPrimitiveRoot_omega m).pow_eq_one, one_pow,
    sub_self] at h1
  exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (omega_pow_ne_one hk).symm)

/-- **`C_x = 0` iff `x = ω^{k₀}`** for some `1 ≤ k₀ ≤ d - 1` [AOS, §7]. -/
theorem Cx_eq_zero_iff : Cx m x = 0 ↔ ∃ k ∈ Icc 1 (2 * m), x = omega m ^ k := by
  constructor
  · intro h
    have h1 : Cx m x * (1 - x) = 1 - x ^ (2 * m + 1) := geom_sum_mul_neg _ _
    rw [h, zero_mul, eq_comm, sub_eq_zero, eq_comm] at h1
    obtain ⟨k, hk, hxk⟩ := (isPrimitiveRoot_omega m).eq_pow_of_pow_eq_one h1
    refine ⟨k, mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun hk0 => ?_, by omega⟩, hxk.symm⟩
    subst hk0
    rw [pow_zero] at hxk
    subst hxk
    have h2 : ((2 * m + 1 : ℕ) : ℂ) = 0 := by simpa [Cx, cyclotomicSum] using h
    exact absurd (Nat.cast_eq_zero.mp h2) (by omega)
  · rintro ⟨k, hk, rfl⟩
    exact Cx_omega_pow hk

theorem omega_pow_injOn {k k' : ℕ} (hk : k ∈ Icc 1 (2 * m)) (hk' : k' ∈ Icc 1 (2 * m))
    (h : omega m ^ k = omega m ^ k') : k = k' := by
  rw [mem_Icc] at hk hk'
  exact (isPrimitiveRoot_omega m).pow_inj (by omega) (by omega) h

/-! ### Linearity -/

/-- The left-hand side `∑_{r=0}^{d-1} x^r Y_{j+r-2} - q^{j-1} Y_j` is linear in `Y`. -/
private theorem recurrence_lhs_smul_add (Y Y' : ℕ → ℂ) (a b : ℂ) (j : ℕ) :
    ∑ r ∈ range (2 * m + 1), x ^ r * (a • Y + b • Y') (j + r - 2) -
        q ^ (j - 1) * (a • Y + b • Y') j =
      a * (∑ r ∈ range (2 * m + 1), x ^ r * Y (j + r - 2) - q ^ (j - 1) * Y j) +
        b * (∑ r ∈ range (2 * m + 1), x ^ r * Y' (j + r - 2) - q ^ (j - 1) * Y' j) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sub, mul_sum, mul_add, sum_add_distrib]
  rw [show ∑ i ∈ range (2 * m + 1), x ^ i * (a * Y (j + i - 2)) =
      ∑ i ∈ range (2 * m + 1), a * (x ^ i * Y (j + i - 2)) from sum_congr rfl fun _ _ => by ring,
    show ∑ i ∈ range (2 * m + 1), x ^ i * (b * Y' (j + i - 2)) =
      ∑ i ∈ range (2 * m + 1), b * (x ^ i * Y' (j + i - 2)) from sum_congr rfl fun _ _ => by ring]
  ring

/-- Linearity of the recurrence in `(Y, γ)`: `a Y + b Y' ∈ V_{aγ + bγ'}` [AOS, §7]. -/
theorem smul_add_smul_mem {γ γ' : ℂ} {Y Y' : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ)
    (hY' : Y' ∈ recurrenceFamily m x q γ') (a b : ℂ) :
    a • Y + b • Y' ∈ recurrenceFamily m x q (a * γ + b * γ') := by
  intro j hj
  rw [recurrence_lhs_smul_add, hY j hj, hY' j hj]
  ring

/-- The homogeneous solution space `V_0`, as a submodule of `ℕ → ℂ`. -/
def recurrenceKernel (m : ℕ) (x q : ℂ) : Submodule ℂ (ℕ → ℂ) where
  carrier := recurrenceFamily m x q 0
  add_mem' {Y Y'} hY hY' := by
    simpa using smul_add_smul_mem hY hY' 1 1
  zero_mem' j _ := by simp
  smul_mem' a {Y} hY := by
    simpa using smul_add_smul_mem hY hY a 0

theorem mem_recurrenceKernel {Y : ℕ → ℂ} :
    Y ∈ recurrenceKernel m x q ↔ Y ∈ recurrenceFamily m x q 0 := Iff.rfl

theorem sub_mem_recurrenceKernel {γ : ℂ} {Y Y' : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ)
    (hY' : Y' ∈ recurrenceFamily m x q γ) : Y - Y' ∈ recurrenceKernel m x q := by
  have := smul_add_smul_mem hY hY' 1 (-1)
  exact mem_recurrenceKernel.mpr (by simpa [sub_eq_add_neg] using this)

theorem add_mem_recurrenceFamily {γ : ℂ} {Y W : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ)
    (hW : W ∈ recurrenceKernel m x q) : Y + W ∈ recurrenceFamily m x q γ := by
  simpa using smul_add_smul_mem hY hW 1 1

theorem smul_mem_recurrenceFamily {γ : ℂ} {Y : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ)
    (a : ℂ) : a • Y ∈ recurrenceFamily m x q (a * γ) := by
  simpa using smul_add_smul_mem hY hY a 0

/-- If `C_x = 0`, the right-hand side vanishes and `V_γ = V_0` for every `γ` [AOS, §7]. -/
theorem recurrenceFamily_eq_of_Cx_eq_zero (h : Cx m x = 0) (γ : ℂ) :
    recurrenceFamily m x q γ = recurrenceFamily m x q 0 := by
  ext Y
  simp [recurrenceFamily, h]

/-! ### The Lambert-type solutions in `V` -/

/-- `(S_n(c))_{n ≥ 0} ∈ V_γ` whenever `λ^{j-2} C_c = C_x γ` for all `j`. -/
theorem lambertSolution_mem {c γ : ℂ} (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (hγ : ∀ j : ℤ, (c / x) ^ (j - 2) * Cx m c = Cx m x * γ) :
    (fun n : ℕ => lambertSolution m x c q n) ∈ recurrenceFamily m x q γ := by
  intro j hj
  have h := lambertSolution_recurrence (m := m) hx hc hq0 hq1 (j : ℤ)
  rw [hγ] at h
  rw [← h]
  beta_reduce
  congr 1
  · refine sum_congr rfl fun r _ => ?_
    congr 2
    push_cast [Nat.cast_sub (by omega : 2 ≤ j + r)]
    ring
  · rw [← zpow_natCast, Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]

/-- **The eigen-solutions lie in `V_0`** [AOS, proof of Lemma 7.3(b)]. -/
theorem eigenSolution_mem (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {k : ℕ}
    (hk : k ∈ Icc 1 (2 * m)) : eigenSolution m x q k ∈ recurrenceFamily m x q 0 :=
  lambertSolution_mem hx (norm_omega_pow m k) hq0 hq1 fun j => by
    rw [Cx_omega_pow hk]; ring

/-- **`X(x;q)/G_d(x;q) ∈ V_1`** [AOS, Lemma 7.3(c)]. -/
theorem dysonSequence_mem (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    (fun j : ℕ => XSeries m x j q / GProduct m x q) ∈ recurrenceFamily m x q 1 := by
  have h := lambertSolution_mem (m := m) (γ := 1) hx hx hq0 hq1 fun j => by
    rw [div_self (ne_zero_of_norm_eq_one hx), one_zpow, one_mul, mul_one]
  simpa only [lambertSolution_self hm hx hq1] using h

/-- If `x = ω^{k₀}`, then `Z^{(k₀)} = X(x;q)/G_d(x;q)` [AOS, Lemma 7.3(c)]. -/
theorem eigenSolution_eq_dysonSequence (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq1 : ‖q‖ < 1) {k : ℕ}
    (hxk : x = omega m ^ k) :
    eigenSolution m x q k = fun j : ℕ => XSeries m x j q / GProduct m x q := by
  funext j
  rw [eigenSolution, ← hxk, lambertSolution_self hm hx hq1]

/-- `S_j(c) - λ^j → 0` as `j → ∞`, by [AOS, (7.6)]. -/
theorem tendsto_lambertSolution_sub_pow {c : ℂ} (hx : ‖x‖ = 1) (hc : ‖c‖ = 1) (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) :
    Tendsto (fun j : ℕ => lambertSolution m x c q j - (c / x) ^ j) atTop (𝓝 0) := by
  have hl := div_ne_zero_of_norm hx hc
  refine squeeze_zero_norm (a := fun j : ℕ => hRatioBound m ‖q‖ / (1 - ‖q‖) * ‖q‖ ^ (j + 1))
    (fun j => ?_) ?_
  · have h := norm_lambertSolution_sub_le (m := m) (norm_nonneg q) hq1 hx hc hq0 le_rfl j
    refine le_of_eq_of_le ?_ h
    have hj : lambertSolution m x c q j - (c / x) ^ j =
        (c / x) ^ j * ((c / x) ^ (-(j : ℤ)) * lambertSolution m x c q j - 1) := by
      rw [mul_sub, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hl, add_neg_cancel, zpow_zero,
        one_mul, mul_one]
    rw [hj, norm_mul, norm_pow, norm_div_eq_one hx hc, one_pow, one_mul]
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq1).comp
      (tendsto_add_atTop_nat 1)
    simpa using this.const_mul (hRatioBound m ‖q‖ / (1 - ‖q‖))

/-- **Independence of the eigen-solutions, asymptotic form.** If
`∑_{k=1}^{d-1} s_k Z^{(k)}_j → 0`, then all `s_k` vanish [AOS, proof of Lemma 7.3(b)]. -/
theorem eq_zero_of_tendsto_sum_eigenSolution (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {s : ℕ → ℂ}
    (h : Tendsto (fun j : ℕ => ∑ k ∈ Icc 1 (2 * m), s k * eigenSolution m x q k j) atTop (𝓝 0)) :
    ∀ k ∈ Icc 1 (2 * m), s k = 0 := by
  have hx0 := ne_zero_of_norm_eq_one hx
  have h2 : Tendsto (fun j : ℕ => ∑ k ∈ Icc 1 (2 * m), s k * (omega m ^ k / x) ^ j) atTop
      (𝓝 0) := by
    have hd : Tendsto (fun j : ℕ => ∑ k ∈ Icc 1 (2 * m),
        s k * (eigenSolution m x q k j - (omega m ^ k / x) ^ j)) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Icc 1 (2 * m)) fun k _ =>
        (tendsto_lambertSolution_sub_pow (m := m) hx (norm_omega_pow m k) hq0 hq1).const_mul (s k)
      simpa [eigenSolution] using this
    have h3 := h.sub hd
    rw [sub_zero] at h3
    refine h3.congr fun j => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  classical
  have hz := eq_zero_of_tendsto_sum_mul_pow (ι := Icc 1 (2 * m))
    (μ := fun k => omega m ^ (k : ℕ) / x)
    (s := fun k => s k)
    (fun k k' hkk' => Subtype.ext (omega_pow_injOn k.2 k'.2 ((div_left_inj' hx0).mp hkk')))
    (fun k => by rw [norm_div, norm_omega_pow, hx, div_one])
    (h2.congr fun j => (sum_coe_sort (Icc 1 (2 * m)) fun k => s k * (omega m ^ k / x) ^ j).symm)
  exact fun k hk => congrFun hz ⟨k, hk⟩

/-! ### Windows -/

/-- **Two consecutive windows determine a homogeneous solution.** If `Y ∈ V_0` vanishes at
`J, …, J + d - 2`, then `Y = 0` [AOS, proof of Lemma 7.3(a)]. -/
theorem eq_zero_of_window_eq_zero (hm : 2 ≤ m) (hx0 : x ≠ 0) {Y : ℕ → ℂ}
    (hY : Y ∈ recurrenceFamily m x q 0) (J : ℕ) (hJ : ∀ t < 2 * m, Y (J + t) = 0) : Y = 0 := by
  have hfwd : ∀ n, J ≤ n → Y n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hlt : n < J + 2 * m
      · have := hJ (n - J) (by omega)
        rwa [Nat.add_sub_cancel' hn] at this
      · obtain ⟨j, hjdef⟩ : ∃ j, j = n + 2 - 2 * m := ⟨_, rfl⟩
        have h := hY j (by omega)
        rw [sum_range_succ, mul_zero] at h
        have hsum : ∑ r ∈ range (2 * m), x ^ r * Y (j + r - 2) = 0 := sum_eq_zero fun r hr => by
          rw [mem_range] at hr
          rw [ih (j + r - 2) (by omega) (by omega), mul_zero]
        rw [hsum, ih j (by omega) (by omega), zero_add, mul_zero, sub_zero,
          show j + 2 * m - 2 = n by omega] at h
        exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hx0)
  have hbwd : ∀ k n, J ≤ n + k → Y n = 0 := by
    intro k
    induction k with
    | zero => exact fun n hn => hfwd n (by omega)
    | succ k ih =>
      intro n hn
      by_cases hnk : J ≤ n + k
      · exact ih n hnk
      · have h := hY (n + 2) (by omega)
        rw [sum_range_succ', mul_zero] at h
        have hsum : ∑ r ∈ range (2 * m), x ^ (r + 1) * Y (n + 2 + (r + 1) - 2) = 0 :=
          sum_eq_zero fun r _ => by rw [ih _ (by omega), mul_zero]
        rwa [hsum, ih (n + 2) (by omega), zero_add, mul_zero, sub_zero, pow_zero, one_mul,
          show n + 2 + 0 - 2 = n by omega] at h
  funext n
  exact hbwd J n (by omega)

/-- The window `(Y_J, …, Y_{J+d-2})` of a sequence, as a linear map. -/
def window (m J : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (Fin (2 * m) → ℂ) where
  toFun Y t := Y (J + t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem window_apply (J : ℕ) (Y : ℕ → ℂ) (t : Fin (2 * m)) :
    window m J Y t = Y (J + t) := (rfl)

theorem sum_Icc_one_eq_sum_fin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ k ∈ Icc 1 n, f k = ∑ i : Fin n, f (i + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) n, range_eq_Ico, sum_Ico_add', zero_add]
  congr 1

/-- Extension of `g : Fin (d-1) → ℂ` to `ℕ`, supported on `1, …, d-1`. -/
def finExtend (m : ℕ) (g : Fin (2 * m) → ℂ) (k : ℕ) : ℂ :=
  if h : 1 ≤ k ∧ k ≤ 2 * m then g ⟨k - 1, by omega⟩ else 0

theorem finExtend_succ (g : Fin (2 * m) → ℂ) (i : Fin (2 * m)) : finExtend m g (i + 1) = g i := by
  have h : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ 2 * m := ⟨by omega, by omega⟩
  simp only [finExtend, h, and_self, ↓reduceDIte, Nat.add_sub_cancel]

theorem sum_finExtend_smul {M : Type*} [AddCommMonoid M] [Module ℂ M] (g : Fin (2 * m) → ℂ)
    (F : ℕ → M) : ∑ k ∈ Icc 1 (2 * m), finExtend m g k • F k = ∑ i, g i • F (i + 1) := by
  rw [sum_Icc_one_eq_sum_fin]
  simp only [finExtend_succ]

/-- The windows of the eigen-solutions are linearly independent. -/
theorem linearIndependent_window (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (J : ℕ) :
    LinearIndependent ℂ fun i : Fin (2 * m) => window m J (eigenSolution m x q (i + 1)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set V : ℕ → ℂ := ∑ i, g i • eigenSolution m x q (i + 1) with hV
  have hVmem : V ∈ recurrenceKernel m x q :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (eigenSolution_mem hx hq0 hq1 (mem_Icc.mpr ⟨by omega, by omega⟩))
  have hV0 : V = 0 := by
    refine eq_zero_of_window_eq_zero hm (ne_zero_of_norm_eq_one hx) hVmem J fun t ht => ?_
    have := congrFun hg ⟨t, ht⟩
    simpa [hV, Finset.sum_apply] using this
  have hz := eq_zero_of_tendsto_sum_eigenSolution (m := m) hx hq0 hq1 (s := finExtend m g) (by
    refine tendsto_const_nhds.congr fun j => ?_
    have := congrFun hV0 j
    rw [hV] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    exact (sum_finExtend_smul g (fun k => eigenSolution m x q k j)).symm)
  rw [← finExtend_succ g i]
  exact hz _ (mem_Icc.mpr ⟨by omega, by omega⟩)

theorem span_window_eq_top (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (J : ℕ) :
    Submodule.span ℂ (Set.range fun i : Fin (2 * m) => window m J (eigenSolution m x q (i + 1))) =
      ⊤ := by
  have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  exact (linearIndependent_window hm hx hq0 hq1 J).span_eq_top_of_card_eq_finrank (by simp)

/-- Every window is a combination of the windows of the eigen-solutions. -/
theorem exists_window_eq (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (J : ℕ)
    (v : Fin (2 * m) → ℂ) :
    ∃ g : Fin (2 * m) → ℂ, window m J (∑ i, g i • eigenSolution m x q (i + 1)) = v := by
  have hv : v ∈ Submodule.span ℂ
      (Set.range fun i : Fin (2 * m) => window m J (eigenSolution m x q (i + 1))) := by
    rw [span_window_eq_top hm hx hq0 hq1]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  exact ⟨g, by rw [map_sum]; simpa only [map_smul] using hg⟩

theorem sum_smul_eigenSolution_mem (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (g : Fin (2 * m) → ℂ) :
    ∑ i, g i • eigenSolution m x q (i + 1) ∈ recurrenceKernel m x q :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _
    (eigenSolution_mem hx hq0 hq1 (mem_Icc.mpr ⟨by omega, by omega⟩))

/-- **Lemma 7.3(b), spanning.** Every `Y ∈ V_0` is a combination
`∑_{k=1}^{d-1} s_k Z^{(k)}` [AOS, Lemma 7.3(b)]. -/
theorem exists_eq_sum_eigenSolution (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {Y : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q 0) :
    ∃ s : ℕ → ℂ, Y = ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k := by
  obtain ⟨g, hg⟩ := exists_window_eq hm hx hq0 hq1 0 (window m 0 Y)
  refine ⟨finExtend m g, ?_⟩
  rw [sum_finExtend_smul]
  have hd := sub_mem_recurrenceKernel hY (sum_smul_eigenSolution_mem hx hq0 hq1 g)
  have h0 := eq_zero_of_window_eq_zero hm (ne_zero_of_norm_eq_one hx) hd 0 fun t ht => by
    have := congrFun hg ⟨t, ht⟩
    simp only [window_apply, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.sub_apply, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      this, sub_self]
  exact (sub_eq_zero.mp h0)

/-- **Lemma 7.3(b), independence.** If `∑_{k=1}^{d-1} s_k Z^{(k)} = 0`, then all `s_k`
vanish [AOS, Lemma 7.3(b)]. -/
theorem eq_zero_of_sum_eigenSolution_eq_zero (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {s : ℕ → ℂ} (h : ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k = 0) :
    ∀ k ∈ Icc 1 (2 * m), s k = 0 :=
  eq_zero_of_tendsto_sum_eigenSolution hx hq0 hq1 (tendsto_const_nhds.congr fun j => by
    have := congrFun h j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this.symm)

/-- **Lemma 7.3(b).** The eigen-solutions `Z^{(1)}, …, Z^{(d-1)}` form a basis of `V_0`
[AOS, Lemma 7.3(b)]. -/
theorem eigenSolution_basis (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    (∀ k ∈ Icc 1 (2 * m), eigenSolution m x q k ∈ recurrenceFamily m x q 0) ∧
      (∀ s : ℕ → ℂ, ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k = 0 →
        ∀ k ∈ Icc 1 (2 * m), s k = 0) ∧
      ∀ Y ∈ recurrenceFamily m x q 0,
        ∃ s : ℕ → ℂ, Y = ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k :=
  ⟨fun _ hk => eigenSolution_mem hx hq0 hq1 hk,
    fun _ h => eq_zero_of_sum_eigenSolution_eq_zero hx hq0 hq1 h,
    fun _ hY => exists_eq_sum_eigenSolution hm hx hq0 hq1 hY⟩

/-- A homogeneous solution tending to `0` vanishes. -/
theorem eq_zero_of_tendsto_zero (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {W : ℕ → ℂ} (hW : W ∈ recurrenceFamily m x q 0) (hlim : Tendsto W atTop (𝓝 0)) : W = 0 := by
  obtain ⟨s, rfl⟩ := exists_eq_sum_eigenSolution hm hx hq0 hq1 hW
  have hs := eq_zero_of_tendsto_sum_eigenSolution (m := m) hx hq0 hq1 (s := s)
    (hlim.congr fun j => by
    simp [Finset.sum_apply])
  exact sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]

/-- A particular solution in `V_γ`: `γ X/G_d` if `C_x ≠ 0`, and `0` if `C_x = 0`. -/
theorem exists_mem_recurrenceFamily (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    (γ : ℂ) :
    (if Cx m x = 0 then 0 else γ) • (fun j : ℕ => XSeries m x j q / GProduct m x q) ∈
      recurrenceFamily m x q γ := by
  split_ifs with h
  · rw [recurrenceFamily_eq_of_Cx_eq_zero h, zero_smul]
    exact (recurrenceKernel m x q).zero_mem
  · simpa using smul_mem_recurrenceFamily (dysonSequence_mem hm hx hq0 hq1) γ

/-- **Lemma 7.3(a).** For every `γ` and `J ≥ 0`, `Y ↦ (Y_J, …, Y_{J+d-2})` is a bijection
`V_γ → ℂ^{d-1}` [AOS, Lemma 7.3(a)]. -/
theorem window_bijective (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) (γ : ℂ)
    (J : ℕ) :
    Function.Bijective fun Y : recurrenceFamily m x q γ =>
      fun t : Fin (2 * m) => (Y : ℕ → ℂ) (J + t) := by
  constructor
  · rintro ⟨Y, hY⟩ ⟨Y', hY'⟩ h
    refine Subtype.ext (sub_eq_zero.mp ?_)
    refine eq_zero_of_window_eq_zero hm (ne_zero_of_norm_eq_one hx)
      (sub_mem_recurrenceKernel hY hY') J fun t ht => ?_
    have := congrFun h ⟨t, ht⟩
    simp only at this
    simp [this]
  · intro v
    have hY0 := exists_mem_recurrenceFamily hm hx hq0 hq1 γ
    set Y0 := (if Cx m x = 0 then 0 else γ) • (fun j : ℕ => XSeries m x j q / GProduct m x q)
    obtain ⟨g, hg⟩ := exists_window_eq hm hx hq0 hq1 J (v - window m J Y0)
    refine ⟨⟨Y0 + ∑ i, g i • eigenSolution m x q (i + 1),
      add_mem_recurrenceFamily hY0 (sum_smul_eigenSolution_mem hx hq0 hq1 g)⟩, ?_⟩
    funext t
    have := congrFun hg t
    simp only [window_apply, Pi.sub_apply] at this
    simp only [Pi.add_apply, this]
    ring

/-- **Lemma 7.3(a), dimension.** `dim V_0 = d - 1` [AOS, Lemma 7.3(a)]. -/
theorem finrank_recurrenceKernel (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    Module.finrank ℂ (recurrenceKernel m x q) = 2 * m := by
  have hb := window_bijective hm hx hq0 hq1 0 0
  let f : recurrenceKernel m x q →ₗ[ℂ] (Fin (2 * m) → ℂ) :=
    (window m 0).comp (recurrenceKernel m x q).subtype
  have hf : Function.Bijective f := hb
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_fin_fun]

/-- **Lemma 7.3(a), affine structure.** `V_γ = Y⁰ + V_0` for any `Y⁰ ∈ V_γ`
[AOS, Lemma 7.3(a)]. -/
theorem recurrenceFamily_eq_add {γ : ℂ} {Y₀ : ℕ → ℂ} (hY₀ : Y₀ ∈ recurrenceFamily m x q γ) :
    recurrenceFamily m x q γ = (fun W => Y₀ + W) '' recurrenceFamily m x q 0 := by
  ext Y
  constructor
  · intro hY
    exact ⟨Y - Y₀, sub_mem_recurrenceKernel hY hY₀, by simp⟩
  · rintro ⟨W, hW, rfl⟩
    exact add_mem_recurrenceFamily hY₀ hW

/-- **Lemma 7.3(c), existence.** Every `Y ∈ V_γ` decomposes as
`Y = γ' X(x;q)/G_d(x;q) + ∑_{k=1}^{d-1} s_k Z^{(k)}`, where `γ' = γ` if `C_x ≠ 0` and `γ' = 0`
if `C_x = 0` [AOS, (7.13) and Lemma 7.3(c)]. -/
theorem exists_decomposition (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1)
    {γ : ℂ} {Y : ℕ → ℂ} (hY : Y ∈ recurrenceFamily m x q γ) :
    ∃ s : ℕ → ℂ, Y = (if Cx m x = 0 then 0 else γ) •
        (fun j : ℕ => XSeries m x j q / GProduct m x q) +
      ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k := by
  obtain ⟨s, hs⟩ := exists_eq_sum_eigenSolution hm hx hq0 hq1
    (sub_mem_recurrenceKernel hY (exists_mem_recurrenceFamily hm hx hq0 hq1 γ))
  exact ⟨s, by rw [← hs]; abel⟩

/-- **Lemma 7.3(c), uniqueness.** The coefficients `s_k` of the decomposition are unique
[AOS, Lemma 7.3(c)]. -/
theorem decomposition_unique (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) {s t : ℕ → ℂ}
    (h : ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k =
      ∑ k ∈ Icc 1 (2 * m), t k • eigenSolution m x q k) :
    ∀ k ∈ Icc 1 (2 * m), s k = t k := by
  have h0 : ∑ k ∈ Icc 1 (2 * m), (s - t) k • eigenSolution m x q k = 0 := by
    simp only [Pi.sub_apply, sub_smul, sum_sub_distrib, h, sub_self]
  exact fun k hk => sub_eq_zero.mp (eq_zero_of_sum_eigenSolution_eq_zero hx hq0 hq1 h0 k hk)

/-- **Lemma 7.3** [AOS, Lemma 7.3]. Let `m ≥ 2`, `|x| = 1`, `0 < |q| < 1`.
(a) For every `γ` and `J`, `Y ↦ (Y_J, …, Y_{J+d-2})` is a bijection `V_γ → ℂ^{d-1}`;
`dim V_0 = d - 1`; and `V_γ = Y⁰ + V_0` for every `Y⁰ ∈ V_γ`.
(b) `Z^{(1)}, …, Z^{(d-1)}` form a basis of `V_0`.
(c) `X/G_d ∈ V_1`; every `Y ∈ V_γ` is `γ' X/G_d + ∑_k s_k Z^{(k)}` with `γ' = γ` if `C_x ≠ 0`
and `γ' = 0` if `C_x = 0`, with unique `s_k`; and if `C_x = 0`, then `x = ω^{k₀}` for some
`1 ≤ k₀ ≤ d - 1`, `Z^{(k₀)} = X/G_d`, and `V_γ = V_0` for every `γ`. -/
theorem solutionSpace_structure (hm : 2 ≤ m) (hx : ‖x‖ = 1) (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    (∀ (γ : ℂ) (J : ℕ), Function.Bijective fun Y : recurrenceFamily m x q γ =>
      fun t : Fin (2 * m) => (Y : ℕ → ℂ) (J + t)) ∧
    Module.finrank ℂ (recurrenceKernel m x q) = 2 * m ∧
    (∀ (γ : ℂ) (Y₀ : ℕ → ℂ), Y₀ ∈ recurrenceFamily m x q γ →
      recurrenceFamily m x q γ = (fun W => Y₀ + W) '' recurrenceFamily m x q 0) ∧
    ((∀ k ∈ Icc 1 (2 * m), eigenSolution m x q k ∈ recurrenceFamily m x q 0) ∧
      (∀ s : ℕ → ℂ, ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k = 0 →
        ∀ k ∈ Icc 1 (2 * m), s k = 0) ∧
      ∀ Y ∈ recurrenceFamily m x q 0,
        ∃ s : ℕ → ℂ, Y = ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k) ∧
    (fun j : ℕ => XSeries m x j q / GProduct m x q) ∈ recurrenceFamily m x q 1 ∧
    (∀ (γ : ℂ) (Y : ℕ → ℂ), Y ∈ recurrenceFamily m x q γ →
      ∃ s : ℕ → ℂ, Y = (if Cx m x = 0 then 0 else γ) •
          (fun j : ℕ => XSeries m x j q / GProduct m x q) +
        ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k) ∧
    (∀ s t : ℕ → ℂ, ∑ k ∈ Icc 1 (2 * m), s k • eigenSolution m x q k =
      ∑ k ∈ Icc 1 (2 * m), t k • eigenSolution m x q k → ∀ k ∈ Icc 1 (2 * m), s k = t k) ∧
    (Cx m x = 0 → (∃ k₀ ∈ Icc 1 (2 * m), x = omega m ^ k₀ ∧
      eigenSolution m x q k₀ = fun j : ℕ => XSeries m x j q / GProduct m x q) ∧
      ∀ γ : ℂ, recurrenceFamily m x q γ = recurrenceFamily m x q 0) :=
  ⟨window_bijective hm hx hq0 hq1, finrank_recurrenceKernel hm hx hq0 hq1,
    fun _ _ h => recurrenceFamily_eq_add h, eigenSolution_basis hm hx hq0 hq1,
    dysonSequence_mem hm hx hq0 hq1, fun _ _ h => exists_decomposition hm hx hq0 hq1 h,
    fun _ _ h => decomposition_unique hx hq0 hq1 h,
    fun h => ⟨(Cx_eq_zero_iff.mp h).imp fun _ hk =>
        ⟨hk.1, hk.2, eigenSolution_eq_dysonSequence hm hx hq1 hk.2⟩,
      recurrenceFamily_eq_of_Cx_eq_zero h⟩⟩

end HigherDyson3
