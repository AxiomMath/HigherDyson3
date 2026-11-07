/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.Convergence
public import HigherDyson3.Bounds.DenominatorBoundRestricted
public import HigherDyson3.Divisor.DivisorNbhdOpen
public import HigherDyson3.Kernel.ExpQuotientHolomorphic
public import HigherDyson3.Kernel.KernelSimplePole

/-!
# The periodization of a Lambert seed has at most simple poles

Let `m ≥ 1`, `x = e(α)`, `c = e(β)` with `β ∈ ℚ ∩ [0,1)`, and let `(b_i)` be holomorphic on
the unit disc with a Gaussian bound. Fix a component `L_{a,k} = {w = -β + aτ + k}` of `𝒟_c`.
Along it exactly the denominators `1 - c u q^{n+i}` with `n + i = -a` vanish
[AOS, proof of Lemma 7.4(a)]. Splitting the double series accordingly,
`ℰ_Φ = R_a + N_a / (1 - c u q^{-a})` off `𝒟_c`, where
* the regular part `R_a`, the sum over `n + i ≠ -a`, is holomorphic on the neighbourhood
  `Ω_{a,k}` of `L_{a,k}`, by the Gaussian majorant with denominators bounded away from zero;
* the singular numerator `N_a = x⁻² ∑_i x^{2(a+i)} q^{m(a+i)²} u^{-2m(a+i)} b_i(q)` collects the
  infinitely many terms with `n = -a - i`; it is holomorphic on `ℍ × ℂ`.

Since `c u q^{-a} = e(w + β - aτ - k)`, multiplying by `z = w + β - aτ - k` gives
`z ℰ_Φ = z R_a + N_a · z / (1 - e(z))`, holomorphic on `Ω_{a,k}`.

## Main results

* `HigherDyson3.seedPeriodization_lambertSeed_eq_regular_add`: the splitting.
* `HigherDyson3.differentiableOn_lambertRegularPart`,
  `HigherDyson3.differentiableOn_lambertSingularNumerator`: holomorphy of the two parts.
* `HigherDyson3.seedPeriodization_lambertSeed_simple_poles`: at most simple poles along `𝒟_c`.
-/

public section

noncomputable section

open Complex

namespace HigherDyson3

/-- The regular part `R_a = ∑_{n + i ≠ -a} ℰ^{dbl}_{n,i}` of the double series of the
periodization of a Lambert seed, the sum of the double summands whose denominator does not
vanish along the components `L_{a,k}`. -/
def lambertRegularPart (m : ℕ) (α β : ℚ) (b : ℕ → ℂ → ℂ) (a : ℤ) (τ w : ℂ) : ℂ :=
  ∑' k : {k : ℤ × ℕ // k.1 + k.2 ≠ -a}, lambertDoubleSummand m α β b k.1.1 k.1.2 τ w

/-- The singular numerator `N_a = x⁻² ∑_{i ≥ 0} x^{-2n} q^{mn²} u^{2mn} b_i(q)`, `n = -a - i`,
of the double series of the periodization of a Lambert seed: the sum of the numerators of the
double summands with denominator `1 - c u q^{-a}`. -/
def lambertSingularNumerator (m : ℕ) (α : ℚ) (b : ℕ → ℂ → ℂ) (a : ℤ) (τ w : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * ∑' i : ℕ, e α ^ (-2 * (-a - i)) * e τ ^ ((m : ℤ) * (-a - i) ^ 2) *
    e w ^ (2 * (m : ℤ) * (-a - i)) * b i (e τ)

/-- The defining formula of `HigherDyson3.lambertSingularNumerator`. -/
lemma lambertSingularNumerator_eq (m : ℕ) (α : ℚ) (b : ℕ → ℂ → ℂ) (a : ℤ) (τ w : ℂ) :
    lambertSingularNumerator m α b a τ w =
      (e α ^ 2)⁻¹ * ∑' i : ℕ, e α ^ (-2 * (-a - i)) * e τ ^ ((m : ℤ) * (-a - i) ^ 2) *
        e w ^ (2 * (m : ℤ) * (-a - i)) * b i (e τ) := (rfl)

/-- On `Ω_{a,k}`, no denominator `1 - c u q^j` with `j ≠ -a` vanishes. -/
lemma one_sub_e_mul_ne_zero_of_mem_divisorNbhd {β : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {a k : ℤ} {p : ℂ × ℂ} (hp : p ∈ divisorNbhd β a k) {j : ℤ} (hj : j ≠ -a) :
    1 - e β * e p.2 * e p.1 ^ j ≠ 0 := by
  intro h
  obtain ⟨k', hk'⟩ := (divisor_char β hβ0 hβ1 (τ := p.1) (w := p.2) hp.1 j).mp h
  refine hp.2 (Set.mem_iUnion₂.mpr ⟨(-j, k'), ?_, hk'⟩)
  intro hc
  exact hj (by have := congrArg Prod.fst hc; simp at this; omega)

/-- **Holomorphy of the regular part** on the neighbourhood `Ω_{a,k}` of `L_{a,k}`. -/
theorem differentiableOn_lambertRegularPart {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (a k : ℤ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => lambertRegularPart m α β b a p.1 p.2)
      (divisorNbhd β a k) := by
  have hcast : ((β : ℝ) : ℂ) = (β : ℂ) := Complex.ofReal_ratCast β
  unfold lambertRegularPart
  refine differentiableOn_tsum_of_normal (divisorNbhd_isOpen β hβ0 hβ1 a k) ?_ ?_
  · intro n p hp
    exact (differentiableAt_lambertDoubleSummand m α β hb _ _ hp.1
      (one_sub_e_mul_ne_zero_of_mem_divisorNbhd hβ0 hβ1 hp n.2)).differentiableWithinAt
  · intro K hK hKc
    have hKH : K ⊆ halfPlaneProd := fun p hp => (hK hp).1
    obtain ⟨A, -, hA⟩ := denominator_bound_restricted (β : ℝ) K hKc hKH {j | j ≠ -a}
      (fun p hp j hj => by
        rw [hcast]; exact one_sub_e_mul_ne_zero_of_mem_divisorNbhd hβ0 hβ1 (hK hp) hj)
    obtain ⟨M, hM, -, hle⟩ := exists_majorant_lambertDoubleSummand hm α β hB K hKc hKH
      {j | j ≠ -a} (A := A) fun p hp j hj => by simpa [hcast] using hA p hp j hj
    exact ⟨fun n => M n, hM.subtype _, fun n p hp => hle n n.2 p hp⟩

/-- A summable majorant for the terms of the singular numerator on a compact subset of
`ℍ × ℂ`. -/
theorem exists_majorant_lambertSingularNumerator {m : ℕ} (α : ℚ) {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (a : ℤ) (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSH : S ⊆ halfPlaneProd) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ i : ℕ, ∀ p ∈ S,
      ‖e α ^ (-2 * (-a - i)) * e p.1 ^ ((m : ℤ) * (-a - i) ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * (-a - i)) * b i (e p.1)‖ ≤ M i := by
  obtain ⟨Q₀, Q, a₀, b₀, -, -, hQ1, ha₀, hab, hbd⟩ := compact_q_u_bounds S hS hSH
  set Q' := max Q 0 with hQ'
  have hQ0 : 0 ≤ Q' := le_max_right _ _
  have hQ1' : Q' < 1 := max_lt hQ1 one_pos
  obtain ⟨B, hB0, hBb⟩ := exists_gaussian_bound_of_le hB hQ1'
  set c := max b₀ a₀⁻¹ with hc
  have hc1 : 1 ≤ c := by
    rcases le_or_gt 1 b₀ with h | h
    · exact le_max_of_le_left h
    · exact le_max_of_le_right ((one_lt_inv₀ ha₀).mpr (hab.trans_lt h)).le
  set V := c ^ (2 * m) with hV
  have hV1 : 1 ≤ V := one_le_pow₀ hc1
  have hG := gaussianSummable_nat (m := 1) le_rfl hQ0 hQ1' hV1
  refine ⟨fun i => B * V ^ a.natAbs * (Q' ^ (1 * i ^ 2) * V ^ i), (hG.mul_left _), ?_⟩
  intro i p hp
  obtain ⟨-, hq, ha, hb'⟩ := hbd p hp
  have hq' : ‖e p.1‖ ≤ Q' := le_max_of_le_left hq
  have hu0 : 0 < ‖e p.2‖ := ha₀.trans_le ha
  have hexp : (m : ℤ) * (-a - i) ^ 2 = ((m * (-a - i).natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs]
  have hqpow : ‖e p.1‖ ^ (m * (-a - (i : ℤ)).natAbs ^ 2) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (hq'.trans hQ1'.le)
  have hu : ‖e p.2‖ ^ (2 * (m : ℤ) * (-a - i)) ≤ V ^ a.natAbs * V ^ i := by
    refine (zpow_le_pow_natAbs (c := c) hu0 (le_max_of_le_left hb')
      (le_max_of_le_right (inv_anti₀ ha₀ ha)) _).trans ?_
    have h1 : (2 * (m : ℤ) * (-a - i)).natAbs ≤ 2 * m * a.natAbs + 2 * m * i := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
      have : (-a - (i : ℤ)).natAbs ≤ a.natAbs + i := by omega
      rw [show (2 : ℤ).natAbs = 2 from rfl, Int.natAbs_natCast]
      nlinarith
    rw [hV, ← pow_mul, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ hc1 h1
  have hbi : ‖b i (e p.1)‖ ≤ B * Q' ^ (i ^ 2) :=
    (hBb i _ hq').trans (by gcongr)
  rw [norm_mul, norm_mul, norm_mul, norm_zpow, norm_zpow, norm_zpow, norm_e_ratCast, one_zpow,
    one_mul, hexp, zpow_natCast]
  calc ‖e p.1‖ ^ (m * (-a - (i : ℤ)).natAbs ^ 2) * ‖e p.2‖ ^ (2 * (m : ℤ) * (-a - i)) *
        ‖b i (e p.1)‖ ≤ 1 * (V ^ a.natAbs * V ^ i) * (B * Q' ^ (i ^ 2)) := by
        gcongr
    _ = B * V ^ a.natAbs * (Q' ^ (1 * i ^ 2) * V ^ i) := by ring

/-- **Holomorphy of the singular numerator** on `ℍ × ℂ`. -/
theorem differentiableOn_lambertSingularNumerator {m : ℕ} (α : ℚ) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (a : ℤ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => lambertSingularNumerator m α b a p.1 p.2)
      halfPlaneProd := by
  have hopen : IsOpen halfPlaneProd :=
    isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)
  unfold lambertSingularNumerator
  refine DifferentiableOn.const_mul ?_ _
  refine differentiableOn_tsum_of_normal hopen (fun i p hp => ?_) fun K hK hKc =>
    exists_majorant_lambertSingularNumerator α hB a K hKc hK
  have hfst : DifferentiableAt ℂ (fun p : ℂ × ℂ => e p.1) p :=
    (e_differentiable _).comp _ differentiableAt_fst
  have hsnd : DifferentiableAt ℂ (fun p : ℂ × ℂ => e p.2) p :=
    (e_differentiable _).comp _ differentiableAt_snd
  exact ((((differentiableAt_const _).mul (hfst.zpow (Or.inl (e_ne_zero _)))).mul
    (hsnd.zpow (Or.inl (e_ne_zero _)))).mul
      (differentiableAt_comp_e_fst (hb i) hp)).differentiableWithinAt

/-- **Splitting off the singular terms.** Off `𝒟_c`,
`ℰ_Φ(τ,w) = R_a(τ,w) + N_a(τ,w) / (1 - c u q^{-a})`. -/
theorem seedPeriodization_lambertSeed_eq_regular_add {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (a : ℤ) {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor β) :
    seedPeriodization m α (lambertSeed (e α) (e β) b) τ w =
      lambertRegularPart m α β b a τ w +
        lambertSingularNumerator m α b a τ w / (1 - e β * e w * e τ ^ (-a)) := by
  obtain ⟨hsum, heq⟩ := seedPeriodization_lambertSeed_eq_tsum_double hm α hβ0 hβ1 hB hτw
  set f : ℤ × ℕ → ℂ := fun k => lambertDoubleSummand m α β b k.1 k.2 τ w with hf
  have hfs : Summable f := hsum.of_norm
  rw [heq, ← hfs.tsum_subtype_add_tsum_subtype_compl {k : ℤ × ℕ | k.1 + k.2 ≠ -a}]
  congr 1
  let E : ℕ ≃ ↥({k : ℤ × ℕ | k.1 + k.2 ≠ -a}ᶜ) :=
    { toFun := fun i => ⟨(-a - i, i), by simp⟩
      invFun := fun k => k.1.2
      left_inv := fun i => rfl
      right_inv := fun k => by
        obtain ⟨⟨n, i⟩, hk⟩ := k
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hk
        ext
        · simp only; omega
        · rfl }
  rw [← E.tsum_eq]
  simp only [E, Equiv.coe_fn_mk, hf, lambertDoubleSummand_eq, lambertSingularNumerator,
    sub_add_cancel]
  rw [← tsum_mul_left, ← tsum_div_const]
  refine tsum_congr fun i => ?_
  ring

/-- **At most simple poles** [AOS, Lemma 7.4(a)]. For `m ≥ 1`, `x = e(α)`, `c = e(β)` with
`0 ≤ β < 1` rational, coefficients `b_i` holomorphic on the unit disc with a Gaussian bound,
and `a, k ∈ ℤ`, there is `N` holomorphic on the neighbourhood `Ω_{a,k}` of
`L_{a,k} = {w = -β + aτ + k}` with `N(τ,w) = (w + β - aτ - k) ℰ_Φ(τ,w)` on `(ℍ × ℂ) \ 𝒟_c`. -/
theorem seedPeriodization_lambertSeed_simple_poles {m : ℕ} (hm : 1 ≤ m) (α : ℚ) {β : ℚ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    (a k : ℤ) :
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd β a k) ∧
      ∀ p ∈ halfPlaneProd \ divisor β,
        N p = (p.2 + β - a * p.1 - k) *
          seedPeriodization m α (lambertSeed (e α) (e β) b) p.1 p.2 := by
  set z : ℂ × ℂ → ℂ := fun p => p.2 + β - a * p.1 - k with hz
  have hzd : Differentiable ℂ z := by rw [hz]; fun_prop
  have hsub : divisorNbhd β a k ⊆ halfPlaneProd := Set.sdiff_subset
  refine ⟨fun p => z p * lambertRegularPart m α β b a p.1 p.2 +
    lambertSingularNumerator m α b a p.1 p.2 * expQuotient (z p), ?_, fun p hp => ?_⟩
  · refine (hzd.differentiableOn.mul
      (differentiableOn_lambertRegularPart hm α hβ0 hβ1 hb hB a k)).add
      (DifferentiableOn.mul ((differentiableOn_lambertSingularNumerator α hb hB a).mono hsub)
        (expQuotient_differentiableOn.2.comp hzd.differentiableOn
          (kernelSimplePole_mapsTo β a k)))
  · have hz0 : z p ≠ 0 := by simpa using kernelSimplePole_ne_int β a k hp 0
    have hEq : expQuotient (z p) = z p / (1 - e β * e p.2 * e p.1 ^ (-a)) := by
      rw [kernelSimplePole_e_mul _ _ _ a k, expQuotient,
        ite_eq_right_of_eq_false _ _ (eq_false hz0)]
    simp only
    rw [hEq, seedPeriodization_lambertSeed_eq_regular_add hm α hβ0 hβ1 hB a hp]
    ring

end HigherDyson3
