/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.AppellLerch
public import HigherDyson3.Divisor.DivisorComplOpen
public import HigherDyson3.Holomorphy.JointRemovable
public import HigherDyson3.Theta.PeriodicFourier

/-!
# Analytic properties of the Appell–Lerch kernels

For `m ≥ 1` and `β ∈ ℚ`, the Appell–Lerch kernel
`A_{m,β}(τ, w) = -∑_{n ∈ ℤ} q^{mn²} u^{2mn} / (1 - e(-β) q^n u)` [AOS, (4.5)]:

* converges normally on compact subsets of `(ℍ × ℂ) \ 𝒟_β`, where
  `𝒟_β = {w ∈ β + ℤτ + ℤ} = divisor (-β)`, and is holomorphic there;
* satisfies `A(τ, w + aτ + b) = q^{-ma²} u^{-2ma} A(τ, w)`, in particular the index-`m`
  elliptic law;
* has at most simple poles: `(w - β - aτ - b) A` extends holomorphically to the neighbourhood
  `Ω_{a,b}` of the component `w = β + aτ + b`, with value `q^{-ma²} e(β)^{-2ma} / (2πi)` there;
* `2πi ε A(τ, β + ε) → 1` as `ε → 0`, i.e. `A(τ, β + ε) = 1/(2πiε) + O(1)`.

These are the parts of [AOS, Proposition 4.3] used in the local polar subtraction
[AOS, Proposition 4.4]. As for the kernel `𝒦_{m,x}`, the singular summand `n = -a` is split off
near `w = β + aτ + b`, and `(w - β - aτ - b) / (1 - e(w - β - aτ - b))` is `expQuotient`.

We also record that `divisor α`, its components and the neighbourhoods `Ω_{a,b}` only depend on
`α` modulo `1`, which extends the openness results for `0 ≤ α < 1` to every `α ∈ ℚ`.
-/

public section

open Complex Filter Topology

namespace HigherDyson3

/-! ### The divisor only depends on `α mod 1` -/

theorem divisorComponent_eq_fract (α : ℚ) (a b : ℤ) :
    divisorComponent α a b = divisorComponent (Int.fract α) a (b - ⌊α⌋) := by
  ext p
  simp only [divisorComponent, Set.mem_ofPred_eq, ← Int.self_sub_floor]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> rw [h2] <;> ring

theorem divisor_eq_fract (α : ℚ) : divisor α = divisor (Int.fract α) := by
  ext p
  simp only [divisor, Set.mem_iUnion]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b - ⌊α⌋, by rwa [← divisorComponent_eq_fract]⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b + ⌊α⌋, by rw [divisorComponent_eq_fract, add_sub_cancel_right]; exact h⟩

theorem divisorNbhd_eq_fract (α : ℚ) (a b : ℤ) :
    divisorNbhd α a b = divisorNbhd (Int.fract α) a (b - ⌊α⌋) := by
  ext p
  simp only [divisorNbhd, Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and]
  refine and_congr_right fun _ => ⟨fun h c hc hp => ?_, fun h c hc hp => ?_⟩
  · obtain ⟨c1, c2⟩ := c
    refine h (c1, c2 + ⌊α⌋) ?_ ?_
    · intro hc'
      apply hc
      simp only [Prod.mk.injEq] at hc' ⊢
      omega
    · rw [divisorComponent_eq_fract, add_sub_cancel_right]
      exact hp
  · obtain ⟨c1, c2⟩ := c
    refine h (c1, c2 - ⌊α⌋) ?_ ?_
    · intro hc'
      apply hc
      simp only [Prod.mk.injEq] at hc' ⊢
      omega
    · rw [← divisorComponent_eq_fract]
      exact hp

/-- `(ℍ × ℂ) \ divisor α` is open, for every `α ∈ ℚ`. -/
theorem isOpen_halfPlaneProd_diff_divisor (α : ℚ) : IsOpen (halfPlaneProd \ divisor α) := by
  rw [divisor_eq_fract]
  exact divisor_compl_open _ (Int.fract_nonneg α) (Int.fract_lt_one α)

/-- `Ω_{a,b}` is open, for every `α ∈ ℚ`. -/
theorem isOpen_divisorNbhd (α : ℚ) (a b : ℤ) : IsOpen (divisorNbhd α a b) := by
  rw [divisorNbhd_eq_fract]
  exact divisorNbhd_isOpen _ (Int.fract_nonneg α) (Int.fract_lt_one α) _ _

/-- A point of `L_{a,b}` lies in `Ω_{a,b}`. -/
theorem mem_divisorNbhd_of_mem_divisorComponent {α : ℚ} {a b : ℤ} {p : ℂ × ℂ}
    (hp : p ∈ divisorComponent α a b) : p ∈ divisorNbhd α a b := by
  obtain ⟨τ, w⟩ := p
  obtain ⟨hτ, hw⟩ := hp
  simp only at hw
  subst hw
  exact kernelResidue_mem_divisorNbhd α hτ a b

/-! ### The summands -/

/-- The `n`-th summand `q^{mn²} u^{2mn} / (1 - e(-β) q^n u)` of `-A_{m,β}`. -/
noncomputable def appellLerchTerm (m : ℕ) (β : ℚ) (n : ℤ) (p : ℂ × ℂ) : ℂ :=
  e p.1 ^ ((m : ℤ) * n ^ 2) * e p.2 ^ (2 * (m : ℤ) * n) / (1 - e (-β) * e p.1 ^ n * e p.2)

theorem appellLerch_eq_neg_tsum (m : ℕ) (β : ℚ) (τ w : ℂ) :
    appellLerch m β τ w = -∑' n : ℤ, appellLerchTerm m β n (τ, w) := by
  rw [appellLerch_def]
  rfl

private lemma differentiable_e_zpow (n : ℤ) : Differentiable ℂ fun z : ℂ => e z ^ n := fun z =>
  (differentiable_e z).zpow (Or.inl (Complex.exp_ne_zero _))

/-- `e(-β) q^n u = e(w - β + nτ)`. -/
private lemma appellLerch_denom_e (β : ℚ) (n : ℤ) (τ w : ℂ) :
    e (-β) * e τ ^ n * e w = e (w - β + n * τ) := by
  rw [kernelResidue_e_zpow, kernelResidue_e_mul, kernelResidue_e_mul]
  congr 1
  ring

/-- A vanishing denominator puts the point on a component of `𝒟_β`. -/
theorem appellLerch_denom_eq_zero {β : ℚ} {n : ℤ} {p : ℂ × ℂ} (hp : p ∈ halfPlaneProd)
    (h : 1 - e (-β) * e p.1 ^ n * e p.2 = 0) :
    ∃ b : ℤ, p ∈ divisorComponent (-β) (-n) b := by
  rw [sub_eq_zero, eq_comm, appellLerch_denom_e, e, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨k, hp, ?_⟩
  have : p.2 - β + n * p.1 = k := mul_left_cancel₀ hπ (by rw [hk]; ring)
  push_cast
  linear_combination this

private lemma denom_ne_zero_of_mem_divisorNbhd {β : ℚ} {a b : ℤ} {p : ℂ × ℂ}
    (hp : p ∈ divisorNbhd (-β) a b) {n : ℤ} (hn : n ≠ -a) :
    1 - e (-β) * e p.1 ^ n * e p.2 ≠ 0 := by
  intro h
  obtain ⟨b', hb'⟩ := appellLerch_denom_eq_zero hp.1 h
  refine hp.2 (Set.mem_iUnion₂.mpr ⟨(-n, b'), ?_, hb'⟩)
  intro hc
  exact hn (by have := congrArg Prod.fst hc; simp at this; omega)

private lemma denom_ne_zero_of_not_mem_divisor {β : ℚ} {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd \ divisor (-β)) (n : ℤ) :
    1 - e (-β) * e p.1 ^ n * e p.2 ≠ 0 := fun h => by
  obtain ⟨b', hb'⟩ := appellLerch_denom_eq_zero hp.1 h
  exact hp.2 (Set.mem_iUnion₂.mpr ⟨-n, b', hb'⟩)

/-- A summable majorant for the summands on a compact `S ⊆ ℍ × ℂ`, for the indices `n ∈ I`
whose denominators do not vanish on `S`. -/
theorem appellLerchTerm_bound {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSH : S ⊆ halfPlaneProd) (I : Set ℤ)
    (hI : ∀ p ∈ S, ∀ n ∈ I, 1 - e (-β) * e p.1 ^ n * e p.2 ≠ 0) :
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ n ∈ I, ∀ p ∈ S, ‖appellLerchTerm m β n p‖ ≤ M n := by
  have hcast : (((-β : ℚ) : ℝ) : ℂ) = -(β : ℂ) := by push_cast; rfl
  have hswap : ∀ (p : ℂ × ℂ) (n : ℤ), e (-β) * e p.1 ^ n * e p.2 =
      e (((-β : ℚ) : ℝ) : ℂ) * e p.2 * e p.1 ^ n := fun p n => by rw [hcast]; ring
  obtain ⟨A, hA0, hA⟩ := denominator_bound_restricted ((-β : ℚ) : ℝ) S hS hSH I
    fun p hp n hn => by rw [← hswap]; exact hI p hp n hn
  obtain ⟨M, hMs, hM0, hM⟩ := thetaTermMajorant_exists (m := (m : ℤ)) (by omega) 0 S hS hSH
  refine ⟨fun n => A * M n, hMs.mul_left A, fun n hn p hp => ?_⟩
  have hAn := hA p hp n hn
  rw [← hswap] at hAn
  have hMn := hM n p hp
  simp only [zero_mul, add_zero, zero_add] at hMn
  change ‖appellLerchTerm m β n p‖ ≤ A * M n
  rw [appellLerchTerm, norm_div, div_eq_mul_inv, mul_comm A]
  exact mul_le_mul hMn hAn (by positivity) (hM0 _)

/-- **Normal convergence** [AOS, Proposition 4.3(1)]: on every compact subset of
`(ℍ × ℂ) \ 𝒟_β` the summands of `A_{m,β}` admit a summable majorant. -/
theorem appellLerch_normal {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSD : S ⊆ halfPlaneProd \ divisor (-β)) :
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ n, ∀ p ∈ S, ‖appellLerchTerm m β n p‖ ≤ M n := by
  obtain ⟨M, hM, hle⟩ := appellLerchTerm_bound hm β S hS (hSD.trans Set.sdiff_subset) Set.univ
    fun p hp n _ => denom_ne_zero_of_not_mem_divisor (hSD hp) n
  exact ⟨M, hM, fun n => hle n trivial⟩

private lemma differentiableOn_appellLerchTerm (m : ℕ) (β : ℚ) (n : ℤ) {U : Set (ℂ × ℂ)}
    (hU : ∀ p ∈ U, 1 - e (-β) * e p.1 ^ n * e p.2 ≠ 0) :
    DifferentiableOn ℂ (appellLerchTerm m β n) U := by
  intro p hp
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold appellLerchTerm
  simp only [div_eq_mul_inv]
  refine DifferentiableAt.mul ?_ (DifferentiableAt.inv ?_ (hU p hp))
  · exact (((differentiable_e_zpow _) _).comp _ differentiableAt_fst).mul
      (((differentiable_e_zpow _) _).comp _ differentiableAt_snd)
  · refine (differentiableAt_const _).sub (DifferentiableAt.mul ?_ ?_)
    · exact (differentiableAt_const _).mul
        (((differentiable_e_zpow _) _).comp _ differentiableAt_fst)
    · exact (differentiable_e _).comp _ differentiableAt_snd

/-- **Holomorphy** [AOS, Proposition 4.3(1)]: `A_{m,β}` is holomorphic on `(ℍ × ℂ) \ 𝒟_β`. -/
theorem appellLerch_differentiableOn {m : ℕ} (hm : 1 ≤ m) (β : ℚ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => appellLerch m β p.1 p.2)
      (halfPlaneProd \ divisor (-β)) := by
  simp only [appellLerch_eq_neg_tsum]
  refine DifferentiableOn.neg (differentiableOn_tsum_of_normal
    (f := fun n p => appellLerchTerm m β n p) (isOpen_halfPlaneProd_diff_divisor _)
    (fun n => differentiableOn_appellLerchTerm m β n fun p hp =>
      denom_ne_zero_of_not_mem_divisor hp n) fun K hK hKc => ?_)
  obtain ⟨M, hM, hle⟩ := appellLerch_normal hm β K hKc hK
  exact ⟨M, hM, hle⟩

/-! ### The elliptic law -/

/-- **The elliptic law of `A_{m,β}`** [AOS, Proposition 4.3(2)], for all translates:
`A(τ, w + aτ + b) = q^{-ma²} u^{-2ma} A(τ, w)`. -/
theorem appellLerch_add_mul_add (m : ℕ) (β : ℚ) (τ w : ℂ) (a b : ℤ) :
    appellLerch m β τ (w + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * appellLerch m β τ w := by
  have key : ∀ n : ℤ, appellLerchTerm m β n (τ, w + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * appellLerchTerm m β (n + a) (τ, w) := by
    intro n
    have hnum : e τ ^ ((m : ℤ) * n ^ 2) * e (w + a * τ + b) ^ (2 * (m : ℤ) * n) =
        e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
          (e τ ^ ((m : ℤ) * (n + a) ^ 2) * e w ^ (2 * (m : ℤ) * (n + a))) := by
      simp only [kernelResidue_e_zpow, kernelResidue_e_mul]
      simp only [e]
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨2 * m * n * b, by push_cast; ring⟩
    have hden : e (-β) * e τ ^ n * e (w + a * τ + b) = e (-β) * e τ ^ (n + a) * e w := by
      simp only [kernelResidue_e_zpow, kernelResidue_e_mul]
      simp only [e]
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨b, by push_cast; ring⟩
    simp only [appellLerchTerm]
    rw [hnum, hden, mul_div_assoc]
  rw [appellLerch_eq_neg_tsum, appellLerch_eq_neg_tsum]
  simp_rw [key]
  rw [tsum_mul_left, mul_neg]
  congr 2
  exact (Equiv.addRight a).tsum_eq fun n => appellLerchTerm m β n (τ, w)

/-- `A_{m,β}(τ, w + 1) = A_{m,β}(τ, w)` [AOS, (4.6)]. -/
theorem appellLerch_add_one (m : ℕ) (β : ℚ) (τ w : ℂ) :
    appellLerch m β τ (w + 1) = appellLerch m β τ w := by
  simpa using appellLerch_add_mul_add m β τ w 0 1

/-- `A_{m,β}(τ, w + τ) = q^{-m} u^{-2m} A_{m,β}(τ, w)` [AOS, (4.6)]. -/
theorem appellLerch_add_self (m : ℕ) (β : ℚ) (τ w : ℂ) :
    appellLerch m β τ (w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * appellLerch m β τ w := by
  simpa using appellLerch_add_mul_add m β τ w 1 0

/-! ### Simple poles and residues -/

/-- The regular part: the series of `A_{m,β}` without the summand `n = -a` (and without the
sign). -/
noncomputable def appellLerchRegular (m : ℕ) (β : ℚ) (a : ℤ) (p : ℂ × ℂ) : ℂ :=
  ∑' n : {n : ℤ // n ≠ -a}, appellLerchTerm m β n p

/-- The regular part is holomorphic on `Ω_{a,b}`. -/
theorem appellLerchRegular_differentiableOn {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (a b : ℤ) :
    DifferentiableOn ℂ (appellLerchRegular m β a) (divisorNbhd (-β) a b) := by
  unfold appellLerchRegular
  refine differentiableOn_tsum_of_normal (f := fun (n : {n : ℤ // n ≠ -a}) p =>
    appellLerchTerm m β n p) (isOpen_divisorNbhd _ a b)
    (fun n => differentiableOn_appellLerchTerm m β n fun p hp =>
      denom_ne_zero_of_mem_divisorNbhd hp n.2) fun K hK hKc => ?_
  obtain ⟨M, hM, hle⟩ := appellLerchTerm_bound hm β K hKc (fun p hp => (hK hp).1) {n | n ≠ -a}
    fun p hp n hn => denom_ne_zero_of_mem_divisorNbhd (hK hp) hn
  exact ⟨fun n => M n, hM.subtype _, fun n p hp => hle n n.2 p hp⟩

/-- The numerator `(w - β - aτ - b) A_{m,β}` near the component `w = β + aτ + b`. -/
noncomputable def appellLerchPolarNumerator (m : ℕ) (β : ℚ) (a b : ℤ) (p : ℂ × ℂ) : ℂ :=
  -((p.2 - β - a * p.1 - b) * appellLerchRegular m β a p +
    e p.1 ^ ((m : ℤ) * a ^ 2) * e p.2 ^ (-2 * (m : ℤ) * a) * expQuotient (p.2 - β - a * p.1 - b))

/-- On `Ω_{a,b}`, `w - β - aτ - b` is not a nonzero integer. -/
private lemma polar_mapsTo (β : ℚ) (a b : ℤ) :
    Set.MapsTo (fun p : ℂ × ℂ => p.2 - β - a * p.1 - b) (divisorNbhd (-β) a b)
      (Set.range ((↑) : ℤ → ℂ) \ {0})ᶜ := by
  rintro p hp ⟨⟨k, hk⟩, hk0⟩
  have hk0 : k ≠ 0 := by rintro rfl; exact hk0 (by rw [← hk]; simp)
  refine hp.2 (Set.mem_iUnion₂.mpr ⟨(a, b + k), ?_, hp.1, ?_⟩)
  · intro h
    exact hk0 (by have := congrArg Prod.snd h; simpa using this)
  · push_cast
    linear_combination -hk

theorem appellLerchPolarNumerator_differentiableOn {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (a b : ℤ) :
    DifferentiableOn ℂ (appellLerchPolarNumerator m β a b) (divisorNbhd (-β) a b) := by
  have hz : Differentiable ℂ fun p : ℂ × ℂ => p.2 - β - a * p.1 - b := by fun_prop
  refine DifferentiableOn.neg (DifferentiableOn.add
    (hz.differentiableOn.mul (appellLerchRegular_differentiableOn hm β a b))
    (DifferentiableOn.mul ?_ ?_))
  · exact ((((differentiable_e_zpow _).comp differentiable_fst).mul
      ((differentiable_e_zpow _).comp differentiable_snd))).differentiableOn
  · exact expQuotient_differentiableOn.2.comp hz.differentiableOn (polar_mapsTo β a b)

/-- Off `𝒟_β`, the series of `A_{m,β}` splits as the regular part plus the summand `n = -a`. -/
private lemma appellLerch_split {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (a : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd \ divisor (-β)) :
    appellLerch m β p.1 p.2 = -(appellLerchRegular m β a p + appellLerchTerm m β (-a) p) := by
  obtain ⟨M, hM, hle⟩ := appellLerch_normal hm β {p} isCompact_singleton
    (Set.singleton_subset_iff.mpr hp)
  have hs : Summable fun n => appellLerchTerm m β n p :=
    Summable.of_norm_bounded hM fun n => hle n p rfl
  rw [appellLerch_eq_neg_tsum, kernelSplit_tsum_eq hs (-a)]
  rfl

/-- `(w - β - aτ - b) A_{m,β}` is the polar numerator off `𝒟_β`. -/
theorem appellLerchPolarNumerator_eq {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (a b : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd \ divisor (-β)) :
    appellLerchPolarNumerator m β a b p = (p.2 - β - a * p.1 - b) * appellLerch m β p.1 p.2 := by
  set z := p.2 - β - a * p.1 - b with hz
  have hz0 : z ≠ 0 := by
    intro h
    refine hp.2 (Set.mem_iUnion₂.mpr ⟨a, b, hp.1, ?_⟩)
    push_cast
    linear_combination h
  have hden : 1 - e (-β) * e p.1 ^ (-a) * e p.2 = 1 - e z := by
    rw [appellLerch_denom_e, hz]
    simp only [e]
    congr 1
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨b, by push_cast; ring⟩
  have hΦ : expQuotient z = z / (1 - e z) := by
    rw [expQuotient, ite_eq_right hz0]
  rw [appellLerch_split hm β a hp, appellLerchPolarNumerator, ← hz, hΦ, appellLerchTerm, hden]
  have h1 : (-a) ^ 2 = a ^ 2 := by ring
  have h2 : 2 * (m : ℤ) * -a = -2 * m * a := by ring
  rw [h1, h2]
  ring

/-- The value of the polar numerator on the component `w = β + aτ + b`: the residue of
`A_{m,β}` there is `q^{-ma²} e(β)^{-2ma} / (2πi)`. -/
theorem appellLerchPolarNumerator_of_mem {m : ℕ} (β : ℚ) (a b : ℤ) {p : ℂ × ℂ}
    (hp : p ∈ divisorComponent (-β) a b) :
    appellLerchPolarNumerator m β a b p =
      e p.1 ^ ((m : ℤ) * a ^ 2) * e p.2 ^ (-2 * (m : ℤ) * a) / (2 * Real.pi * I) := by
  have hz : p.2 - β - a * p.1 - b = 0 := by
    rw [hp.2]; push_cast; ring
  rw [appellLerchPolarNumerator, hz]
  simp [expQuotient]
  ring

/-- **At most simple poles** [AOS, Proposition 4.3(3)]: for `a, b ∈ ℤ`,
`(w - β - aτ - b) A_{m,β}(τ, w)` extends holomorphically to the neighbourhood `Ω_{a,b}` of the
component `w = β + aτ + b` of `𝒟_β`. -/
theorem appellLerch_simple_pole {m : ℕ} (hm : 1 ≤ m) (β : ℚ) (a b : ℤ) :
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd (-β) a b) ∧
      ∀ p ∈ halfPlaneProd \ divisor (-β),
        N p = (p.2 - β - a * p.1 - b) * appellLerch m β p.1 p.2 :=
  ⟨_, appellLerchPolarNumerator_differentiableOn hm β a b,
    fun _ hp => appellLerchPolarNumerator_eq hm β a b hp⟩

/-- **The residue at `w = β`** [AOS, (4.7)]: `2πi ε A_{m,β}(τ, β + ε) → 1` as `ε → 0`,
`ε ≠ 0`, i.e. `A_{m,β}(τ, β + ε) = 1/(2πiε) + O(1)`. -/
theorem appellLerch_residue {m : ℕ} (hm : 1 ≤ m) (β : ℚ) {τ : ℂ} (hτ : 0 < τ.im) :
    Tendsto (fun ε : ℂ => 2 * Real.pi * I * ε * appellLerch m β τ (β + ε)) (𝓝[≠] 0) (𝓝 1) := by
  have hmem : (τ, (β : ℂ)) ∈ divisorComponent (-β) 0 0 := ⟨hτ, by push_cast; ring⟩
  have hV : divisorNbhd (-β) 0 0 ∈ 𝓝 (τ, (β : ℂ)) :=
    (isOpen_divisorNbhd _ 0 0).mem_nhds (mem_divisorNbhd_of_mem_divisorComponent hmem)
  have hlim := tendsto_mul_of_eq_sub_mul (H := fun p => appellLerch m β p.1 p.2)
    (N := appellLerchPolarNumerator m β 0 0) (D := divisor (-β)) hV
    (fun q hq hq2 hqD => ?_)
    ((appellLerchPolarNumerator_differentiableOn hm β 0 0).differentiableAt hV).continuousAt
    (fun q hq hqD => by
      rw [appellLerchPolarNumerator_eq hm β 0 0 ⟨hq.1, hqD⟩]
      push_cast
      ring_nf)
  · rw [appellLerchPolarNumerator_of_mem β 0 0 hmem] at hlim
    have h2 := hlim.const_mul (2 * Real.pi * I)
    have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp only [sq, mul_zero, zpow_zero, one_mul] at h2
    rw [mul_one_div_cancel hπ] at h2
    simpa only [mul_assoc] using h2
  · obtain ⟨c, hc, hqc⟩ := Set.mem_iUnion₂.mp hqD
    by_cases h : (c, hc) = ((0 : ℤ), (0 : ℤ))
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hq2 (by rw [hqc.2]; push_cast; ring)
    · exact hq.2 (Set.mem_iUnion₂.mpr ⟨(c, hc), h, hqc⟩)

end HigherDyson3
