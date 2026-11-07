/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Kernel.AppellLerchProperties
public import HigherDyson3.Theta.ThetaDecomposition

/-!
# Local polar subtraction for simple poles

Let `m ≥ 1`, let `S` be a finite set of rationals, pairwise distinct modulo `1`, and for
`β ∈ S` let `𝒟_β = {(τ, w) ∈ ℍ × ℂ : w ∈ β + ℤτ + ℤ}`. Let `H` be holomorphic on
`(ℍ × ℂ) \ ⋃_β 𝒟_β`, with at most simple poles along each `𝒟_β` (for all `a, b ∈ ℤ`,
`(w - β - aτ - b) H` extends holomorphically to a neighbourhood of every point of `𝒟_β` with
`w = β + aτ + b`), and with the index-`m` elliptic law. Write
`κ_β(τ) = lim_{ε → 0} 2πi ε H(τ, β + ε)`. Then each `κ_β` is holomorphic on `ℍ`, and
`H - ∑_β κ_β A_{m,β}` extends to a holomorphic function on `ℍ × ℂ` with the same elliptic law;
hence it is `∑_ℓ h_ℓ ϑ_{m,ℓ}` with unique holomorphic `h_ℓ` [AOS, Proposition 4.4].

Near `(τ₀, β)`, `(w - β) H = N` with `N` holomorphic, so `κ_β = 2πi N(·, β)` is holomorphic, and
`(w - β)(H - ∑ κ_{β'} A_{m,β'})` is holomorphic and vanishes on `w = β`; division by `w - β`
(`HigherDyson3.exists_differentiableOn_eq_sub_mul`) removes the singularity. Near a translate
`w = β + aτ + b`, the elliptic law transports this extension. The local extensions are glued
along the dense complement of the poles, and the theta decomposition finishes the proof.

## Main results

* `HigherDyson3.residueCoeff`: the residue coefficient `κ_β`.
* `HigherDyson3.localPolarPart`: `H^{P,loc} = ∑_{β ∈ S} κ_β A_{m,β}`.
* `HigherDyson3.local_polar_subtraction`: [AOS, Proposition 4.4].
-/

public section

open Complex Filter Topology Set

namespace HigherDyson3

/-- The polar divisor `⋃_{β ∈ S} 𝒟_β`, `𝒟_β = {w ∈ β + ℤτ + ℤ} = divisor (-β)`. -/
def polarDivisor (S : Finset ℚ) : Set (ℂ × ℂ) := ⋃ β ∈ S, divisor (-β)

/-- The residue coefficient `κ_β(τ) = lim_{ε → 0, ε ≠ 0} 2πi ε H(τ, β + ε)`. -/
noncomputable def residueCoeff (H : ℂ × ℂ → ℂ) (β : ℚ) (τ : ℂ) : ℂ :=
  limUnder (𝓝[≠] (0 : ℂ)) fun ε => 2 * Real.pi * I * ε * H (τ, β + ε)

/-- The local polar part `H^{P,loc}(τ, w) = ∑_{β ∈ S} κ_β(τ) A_{m,β}(τ, w)`. -/
noncomputable def localPolarPart (m : ℕ) (S : Finset ℚ) (H : ℂ × ℂ → ℂ) (τ w : ℂ) : ℂ :=
  ∑ β ∈ S, residueCoeff H β τ * appellLerch m β τ w

/-! ### The polar divisor -/

theorem mem_divisor_neg_iff {β : ℚ} {p : ℂ × ℂ} :
    p ∈ divisor (-β) ↔ 0 < p.1.im ∧ ∃ a b : ℤ, p.2 = β + a * p.1 + b := by
  simp only [divisor, divisorComponent, mem_iUnion, mem_ofPred_eq]
  push_cast
  simp only [neg_neg]
  constructor
  · rintro ⟨a, b, h1, h2⟩; exact ⟨h1, a, b, h2⟩
  · rintro ⟨h1, a, b, h2⟩; exact ⟨a, b, h1, h2⟩

/-- The polar divisor is invariant under `w ↦ w + aτ + b`. -/
theorem mem_polarDivisor_shift {S : Finset ℚ} {p : ℂ × ℂ} (a b : ℤ) :
    (p.1, p.2 + a * p.1 + b) ∈ polarDivisor S ↔ p ∈ polarDivisor S := by
  simp only [polarDivisor, mem_iUnion, exists_prop, mem_divisor_neg_iff]
  constructor
  · rintro ⟨β, hβ, h1, c, d, h⟩
    exact ⟨β, hβ, h1, c - a, d - b, by push_cast; linear_combination h⟩
  · rintro ⟨β, hβ, h1, c, d, h⟩
    exact ⟨β, hβ, h1, c + a, d + b, by push_cast; linear_combination h⟩

theorem shift_mem_compl_polarDivisor {S : Finset ℚ} {p : ℂ × ℂ}
    (hp : p ∈ halfPlaneProd \ polarDivisor S) (a b : ℤ) :
    (p.1, p.2 + a * p.1 + b) ∈ halfPlaneProd \ polarDivisor S :=
  ⟨hp.1, fun h => hp.2 ((mem_polarDivisor_shift a b).mp h)⟩

theorem isOpen_compl_polarDivisor (S : Finset ℚ) :
    IsOpen (halfPlaneProd \ polarDivisor S) := by
  have : halfPlaneProd \ polarDivisor S =
      halfPlaneProd ∩ ⋂ β ∈ S, (halfPlaneProd \ divisor (-β)) := by
    ext p
    simp only [polarDivisor, Set.mem_sdiff, mem_iUnion, exists_prop, not_exists, not_and,
      mem_inter_iff, mem_iInter]
    exact ⟨fun h => ⟨h.1, fun β hβ => ⟨h.1, h.2 β hβ⟩⟩, fun h => ⟨h.1, fun β hβ => (h.2 β hβ).2⟩⟩
  rw [this]
  exact isOpen_halfPlaneProd.inter
    (isOpen_biInter_finset fun β _ => isOpen_halfPlaneProd_diff_divisor _)

/-- The complement of the polar divisor is dense in `ℍ × ℂ`. -/
theorem halfPlaneProd_subset_closure_compl_polarDivisor (S : Finset ℚ) :
    halfPlaneProd ⊆ closure (halfPlaneProd \ polarDivisor S) := by
  intro p hp
  set T : Set ℂ := {w | (p.1, w) ∈ polarDivisor S} with hT
  have hTc : T.Countable := by
    refine (Set.countable_range fun x : ℚ × ℤ × ℤ => (x.1 : ℂ) + x.2.1 * p.1 + x.2.2).mono ?_
    intro w hw
    simp only [hT, polarDivisor, mem_ofPred_eq, mem_iUnion, exists_prop, mem_divisor_neg_iff]
      at hw
    obtain ⟨β, -, -, a, b, h⟩ := hw
    exact ⟨(β, a, b), h.symm⟩
  have hd : p.2 ∈ closure Tᶜ := (hTc.dense_compl ℂ).closure_eq ▸ mem_univ _
  have := map_mem_closure (f := fun w : ℂ => (p.1, w)) (by fun_prop) hd
    (t := halfPlaneProd \ polarDivisor S) fun w hw => ⟨hp, hw⟩
  simpa using this

/-! ### The elliptic law on a translation-invariant set -/

private lemma e_zpow_mul_eq {τ w : ℂ} {k₁ k₂ k₃ k₄ k₅ k₆ : ℤ} {c₁ c₂ : ℂ}
    (h : (k₁ : ℂ) * τ + k₂ * (w + c₁) + k₃ * τ + k₄ * w = k₅ * τ + k₆ * w) :
    e τ ^ k₁ * e (w + c₁) ^ k₂ * (e τ ^ k₃ * e w ^ k₄ * c₂) = e τ ^ k₅ * e w ^ k₆ * c₂ := by
  simp only [kernelResidue_e_zpow]
  rw [← mul_assoc, kernelResidue_e_mul, kernelResidue_e_mul, kernelResidue_e_mul,
    kernelResidue_e_mul]
  congr 2
  linear_combination h

/-- **Iterating the elliptic law.** If `F(τ, w + 1) = F(τ, w)` and
`F(τ, w + τ) = q^{-m} u^{-2m} F(τ, w)` on a set `Ω` invariant under all `w ↦ w + aτ + b`, then
`F(τ, w + aτ + b) = q^{-ma²} u^{-2ma} F(τ, w)` on `Ω`. -/
theorem elliptic_law_iterate {m : ℕ} {F : ℂ × ℂ → ℂ} {Ω : Set (ℂ × ℂ)}
    (hΩ : ∀ p ∈ Ω, ∀ a b : ℤ, (p.1, p.2 + a * p.1 + b) ∈ Ω)
    (h1 : ∀ p ∈ Ω, F (p.1, p.2 + 1) = F p)
    (hτ : ∀ p ∈ Ω, F (p.1, p.2 + p.1) = e p.1 ^ (-(m : ℤ)) * e p.2 ^ (-2 * (m : ℤ)) * F p)
    {p : ℂ × ℂ} (hp : p ∈ Ω) (a b : ℤ) :
    F (p.1, p.2 + a * p.1 + b) =
      e p.1 ^ (-(m : ℤ) * a ^ 2) * e p.2 ^ (-2 * (m : ℤ) * a) * F p := by
  obtain ⟨τ, w⟩ := p
  simp only at *
  have hΩ' : ∀ w', (τ, w') ∈ Ω → ∀ a b : ℤ, (τ, w' + a * τ + b) ∈ Ω := fun w' h a b =>
    hΩ _ h a b
  -- integer translations
  have hb : ∀ w', (τ, w') ∈ Ω → ∀ b : ℤ, F (τ, w' + b) = F (τ, w') := by
    intro w' hw' b
    induction b using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have := h1 _ (by simpa using hΩ' w' hw' 0 k)
      simp only at this
      push_cast at ih ⊢
      rw [← add_assoc, this, ih]
    | pred k ih =>
      have := h1 _ (by simpa using hΩ' w' hw' 0 (-k - 1))
      simp only at this
      push_cast at ih this ⊢
      rw [← ih, ← this]
      ring_nf
  -- translations by multiples of `τ`
  have ha : ∀ a : ℤ, F (τ, w + a * τ) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * F (τ, w) := by
    intro a
    induction a using Int.induction_on with
    | zero => simp
    | succ k ih =>
      have := hτ _ (by simpa using hΩ' w hp k 0)
      simp only at this
      push_cast at ih ⊢
      rw [show w + (k + 1) * τ = w + k * τ + τ by ring, this, ih]
      refine e_zpow_mul_eq ?_
      push_cast
      ring
    | pred k ih =>
      have hmem : (τ, w + ((-k - 1 : ℤ) : ℂ) * τ) ∈ Ω := by simpa using hΩ' w hp (-k - 1) 0
      have := hτ _ hmem
      simp only at this
      rw [show w + ((-k - 1 : ℤ) : ℂ) * τ + τ = w + ((-k : ℤ) : ℂ) * τ by push_cast; ring, ih]
        at this
      have hc : e τ ^ (-(m : ℤ)) * e (w + ((-k - 1 : ℤ) : ℂ) * τ) ^ (-2 * (m : ℤ)) ≠ 0 :=
        mul_ne_zero (zpow_ne_zero _ (Complex.exp_ne_zero _))
          (zpow_ne_zero _ (Complex.exp_ne_zero _))
      apply mul_left_cancel₀ hc
      rw [← this]
      symm
      refine e_zpow_mul_eq ?_
      push_cast
      ring
  have hmem : (τ, w + a * τ) ∈ Ω := by simpa using hΩ' w hp a 0
  rw [hb _ hmem b, ha a]

/-! ### The local analysis near `w = β` -/

/-- Near `(τ₀, β)`, `β ∈ S`, the polar divisor is the line `w = β`. -/
private lemma exists_nhds_line {S : Finset ℚ}
    (hS : ∀ β ∈ S, ∀ β' ∈ S, ∀ k : ℤ, β - β' = k → β = β') {β : ℚ} (hβ : β ∈ S) {τ₀ : ℂ}
    (hτ₀ : 0 < τ₀.im) :
    ∃ V : Set (ℂ × ℂ), IsOpen V ∧ (τ₀, (β : ℂ)) ∈ V ∧ V ⊆ divisorNbhd (-β) 0 0 ∧
      (∀ β' ∈ S.erase β, V ⊆ halfPlaneProd \ divisor (-β')) ∧
      ∀ q ∈ V, q.2 ≠ β → q ∈ halfPlaneProd \ polarDivisor S := by
  refine ⟨divisorNbhd (-β) 0 0 ∩ ⋂ β' ∈ S.erase β, (halfPlaneProd \ divisor (-β')),
    (isOpen_divisorNbhd _ 0 0).inter
      (isOpen_biInter_finset fun β' _ => isOpen_halfPlaneProd_diff_divisor _), ⟨?_, ?_⟩,
    inter_subset_left, fun β' hβ' => inter_subset_right.trans (biInter_subset_of_mem hβ'),
    fun q hq hqβ => ⟨hq.1.1, fun hD => ?_⟩⟩
  · exact mem_divisorNbhd_of_mem_divisorComponent ⟨hτ₀, by push_cast; ring⟩
  · refine mem_iInter₂.mpr fun β' hβ' => ⟨hτ₀, fun hD => ?_⟩
    obtain ⟨-, a, b, h⟩ := mem_divisor_neg_iff.mp hD
    simp only at h
    have him := congrArg Complex.im h
    simp only [add_im, ratCast_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero,
      zero_add] at him
    have ha : a = 0 := by
      have : (a : ℝ) * τ₀.im = 0 := by linarith
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hτ₀.ne'
    subst ha
    have : ((β - β' : ℚ) : ℂ) = ((b : ℤ) : ℂ) := by push_cast; linear_combination h
    have hk : β - β' = b := by exact_mod_cast this
    exact (Finset.ne_of_mem_erase hβ') (hS β' (Finset.mem_of_mem_erase hβ') β hβ (-b)
      (by push_cast; linarith))
  · simp only [polarDivisor, mem_iUnion, exists_prop] at hD
    obtain ⟨β', hβ'S, hβ'⟩ := hD
    by_cases hβ'β : β' = β
    · subst hβ'β
      obtain ⟨c, hc⟩ := mem_iUnion.mp hβ'
      obtain ⟨d, hd⟩ := mem_iUnion.mp hc
      by_cases hcd : (c, d) = ((0 : ℤ), (0 : ℤ))
      · simp only [Prod.mk.injEq] at hcd
        obtain ⟨rfl, rfl⟩ := hcd
        exact hqβ (by rw [hd.2]; push_cast; ring)
      · exact hq.1.2 (mem_iUnion₂.mpr ⟨(c, d), hcd, hd⟩)
    · exact (mem_iInter₂.mp hq.2 β' (Finset.mem_erase.mpr ⟨hβ'β, hβ'S⟩)).2 hβ'

/-- The residue coefficient through a local numerator `N = (w - β) H`. -/
private lemma residueCoeff_eq_of_numerator {S : Finset ℚ} {H N : ℂ × ℂ → ℂ} {β : ℚ} {τ : ℂ}
    {W : Set (ℂ × ℂ)} (hW : W ∈ 𝓝 (τ, (β : ℂ)))
    (hWD : ∀ q ∈ W, q.2 ≠ β → q ∉ polarDivisor S) (hN : ContinuousAt N (τ, β))
    (hNH : ∀ q ∈ W, q ∉ polarDivisor S → N q = (q.2 - β) * H q) :
    Tendsto (fun ε : ℂ => 2 * Real.pi * I * ε * H (τ, β + ε)) (𝓝[≠] 0)
        (𝓝 (residueCoeff H β τ)) ∧
      residueCoeff H β τ = 2 * Real.pi * I * N (τ, β) := by
  have h := (tendsto_mul_of_eq_sub_mul hW hWD hN hNH).const_mul (2 * Real.pi * I)
  simp only [← mul_assoc] at h
  have heq : residueCoeff H β τ = 2 * Real.pi * I * N (τ, β) := h.limUnder_eq
  exact ⟨heq ▸ h, heq⟩

/-- The local data at `(τ₀, β)`: a neighbourhood on which the polar divisor is `w = β`, the
numerator `N = (w - β) H`, and `κ_β = 2πi N(·, β)`. -/
private lemma exists_local_numerator {S : Finset ℚ}
    (hS : ∀ β ∈ S, ∀ β' ∈ S, ∀ k : ℤ, β - β' = k → β = β') {H : ℂ × ℂ → ℂ}
    (hpole : ∀ β ∈ S, ∀ a b : ℤ, ∀ p ∈ divisorComponent (-β) a b, ∃ U ∈ 𝓝 p,
      ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N U ∧
        ∀ q ∈ U \ polarDivisor S, N q = (q.2 - β - a * q.1 - b) * H q)
    {β : ℚ} (hβ : β ∈ S) {τ₀ : ℂ} (hτ₀ : 0 < τ₀.im) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (τ₀, (β : ℂ)) ∈ W ∧ W ⊆ divisorNbhd (-β) 0 0 ∧
      (∀ β' ∈ S.erase β, W ⊆ halfPlaneProd \ divisor (-β')) ∧
      (∀ q ∈ W, q.2 ≠ β → q ∈ halfPlaneProd \ polarDivisor S) ∧
      ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N W ∧
        (∀ q ∈ W, q ∉ polarDivisor S → N q = (q.2 - β) * H q) ∧
        ∀ τ, (τ, (β : ℂ)) ∈ W →
          Tendsto (fun ε : ℂ => 2 * Real.pi * I * ε * H (τ, β + ε)) (𝓝[≠] 0)
            (𝓝 (residueCoeff H β τ)) ∧ residueCoeff H β τ = 2 * Real.pi * I * N (τ, β) := by
  obtain ⟨V, hVo, hV₀, hVΩ, hVβ', hVline⟩ := exists_nhds_line hS hβ hτ₀
  obtain ⟨U, hU, N, hN, hNH⟩ := hpole β hβ 0 0 (τ₀, β) ⟨hτ₀, by push_cast; ring⟩
  refine ⟨interior U ∩ V, isOpen_interior.inter hVo, ⟨mem_interior_iff_mem_nhds.mpr hU, hV₀⟩,
    inter_subset_right.trans hVΩ, fun β' hβ' => inter_subset_right.trans (hVβ' β' hβ'),
    fun q hq => hVline q hq.2, N, hN.mono (inter_subset_left.trans interior_subset),
    fun q hq hqD => ?_, fun τ hτ => ?_⟩
  · rw [hNH q ⟨interior_subset hq.1, hqD⟩]
    push_cast
    ring
  · have hW : interior U ∩ V ∈ 𝓝 (τ, (β : ℂ)) := (isOpen_interior.inter hVo).mem_nhds hτ
    refine residueCoeff_eq_of_numerator hW (fun q hq hqβ => (hVline q hq.2 hqβ).2)
      ((hN.differentiableAt (mem_interior_iff_mem_nhds.mp hτ.1)).continuousAt)
      fun q hq hqD => ?_
    rw [hNH q ⟨interior_subset hq.1, hqD⟩]
    push_cast
    ring

/-- `τ ↦ κ_β(τ)` is holomorphic on `ℍ`, and `2πi ε H(τ, β + ε) → κ_β(τ)`. -/
private lemma residueCoeff_properties {S : Finset ℚ}
    (hS : ∀ β ∈ S, ∀ β' ∈ S, ∀ k : ℤ, β - β' = k → β = β') {H : ℂ × ℂ → ℂ}
    (hpole : ∀ β ∈ S, ∀ a b : ℤ, ∀ p ∈ divisorComponent (-β) a b, ∃ U ∈ 𝓝 p,
      ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N U ∧
        ∀ q ∈ U \ polarDivisor S, N q = (q.2 - β - a * q.1 - b) * H q)
    {β : ℚ} (hβ : β ∈ S) :
    (∀ τ : ℂ, 0 < τ.im → Tendsto (fun ε : ℂ => 2 * Real.pi * I * ε * H (τ, β + ε)) (𝓝[≠] 0)
      (𝓝 (residueCoeff H β τ))) ∧
      DifferentiableOn ℂ (residueCoeff H β) upperHalfPlaneSet := by
  refine ⟨fun τ hτ => ?_, fun τ₀ hτ₀ => ?_⟩
  · obtain ⟨W, -, hW₀, -, -, -, N, -, -, hres⟩ := exists_local_numerator hS hpole hβ hτ
    exact (hres τ hW₀).1
  · obtain ⟨W, hWo, hW₀, -, -, -, N, hN, -, hres⟩ := exists_local_numerator hS hpole hβ hτ₀
    have hline : Continuous fun τ : ℂ => ((τ, (β : ℂ)) : ℂ × ℂ) := by fun_prop
    have hev : ∀ᶠ τ in 𝓝 τ₀, (τ, (β : ℂ)) ∈ W :=
      hline.continuousAt.preimage_mem_nhds (hWo.mem_nhds hW₀)
    have hd : DifferentiableAt ℂ (fun τ => 2 * Real.pi * I * N (τ, β)) τ₀ :=
      (differentiableAt_const _).mul ((hN.differentiableAt (hWo.mem_nhds hW₀)).comp τ₀
        (by fun_prop))
    exact (hd.congr_of_eventuallyEq (hev.mono fun τ hτ => (hres τ hτ).2)).differentiableWithinAt

/-- The local extension of `H - H^{P,loc}` across the line `w = β` near `(τ₀, β)`. -/
private lemma exists_local_extension_line {m : ℕ} (hm : 1 ≤ m) {S : Finset ℚ}
    (hS : ∀ β ∈ S, ∀ β' ∈ S, ∀ k : ℤ, β - β' = k → β = β') {H : ℂ × ℂ → ℂ}
    (hpole : ∀ β ∈ S, ∀ a b : ℤ, ∀ p ∈ divisorComponent (-β) a b, ∃ U ∈ 𝓝 p,
      ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N U ∧
        ∀ q ∈ U \ polarDivisor S, N q = (q.2 - β - a * q.1 - b) * H q)
    {β : ℚ} (hβ : β ∈ S) {τ₀ : ℂ} (hτ₀ : 0 < τ₀.im) :
    ∃ V ∈ 𝓝 (τ₀, (β : ℂ)), ∃ E : ℂ × ℂ → ℂ, DifferentiableOn ℂ E V ∧
      ∀ q ∈ V ∩ (halfPlaneProd \ polarDivisor S), E q = H q - localPolarPart m S H q.1 q.2 := by
  classical
  obtain ⟨W, hWo, hW₀, hWΩ, hWβ', hWline, N, hN, hNH, hres⟩ :=
    exists_local_numerator hS hpole hβ hτ₀
  have hWH : W ⊆ halfPlaneProd := fun q hq => (hWΩ hq).1
  have hκ : ∀ β' ∈ S, DifferentiableOn ℂ (fun q : ℂ × ℂ => residueCoeff H β' q.1) W :=
    fun β' hβ' => (residueCoeff_properties hS hpole hβ').2.comp (by fun_prop)
      fun q hq => hWH hq
  set NA := appellLerchPolarNumerator m β 0 0 with hNA
  set Rest : ℂ × ℂ → ℂ := fun q =>
    ∑ β' ∈ S.erase β, residueCoeff H β' q.1 * appellLerch m β' q.1 q.2 with hRest
  have hRestd : DifferentiableOn ℂ Rest W := by
    refine DifferentiableOn.fun_sum fun β' hβ' => (hκ β' (Finset.mem_of_mem_erase hβ')).mul ?_
    exact (appellLerch_differentiableOn hm β').mono (hWβ' β' hβ')
  set Nt : ℂ × ℂ → ℂ := fun q =>
    N q - residueCoeff H β q.1 * NA q - (q.2 - β) * Rest q with hNt
  have hNtd : DifferentiableOn ℂ Nt W := by
    refine (hN.sub ((hκ β hβ).mul ?_)).sub ((by fun_prop : Differentiable ℂ
      fun q : ℂ × ℂ => q.2 - (β : ℂ)).differentiableOn.mul hRestd)
    exact (appellLerchPolarNumerator_differentiableOn hm β 0 0).mono hWΩ
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hNt0 : ∀ q ∈ W, q.2 = β → Nt q = 0 := by
    intro q hq hqβ
    obtain ⟨τ, w⟩ := q
    simp only at hqβ
    subst hqβ
    have hNv : N (τ, β) = residueCoeff H β τ / (2 * Real.pi * I) := by
      rw [(hres τ hq).2]; field_simp
    have hNAv : NA (τ, β) = 1 / (2 * Real.pi * I) := by
      rw [hNA, appellLerchPolarNumerator_of_mem β 0 0 ⟨(hWH hq : 0 < τ.im), by push_cast; ring⟩]
      simp
    simp only [hNt, hNv, hNAv, sub_self, zero_mul, sub_zero]
    ring
  have hNtG : ∀ q ∈ W, q.2 ≠ β →
      Nt q = (q.2 - β) * (H q - localPolarPart m S H q.1 q.2) := by
    intro q hq hqβ
    have hqΩ := hWline q hq hqβ
    have hqA : q ∈ halfPlaneProd \ divisor (-β) := ⟨hqΩ.1, fun h => hqΩ.2
      (mem_iUnion₂.mpr ⟨β, hβ, h⟩)⟩
    simp only [hNt, hNH q hq hqΩ.2, hNA, appellLerchPolarNumerator_eq hm β 0 0 hqA, localPolarPart,
      ← Finset.add_sum_erase S _ hβ, hRest]
    push_cast
    ring
  obtain ⟨N₁, hN₁, hNtN₁⟩ := exists_differentiableOn_eq_sub_mul hWo hNtd hNt0
  refine ⟨W, hWo.mem_nhds hW₀, N₁, hN₁, fun q ⟨hqW, hqΩ⟩ => ?_⟩
  have hqβ : q.2 ≠ β := by
    intro h
    refine hqΩ.2 (mem_iUnion₂.mpr ⟨β, hβ, mem_iUnion₂.mpr ⟨0, 0, hqΩ.1, ?_⟩⟩)
    rw [h]; push_cast; ring
  have := (hNtN₁ q hqW).symm.trans (hNtG q hqW hqβ)
  exact mul_left_cancel₀ (sub_ne_zero.mpr hqβ) this

/-- The elliptic law of `H - H^{P,loc}` off the poles. -/
private lemma polarDifference_law {m : ℕ} {S : Finset ℚ} {H : ℂ × ℂ → ℂ}
    (h1 : ∀ p ∈ halfPlaneProd \ polarDivisor S, H (p.1, p.2 + 1) = H p)
    (hτ : ∀ p ∈ halfPlaneProd \ polarDivisor S,
      H (p.1, p.2 + p.1) = e p.1 ^ (-(m : ℤ)) * e p.2 ^ (-2 * (m : ℤ)) * H p) :
    (∀ p ∈ halfPlaneProd \ polarDivisor S,
      H (p.1, p.2 + 1) - localPolarPart m S H p.1 (p.2 + 1) =
        H p - localPolarPart m S H p.1 p.2) ∧
    ∀ p ∈ halfPlaneProd \ polarDivisor S,
      H (p.1, p.2 + p.1) - localPolarPart m S H p.1 (p.2 + p.1) =
        e p.1 ^ (-(m : ℤ)) * e p.2 ^ (-2 * (m : ℤ)) * (H p - localPolarPart m S H p.1 p.2) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [h1 p hp, localPolarPart, appellLerch_add_one]
  · simp only [hτ p hp, localPolarPart, appellLerch_add_self, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    ring

/-- **Local polar subtraction** [AOS, Proposition 4.4]. Let `m ≥ 1` and let `S` be a finite set
of rationals, pairwise distinct modulo `1`. Let `H` be holomorphic on `(ℍ × ℂ) \ ⋃_{β ∈ S} 𝒟_β`,
`𝒟_β = {w ∈ β + ℤτ + ℤ}`, with at most simple poles: for `β ∈ S` and `a, b ∈ ℤ`,
`(w - β - aτ - b) H(τ, w)` extends holomorphically to a neighbourhood of every point of `𝒟_β`
with `w = β + aτ + b`; and suppose `H(τ, w + 1) = H(τ, w)`, `H(τ, w + τ) = q^{-m} u^{-2m} H(τ, w)`.
Then, with `κ_β(τ) = lim_{ε → 0} 2πi ε H(τ, β + ε)`:
* the limit exists and each `κ_β` is holomorphic on `ℍ`;
* `H - ∑_{β ∈ S} κ_β A_{m,β}` agrees off the poles with a function `G` holomorphic on `ℍ × ℂ`
  which satisfies the same elliptic law;
* `G = ∑_{ℓ=0}^{2m-1} h_ℓ ϑ_{m,ℓ}` with `h_ℓ = thetaDecompositionCoeff m G ℓ` holomorphic on `ℍ`,
  and these coefficients are unique. -/
theorem local_polar_subtraction {m : ℕ} (hm : 1 ≤ m) (S : Finset ℚ)
    (hS : ∀ β ∈ S, ∀ β' ∈ S, ∀ k : ℤ, β - β' = k → β = β') {H : ℂ × ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (halfPlaneProd \ polarDivisor S))
    (hpole : ∀ β ∈ S, ∀ a b : ℤ, ∀ p ∈ divisorComponent (-β) a b, ∃ U ∈ 𝓝 p,
      ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N U ∧
        ∀ q ∈ U \ polarDivisor S, N q = (q.2 - β - a * q.1 - b) * H q)
    (h1 : ∀ p ∈ halfPlaneProd \ polarDivisor S, H (p.1, p.2 + 1) = H p)
    (hτ : ∀ p ∈ halfPlaneProd \ polarDivisor S,
      H (p.1, p.2 + p.1) = e p.1 ^ (-(m : ℤ)) * e p.2 ^ (-2 * (m : ℤ)) * H p) :
    (∀ β ∈ S, ∀ τ : ℂ, 0 < τ.im →
      Tendsto (fun ε : ℂ => 2 * Real.pi * I * ε * H (τ, β + ε)) (𝓝[≠] 0)
        (𝓝 (residueCoeff H β τ))) ∧
    (∀ β ∈ S, DifferentiableOn ℂ (residueCoeff H β) upperHalfPlaneSet) ∧
    ∃ G : ℂ × ℂ → ℂ, DifferentiableOn ℂ G halfPlaneProd ∧
      (∀ p ∈ halfPlaneProd \ polarDivisor S, G p = H p - localPolarPart m S H p.1 p.2) ∧
      (∀ τ w : ℂ, 0 < τ.im → G (τ, w + 1) = G (τ, w)) ∧
      (∀ τ w : ℂ, 0 < τ.im →
        G (τ, w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * G (τ, w)) ∧
      (∀ ℓ, DifferentiableOn ℂ (thetaDecompositionCoeff m G ℓ) upperHalfPlaneSet) ∧
      (∀ τ w : ℂ, 0 < τ.im →
        G (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), thetaDecompositionCoeff m G ℓ τ * theta m ℓ τ w) ∧
      ∀ h : ℕ → ℂ → ℂ, (∀ τ w : ℂ, 0 < τ.im →
        G (τ, w) = ∑ ℓ ∈ Finset.range (2 * m), h ℓ τ * theta m ℓ τ w) →
        ∀ ℓ < 2 * m, ∀ τ : ℂ, 0 < τ.im → h ℓ τ = thetaDecompositionCoeff m G ℓ τ := by
  classical
  set Ω := halfPlaneProd \ polarDivisor S with hΩ
  set G₀ : ℂ × ℂ → ℂ := fun q => H q - localPolarPart m S H q.1 q.2 with hG₀
  have hκ := fun β (hβ : β ∈ S) => residueCoeff_properties hS hpole hβ
  -- `G₀` is holomorphic off the poles and satisfies the elliptic law there
  have hG₀d : DifferentiableOn ℂ G₀ Ω := by
    refine hH.sub (DifferentiableOn.fun_sum fun β hβ => DifferentiableOn.mul ?_ ?_)
    · exact (hκ β hβ).2.comp (by fun_prop) fun q hq => hq.1
    · exact (appellLerch_differentiableOn hm β).mono fun q hq =>
        ⟨hq.1, fun h => hq.2 (mem_iUnion₂.mpr ⟨β, hβ, h⟩)⟩
  obtain ⟨hG₀1, hG₀τ⟩ := polarDifference_law (m := m) h1 hτ
  have hΩinv : ∀ p ∈ Ω, ∀ a b : ℤ, (p.1, p.2 + a * p.1 + b) ∈ Ω :=
    fun p hp a b => shift_mem_compl_polarDivisor hp a b
  have hG₀law : ∀ p ∈ Ω, ∀ a b : ℤ, G₀ (p.1, p.2 + a * p.1 + b) =
      e p.1 ^ (-(m : ℤ) * a ^ 2) * e p.2 ^ (-2 * (m : ℤ) * a) * G₀ p :=
    fun p hp a b => elliptic_law_iterate (F := G₀) hΩinv hG₀1 hG₀τ hp a b
  -- local extensions
  have hloc : ∀ p ∈ halfPlaneProd, ∃ V ∈ 𝓝 p, ∃ E : ℂ × ℂ → ℂ, DifferentiableOn ℂ E V ∧
      ∀ q ∈ V ∩ Ω, E q = G₀ q := by
    intro p hp
    by_cases hpD : p ∈ polarDivisor S
    · obtain ⟨β, hβ, hpβ⟩ := mem_iUnion₂.mp hpD
      obtain ⟨-, a, b, hab⟩ := mem_divisor_neg_iff.mp hpβ
      obtain ⟨V, hV, E, hE, hEG⟩ := exists_local_extension_line hm hS hpole hβ hp
      set T : ℂ × ℂ → ℂ × ℂ := fun q => (q.1, q.2 - a * q.1 - b) with hT
      have hTc : Continuous T := by fun_prop
      have hTp : T p = (p.1, (β : ℂ)) := by simp only [hT, hab]; ring_nf
      refine ⟨T ⁻¹' V, hTc.continuousAt.preimage_mem_nhds (hTp ▸ hV),
        fun q => e q.1 ^ (-(m : ℤ) * a ^ 2) * e (q.2 - a * q.1 - b) ^ (-2 * (m : ℤ) * a) *
          E (T q), ?_, fun q ⟨hqV, hqΩ⟩ => ?_⟩
      · have hez : ∀ n : ℤ, Differentiable ℂ fun z : ℂ => e z ^ n := fun n z =>
          (differentiable_e z).zpow (Or.inl (Complex.exp_ne_zero _))
        have hTd : Differentiable ℂ T := by simp only [hT]; fun_prop
        refine DifferentiableOn.mul (Differentiable.differentiableOn ?_)
          (hE.comp hTd.differentiableOn fun q hq => hq)
        exact ((hez _).comp differentiable_fst).mul ((hez _).comp (by fun_prop))
      · have hTq : T q ∈ Ω := by
          have := hΩinv q hqΩ (-a) (-b)
          simp only [hT]
          push_cast at this
          convert this using 2
          ring
        beta_reduce
        rw [hEG (T q) ⟨hqV, hTq⟩]
        have := hG₀law _ hTq a b
        simp only [hT] at this
        rw [show q.2 - a * q.1 - b + a * q.1 + b = q.2 by ring] at this
        exact this.symm
    · exact ⟨Ω, (isOpen_compl_polarDivisor S).mem_nhds ⟨hp, hpD⟩, G₀, hG₀d, fun q hq => rfl⟩
  obtain ⟨G, hGd, hGG₀⟩ := exists_differentiableOn_extension isOpen_halfPlaneProd
    (halfPlaneProd_subset_closure_compl_polarDivisor S) hloc
  -- the elliptic law of `G`, by density
  have hdense := halfPlaneProd_subset_closure_compl_polarDivisor S
  have hshift : ∀ c : ℂ × ℂ → ℂ, Continuous c →
      ContinuousOn (fun p : ℂ × ℂ => G (p.1, p.2 + c p)) halfPlaneProd := fun c hc =>
    hGd.continuousOn.comp (by fun_prop) fun p hp => (show (p.1, p.2 + c p) ∈ halfPlaneProd from hp)
  have hlaw1 : EqOn (fun p : ℂ × ℂ => G (p.1, p.2 + 1)) G halfPlaneProd := by
    refine EqOn.of_subset_closure (s := Ω) (fun p hp => ?_) (hshift (fun _ => 1) (by fun_prop))
      hGd.continuousOn sdiff_subset hdense
    have hp' : (p.1, p.2 + 1) ∈ Ω := by simpa using hΩinv p hp 0 1
    rw [hGG₀ _ hp', hGG₀ _ hp]
    exact hG₀1 p hp
  have hlawτ : EqOn (fun p : ℂ × ℂ => G (p.1, p.2 + p.1))
      (fun p => e p.1 ^ (-(m : ℤ)) * e p.2 ^ (-2 * (m : ℤ)) * G p) halfPlaneProd := by
    refine EqOn.of_subset_closure (s := Ω) (fun p hp => ?_) (hshift Prod.fst continuous_fst)
      (ContinuousOn.mul (Continuous.continuousOn ?_) hGd.continuousOn) sdiff_subset hdense
    · have hp' : (p.1, p.2 + p.1) ∈ Ω := by simpa using hΩinv p hp 1 0
      rw [hGG₀ _ hp', hGG₀ _ hp]
      exact hG₀τ p hp
    · have he : Continuous e := differentiable_e.continuous
      exact ((he.comp continuous_fst).zpow₀ _ fun _ => Or.inl (Complex.exp_ne_zero _)).mul
        ((he.comp continuous_snd).zpow₀ _ fun _ => Or.inl (Complex.exp_ne_zero _))
  have hG1 : ∀ τ w : ℂ, 0 < τ.im → G (τ, w + 1) = G (τ, w) := fun τ w hτ' =>
    hlaw1 (show (τ, w) ∈ halfPlaneProd from hτ')
  have hGτ : ∀ τ w : ℂ, 0 < τ.im →
      G (τ, w + τ) = e τ ^ (-(m : ℤ)) * e w ^ (-2 * (m : ℤ)) * G (τ, w) := fun τ w hτ' =>
    hlawτ (show (τ, w) ∈ halfPlaneProd from hτ')
  refine ⟨fun β hβ => (hκ β hβ).1, fun β hβ => (hκ β hβ).2, G, hGd, hGG₀, hG1, hGτ,
    differentiableOn_thetaDecompositionCoeff m hGd,
    fun τ w hτ' => theta_decomposition hm hGd hG1 hGτ hτ' w,
    fun h hh ℓ hℓ τ hτ' => theta_decomposition_unique hm hGd hG1 hGτ hτ' (fun ℓ => h ℓ τ)
      (fun w => hh τ w hτ') ℓ hℓ⟩

end HigherDyson3
