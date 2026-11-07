/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Lambert.Slice

/-!
# Joint local form of the poles of a Lambert periodization

Near a point `p₀` of a component `L_{a,k} = {w = -β + aτ + k}` of an orbit `𝒟_{e(β)}`, the
periodization `ℰ_Φ` of a Lambert seed with pole parameter `e(β')` satisfies
`(w + β - aτ - k) ℰ_Φ = N` for a function `N` holomorphic near `p₀`: if `β' = β` by
[AOS, Lemma 7.4(a)], and otherwise because distinct orbits are disjoint, so that `ℰ_Φ` itself is
holomorphic near `p₀`.

## Main results

* `HigherDyson3.eq_of_mem_divisor_of_mem_divisor`: distinct orbits are disjoint.
* `HigherDyson3.exists_differentiableAt_sub_mul_seedPeriodization_lambertSeed`.
-/

public section

noncomputable section

open Complex Filter Topology

namespace HigherDyson3

variable {m : ℕ}

/-- **Distinct orbits are disjoint**: for `β, β' ∈ ℚ ∩ [0,1)`, `𝒟_{e(β)} ∩ 𝒟_{e(β')} = ∅`
unless `β = β'` [AOS, §7]. -/
theorem eq_of_mem_divisor_of_mem_divisor {β β' : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβ'0 : 0 ≤ β') (hβ'1 : β' < 1) {p : ℂ × ℂ} (h : p ∈ divisor β) (h' : p ∈ divisor β') :
    β = β' := by
  obtain ⟨a, b, hp, hw⟩ := Set.mem_iUnion₂.mp h
  obtain ⟨a', b', -, hw'⟩ := Set.mem_iUnion₂.mp h'
  have hp' : 0 < p.1.im := hp
  have heq : -(β : ℂ) + a * p.1 + b = -(β' : ℂ) + a' * p.1 + b' := hw.symm.trans hw'
  have him : ((a : ℝ) - a') * p.1.im = 0 := by
    have := congrArg Complex.im heq
    simp only [add_im, neg_im, ratCast_im, neg_zero, mul_im, intCast_re, intCast_im, zero_mul,
      add_zero, zero_add] at this
    linarith
  have ha : a = a' := by
    have := (mul_eq_zero.mp him).resolve_right hp'.ne'
    exact_mod_cast sub_eq_zero.mp this
  subst ha
  have hb : ((β' - β : ℚ) : ℂ) = ((b' - b : ℤ) : ℚ) := by
    push_cast
    linear_combination heq
  have hb' : (β' - β : ℚ) = ((b' - b : ℤ) : ℚ) := by exact_mod_cast hb
  have h1 : ((b' - b : ℤ) : ℚ) < 1 := by linarith
  have h2 : -1 < ((b' - b : ℤ) : ℚ) := by linarith
  have h3 : b' - b < 1 := by exact_mod_cast h1
  have h4 : -1 < b' - b := by exact_mod_cast h2
  have hb0 : b' - b = 0 := by omega
  rw [hb0, Int.cast_zero, sub_eq_zero] at hb'
  exact hb'.symm

/-- A point of `L_{a,k}` lies in `Ω_{a,k}`. -/
lemma mem_divisorNbhd_of_mem_divisorComponent {β : ℚ} {a k : ℤ} {p : ℂ × ℂ}
    (hp : p ∈ divisorComponent β a k) : p ∈ divisorNbhd β a k := by
  have h := kernelResidue_mem_divisorNbhd β (τ := p.1) hp.1 a k
  have hp2 : p = (p.1, -(β : ℂ) + a * p.1 + k) := Prod.ext rfl hp.2
  rwa [hp2]

/-- **Joint local form of the poles.** Let `p₀ ∈ L_{a,k} ⊆ 𝒟_{e(β)}` and let `Φ` be a Lambert seed
with pole parameter `e(β')`. Then `(w + β - aτ - k) ℰ_Φ(τ,w)` agrees near `p₀`, off `𝒟_{e(β')}`,
with a function holomorphic near `p₀`. -/
theorem exists_differentiableAt_sub_mul_seedPeriodization_lambertSeed (hm : 1 ≤ m) (α : ℚ)
    {β' : ℚ} (hβ'0 : 0 ≤ β') (hβ'1 : β' < 1) {b : ℕ → ℂ → ℂ}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (Metric.ball 0 1))
    (hB : ∀ Q : ℝ, 0 < Q → Q < 1 → ∃ B : ℝ, ∀ i q, ‖q‖ ≤ Q → ‖b i q‖ ≤ B * ‖q‖ ^ (i ^ 2))
    {β : ℚ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a k : ℤ} {p₀ : ℂ × ℂ}
    (hp₀ : p₀ ∈ divisorComponent β a k) :
    ∃ N : ℂ × ℂ → ℂ, (∀ᶠ p in 𝓝 p₀, DifferentiableAt ℂ N p) ∧
      ∀ᶠ p in 𝓝 p₀, p ∈ halfPlaneProd \ divisor β' →
        N p = (p.2 + β - a * p.1 - k) *
          seedPeriodization m α (lambertSeed (e α) (e β') b) p.1 p.2 := by
  by_cases h : β' = β
  · subst h
    obtain ⟨N, hN, hNe⟩ := seedPeriodization_lambertSeed_simple_poles hm α hβ0 hβ1 hb hB a k
    have hU := divisorNbhd_isOpen β' hβ0 hβ1 a k
    refine ⟨N, ?_, Filter.Eventually.of_forall hNe⟩
    filter_upwards [hU.mem_nhds (mem_divisorNbhd_of_mem_divisorComponent hp₀)] with p hp
    exact hN.differentiableAt (hU.mem_nhds hp)
  · have hp₀' : p₀ ∈ halfPlaneProd \ divisor β' := ⟨hp₀.1, fun h' => h
      (eq_of_mem_divisor_of_mem_divisor hβ0 hβ1 hβ'0 hβ'1
        (Set.mem_iUnion₂.mpr ⟨a, k, hp₀⟩) h').symm⟩
    obtain ⟨hU, hD⟩ := differentiableOn_seedPeriodization_lambertSeed (m := m) hm α hβ'0 hβ'1
      hb hB
    refine ⟨fun p => (p.2 + β - a * p.1 - k) *
      seedPeriodization m α (lambertSeed (e α) (e β') b) p.1 p.2, ?_,
      Filter.Eventually.of_forall fun p _ => rfl⟩
    filter_upwards [hU.mem_nhds hp₀'] with p hp
    have hz : Differentiable ℂ fun p : ℂ × ℂ => p.2 + β - a * p.1 - k := by fun_prop
    exact hz.differentiableAt.mul (hD.differentiableAt (hU.mem_nhds hp))

end HigherDyson3
