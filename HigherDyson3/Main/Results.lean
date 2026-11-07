/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson3.Main.Statements
public import HigherDyson3.Recurrence.GeneratingFunction
public import HigherDyson3.Recurrence.PartialFractions
public import HigherDyson3.Product.GTailConvergence
public import HigherDyson3.Periodization.CoeffCDisk
public import HigherDyson3.Dyson.AnalyticSeries
public import HigherDyson3.Examples.LevelFive
public import HigherDyson3.Kernel.AppellLerchPoles

/-!
# The numbered results of the manuscript, bundled

Each theorem here collects the displayed claims of one numbered result of [AOS] that the
library proves in several declarations. The individual statements are in
`HigherDyson3/Main/Statements.lean` and in the modules imported here.
-/

public section

open Complex Finset Filter Topology
open scoped ENNReal NNReal

namespace HigherDyson3

/-- **The product `G_d`** [AOS, (1.2), (3.4), §3]: for `m ≥ 2` and `‖q‖ < 1` the product
`∏_{r ≥ 1} (1 + yq^r + ⋯ + (yq^r)^{d-1})` converges, satisfies the multiplication identity
`G_d(y;q) = (∑_{r<d} (yq)^r) G_d(yq;q)` for every `y`, and equals
`(y^d q^d; q^d)_∞ / (yq; q)_∞` when `y q^r ≠ 1` for all `r ≥ 1`. -/
theorem GProduct_properties {m : ℕ} (hm : 2 ≤ m) {q : ℂ} (hq : ‖q‖ < 1) :
    (∀ y : ℂ, Multipliable fun r : ℕ => cyclotomicSum m (y * q ^ (r + 1))) ∧
      (∀ y : ℂ, GProduct m y q = cyclotomicSum m (y * q) * GProduct m (y * q) q) ∧
      ∀ y : ℂ, (∀ r : ℕ, y * q ^ (r + 1) ≠ 1) →
        GProduct m y q = qPochhammerInf (y ^ (2 * m + 1) * q ^ (2 * m + 1)) (q ^ (2 * m + 1)) /
          qPochhammerInf (y * q) q :=
  ⟨multipliable_cyclotomicSum hm hq, GProduct_eq_cyclotomicSum_mul_GProduct hm hq,
    fun _ hy => GProduct_eq_div hm hq hy⟩

/-- **The generating function of the `X_j`** [AOS, Lemma 3.1]: for `m ≥ 2`, `x ∈ ℂ` and
`0 < |q| < 1`, the series `𝓕_{d,x}(t;q)` converges and equals
`∑_n q^{n²} G_d(xq^n;q)/(1 - tq^n)` for `|t| < 1`; the right-hand
side is holomorphic off the points `t = q^{-n}` and has at most simple poles there; and
`𝒢_{d,x}(u;q) = x^{-2} 𝓕_{d,x}(xu;q)` for `|xu| < 1`. -/
theorem genFun_properties {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    (∀ t : ℂ, ‖t‖ < 1 → (Summable fun j : ℕ => XSeries m x j q * t ^ j) ∧
        genFun m x q t = genFunExpansion m x q t) ∧
      (∀ t₀ : ℂ, (∀ n : ℕ, t₀ * q ^ n ≠ 1) → DifferentiableAt ℂ (genFunExpansion m x q) t₀) ∧
      (∀ n₀ : ℕ, Tendsto (fun t => (t - (q ^ n₀)⁻¹) * genFunExpansion m x q t)
        (𝓝[≠] (q ^ n₀)⁻¹) (𝓝 (-(q ^ n₀)⁻¹ * (q ^ (n₀ ^ 2) * gTail m x n₀ q)))) ∧
      ∀ u : ℂ, ‖x * u‖ < 1 → seed m x u q = (x ^ 2)⁻¹ * genFun m x q (x * u) :=
  ⟨fun _ ht => ⟨summable_genFun hm x hq1 ht, genFun_eq_tsum hm x hq1 ht⟩,
    fun _ ht₀ => differentiableAt_genFunExpansion hm x hq0 hq1 ht₀,
    tendsto_sub_mul_genFunExpansion hm x hq0 hq1,
    fun _ hxu => seed_eq_genFun hm hq1 hxu⟩

/-- **Degree and uniqueness of the defect polynomial** [AOS, Theorem 1.1]: `R_{d,x}(U;q)` has
degree at most `d - 2`, and it is the only polynomial of degree at most `d - 2` satisfying the
functional equation (1.4) on a nonempty open set of admissible `u`. -/
theorem defectPoly_degree_le_and_unique {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (defectPoly m x q).degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ) ∧
      ∀ R' : Polynomial ℂ, R'.degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ) →
        ∀ V : Set ℂ, IsOpen V → V.Nonempty →
          (∀ u ∈ V, u ≠ 0 ∧ (∀ k : ℕ, x * u * q ^ k ≠ 1) ∧
            seed m x (q * u) q =
              x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
                q * u ^ (3 - (2 * m + 1 : ℤ)) * R'.eval u -
                Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q) →
          R' = defectPoly m x q :=
  ⟨thm_finite_defect_degree hm hx hq0 hq1,
    fun _ hdeg _ hVo hVne hV => thm_finite_defect_unique hm hx hq0 hq1 hdeg hVo hVne hV⟩

/-- **Constant term and `q`-pole of the defect polynomial** [AOS, Theorem 1.1]: `[U^0] R_{d,x} =
-X_0(x;q)`, and each coefficient `q [U^a] R_{d,x}(U;q)`, `a ≤ d - 2`, extends holomorphically to
the open unit disc, i.e. the coefficients have at most a simple pole at `q = 0`. -/
theorem defectPoly_coeff_zero_and_q_pole {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 0) :
    (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → (defectPoly m x q).coeff 0 = -XSeries m x 0 q) ∧
      ∀ a ≤ 2 * m + 1 - 2, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
        ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * (defectPoly m x q).coeff a :=
  ⟨fun _ hq0 hq1 => thm_finite_defect_constant_term hm hx hq0 hq1,
    fun _ ha => thm_finite_defect_q_pole hm hx ha⟩

/-- **The partial-fraction expansion of the rational defect** [AOS, Proposition 3.2]: for
`m ≥ 2` and `x ≠ 0`: `f_{d,x} = Q_{d,x}/(u(1-u^d)(1-xu)^{ε_x})` and its expansion
`-X_0/u + ∑_r D_{r,x}/(1-ω^r u) + ε_x E_x/(1-xu)` at every admissible `u` and `0 < |q| < 1`;
the uniqueness of the coefficients; and the holomorphy of `q D_{r,x}(q)` and `q E_x(q)` on
`|q| < 1`. -/
theorem partialFraction_properties {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 0) :
    (∀ q u : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → u ≠ 0 → u ^ (2 * m + 1) ≠ 1 → x * u ≠ 1 →
      normalizedDefect m x q u = (rationalDefect m x q).eval u / defectDenom m x u ∧
        (rationalDefect m x q).eval u / defectDenom m x u =
          -XSeries m x 0 q / u + ∑ r ∈ range (2 * m + 1), pfD m x q r / (1 - omega m ^ r * u) +
            (defectEps m x : ℂ) * pfE m x q / (1 - x * u)) ∧
      (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → ∀ (D' : ℕ → ℂ) (E' : ℂ),
        (∀ u : ℂ, u ≠ 0 → u ^ (2 * m + 1) ≠ 1 → x * u ≠ 1 →
          (rationalDefect m x q).eval u / defectDenom m x u =
            -XSeries m x 0 q / u + ∑ r ∈ range (2 * m + 1), D' r / (1 - omega m ^ r * u) +
              (defectEps m x : ℂ) * E' / (1 - x * u)) →
        (∀ r < 2 * m + 1, D' r = pfD m x q r) ∧ (x ^ (2 * m + 1) ≠ 1 → E' = pfE m x q)) ∧
      (∀ r : ℕ, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
        ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * pfD m x q r) ∧
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
        ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * pfE m x q :=
  ⟨fun _ _ hq0 hq1 hu0 hud hxu =>
      ⟨normalizedDefect_eq hm hu0 hud hxu, rationalDefect_div_eq hm hx hq0 hq1 hu0 hud hxu⟩,
    fun _ hq0 hq1 D' E' h => partialFraction_unique hm hx hq0 hq1 D' E' h,
    exists_differentiableOn_eq_mul_pfD hm hx, exists_differentiableOn_eq_mul_pfE hm hx⟩

/-- **Uniform bounds** [AOS, Lemma 5.1]: for `m ≥ 2` and `0 ≤ Q < 1` the tails `g_{k,x}(q)`
with `|x| ≤ 1` are bounded uniformly in `k` on `|q| ≤ Q`; `g_{k,x} → 1` locally uniformly on
`|q| < 1`; and on every compact `S ⊆ (ℍ × ℂ) \ 𝒟_x` the reciprocals `|1 - xuq^j|^{-1}` are bounded
uniformly in `j ∈ ℤ`. -/
theorem uniform_bounds {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∀ Q : ℝ, 0 ≤ Q → Q < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q → ∀ x : ℂ, ‖x‖ ≤ 1 → ‖gTail m x k q‖ ≤ C) ∧
      (TendstoLocallyUniformlyOn (fun k => gTail m (e α) k) (fun _ => 1) atTop
        (Metric.ball 0 1)) ∧
      ∀ S : Set (ℂ × ℂ), IsCompact S → S ⊆ halfPlaneProd \ divisor α →
        ∃ A : ℝ, 0 < A ∧ ∀ p ∈ S, ∀ j : ℤ, ‖1 - e (α : ℂ) * e p.2 * e p.1 ^ j‖⁻¹ ≤ A :=
  ⟨fun _ hQ0 hQ1 => exists_bound_norm_gTail hm hQ0 hQ1 zero_le_one,
    tendstoLocallyUniformlyOn_gTail _, fun S hS hSD => denominator_bound α hα0 hα1 S hS hSD⟩

/-- **Convergence and meromorphy of `ℰ_{m,x}` and `𝒦_{m,x}`** [AOS, Proposition 5.2,
Theorem 1.2(i)]: both series converge normally on compact subsets of `(ℍ × ℂ) \ 𝒟_x`, are
holomorphic there, and have at most simple poles along every component
`w = -α + aτ + b` of `𝒟_x`. -/
theorem periodization_kernel_convergence_and_poles {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∀ S : Set (ℂ × ℂ), IsCompact S → S ⊆ halfPlaneProd \ divisor α →
      ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
        e p.2 ^ (2 * (m : ℤ) * n) * seed m (e α) (e p.1 ^ n * e p.2) (e p.1)‖₊ : ℝ≥0∞) < ∞) ∧
      (∀ S : Set (ℂ × ℂ), IsCompact S → S ⊆ halfPlaneProd \ divisor α →
        ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
          e p.2 ^ (2 * (m : ℤ) * n) / (1 - e α * e p.2 * e p.1 ^ n)‖₊ : ℝ≥0∞) < ∞) ∧
      IsOpen (halfPlaneProd \ divisor α) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => periodization m α p.1 p.2)
        (halfPlaneProd \ divisor α) ∧
      (∀ a b : ℤ, ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd α a b) ∧
        ∀ p ∈ halfPlaneProd \ divisor α,
          N p = (p.2 + α - a * p.1 - b) * periodization m α p.1 p.2) ∧
      ∀ a b : ℤ, ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd α a b) ∧
        ∀ p ∈ halfPlaneProd \ divisor α, N p = (p.2 + α - a * p.1 - b) * kernel m α p.1 p.2 :=
  ⟨fun S hS hSD => thm_elliptic_normal_convergence hm α hα0 hα1 S hS hSD,
    fun S hS hSD => kernel_normal (by omega) α hα0 hα1 S hS hSD,
    (thm_elliptic_holomorphic_off hm α hα0 hα1).1, (thm_elliptic_holomorphic_off hm α hα0 hα1).2,
    thm_elliptic_simple_poles m hm α hα0 hα1, kernel_simple_pole m hm α hα0 hα1⟩

/-- **Twisted law and residues of `ℰ_{m,x}` and `𝒦_{m,x}`** [AOS, Proposition 5.3,
Theorem 1.2(i),(ii)]. -/
theorem periodization_kernel_law_and_residues {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∀ τ w : ℂ, (τ, w) ∈ halfPlaneProd \ divisor α → ∀ a b : ℤ,
      periodization m α τ (w + a * τ + b) =
        e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
          periodization m α τ w) ∧
      (∀ τ w : ℂ, (τ, w) ∈ halfPlaneProd \ divisor α → ∀ a b : ℤ,
        kernel m α τ (w + a * τ + b) =
          e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * kernel m α τ w) ∧
      (∀ τ ∈ upperHalfPlaneSet, ∀ a b : ℤ,
        Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
          (𝓝 (-(rho m α τ / (2 * Real.pi * I)) * e α ^ (2 * ((m : ℤ) + 1) * a) *
            e τ ^ (-(m : ℤ) * a ^ 2)))) ∧
      (∀ τ ∈ upperHalfPlaneSet, ∀ a b : ℤ,
        Tendsto (fun ε : ℂ => ε * kernel m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
          (𝓝 (-1 / (2 * Real.pi * I) * e α ^ (2 * ((m : ℤ) + 1) * a) *
            e τ ^ (-(m : ℤ) * a ^ 2)))) ∧
      DifferentiableOn ℂ (rho m α) upperHalfPlaneSet :=
  ⟨fun _ _ hτw a b => thm_elliptic_twisted_law hm hα0 hα1 hτw a b,
    fun τ w hp a b => kernel_add_mul_add m hm α hα0 hα1 τ w hp a b,
    fun _ hτ a b => thm_elliptic_residue hm hα0 hα1 hτ a b,
    fun _ hτ a b => kernel_residue m hm α hα0 hα1 hτ a b, thm_elliptic_rho_holomorphic hm α⟩

/-- **The leading term of `ρ_{m,x}` and nontriviality of `ℰ_{m,x}`** [AOS, Theorem 1.2(ii)]:
`ρ_{m,x}(τ) = x^{-2} + O(|q|)` as `Im τ → ∞`, and `ℰ_{m,x}` is not identically zero. -/
theorem rho_leading_and_periodization_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ : ℂ, τ ∈ upperHalfPlaneSet → T ≤ τ.im →
      ‖rho m α τ - (e α ^ 2)⁻¹‖ ≤ C * ‖e τ‖) ∧
      ∃ p ∈ halfPlaneProd \ divisor α, periodization m α p.1 p.2 ≠ 0 :=
  ⟨thm_elliptic_rho_leading hm α, thm_elliptic_ne_zero hm hα0 hα1⟩

/-- **Genuine and removable poles** [AOS, Theorem 1.2(iii)]: for fixed `τ`, every point of
the orbit is a simple pole with nonzero residue if `ρ_{m,x}(τ) ≠ 0`, and every singularity on
the orbit is removable if `ρ_{m,x}(τ) = 0`. -/
theorem periodization_pole_dichotomy {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) :
    (rho m α τ ≠ 0 → ∀ a b : ℤ, ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
        (𝓝 L)) ∧
      (rho m α τ = 0 → ∀ a b : ℤ, ∃ L : ℂ,
        Tendsto (fun w => periodization m α τ w) (𝓝[≠] (-(α : ℂ) + a * τ + b)) (𝓝 L)) :=
  ⟨fun hρ a b => thm_elliptic_pole_genuine hm hα0 hα1 hτ hρ a b,
    fun hρ a b => thm_elliptic_pole_removable hm hα0 hα1 hτ hρ a b⟩

/-- **Holomorphy of the finite part and its elliptic laws** [AOS, Proposition 5.4,
Theorem 1.3]: `ℰ^{fin}_{m,x}` agrees off `𝒟_x` with a function holomorphic on `ℍ × ℂ`; it
satisfies the twisted law, and its translate by `α/m` the untwisted law. -/
theorem finitePart_holomorphic_and_laws {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∃ F : ℂ × ℂ → ℂ, DifferentiableOn ℂ F halfPlaneProd ∧
      ∀ p ∈ halfPlaneProd \ divisor α, F p = finitePart m α p.1 p.2) ∧
      (∀ τ w : ℂ, (τ, w) ∈ halfPlaneProd \ divisor α → ∀ a b : ℤ,
        finitePart m α τ (w + a * τ + b) =
          e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
            finitePart m α τ w) ∧
      ∀ τ w : ℂ, (τ, w + (α : ℂ) / m) ∈ halfPlaneProd \ divisor α → ∀ a b : ℤ,
        finitePart m α τ (w + (α : ℂ) / m + a * τ + b) =
          e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
            finitePart m α τ (w + (α : ℂ) / m) :=
  ⟨thm_theta_holomorphic hm hα0 hα1, fun _ _ hτw a b => thm_theta_twisted_law hm hα0 hα1 hτw a b,
    fun _ _ hτw a b => thm_theta_untwisted_law hm hα0 hα1 hτw a b⟩

/-- **The twisted theta expansion of the finite part** [AOS, Proposition 6.1]:
`ℰ^{fin}_{m,x} = ∑_{ℓ<2m} C_{m,ℓ,x} T^{[x]}_{m,ℓ}` off `𝒟_x`, the series for `C_{m,ℓ,x}`
converges normally on compact subsets of `ℍ`, and as a function of `q` it converges normally on
compact subsets of the whole disc `|q| < 1` (including `q = 0`) and is holomorphic there. -/
theorem finitePart_twistedTheta_expansion {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∀ τ w : ℂ, (τ, w) ∈ halfPlaneProd \ divisor α →
      finitePart m α τ w = ∑ ℓ ∈ range (2 * m), coeffC m ℓ α τ * twistedTheta m ℓ α τ w) ∧
      (∀ ℓ < 2 * m, ∀ S : Set ℂ, IsCompact S → S ⊆ upperHalfPlaneSet →
        ∑' k : ℕ, ⨆ τ ∈ S, (‖gTail m (e α) k (e τ) *
          ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
            e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)‖₊ : ℝ≥0∞) < ∞) ∧
      (∀ ℓ : ℕ, ∀ Q : ℝ, 0 ≤ Q → Q < 1 → ∃ M : ℕ → ℝ, Summable M ∧
        ∀ k : ℕ, ∀ q : ℂ, ‖q‖ ≤ Q → ‖coeffCqTerm m ℓ (e α) k q‖ ≤ M k) ∧
      (∀ ℓ : ℕ, DifferentiableOn ℂ (coeffCq m ℓ (e α)) (Metric.ball 0 1)) ∧
      ∀ ℓ : ℕ, ∀ τ : ℂ, coeffC m ℓ α τ = coeffCq m ℓ (e α) (e τ) := by
  have hx : ‖e (α : ℂ)‖ = 1 := by
    rw [e, Complex.norm_exp]; simp
  exact ⟨fun _ _ hτw => finitePart_eq_sum_twistedTheta hm hα0 hα1 hτw,
    fun _ hℓ S hS hSH => coeffC_normal hm hα0 hα1 hℓ S hS hSH,
    fun ℓ _ hQ0 hQ1 => exists_bound_coeffCqTerm hm ℓ hx hQ0 hQ1,
    fun ℓ => differentiableOn_coeffCq hm ℓ hx, fun ℓ τ => coeffC_eq_coeffCq m ℓ α τ⟩

/-- **The theta expansion of the translated finite part** [AOS, Theorem 1.3]:
`ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h_{m,ℓ,x}(τ) ϑ_{m,ℓ}(τ, w)` off the translated
divisor, the coefficients are unique, their series converge normally on compact subsets of `ℍ`,
and they are holomorphic on `ℍ`. -/
theorem finitePart_theta_expansion {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∀ τ ∈ upperHalfPlaneSet, ∀ w : ℂ, (τ, w + (α : ℂ) / m) ∉ divisor α →
      finitePart m α τ (w + (α : ℂ) / m) =
        ∑ ℓ ∈ range (2 * m), thetaCoeffH m ℓ α τ * theta m ℓ τ w) ∧
      (∀ h' : ℕ → ℂ → ℂ, (∀ τ ∈ upperHalfPlaneSet, ∀ w : ℂ, (τ, w + (α : ℂ) / m) ∉ divisor α →
        finitePart m α τ (w + (α : ℂ) / m) = ∑ ℓ ∈ range (2 * m), h' ℓ τ * theta m ℓ τ w) →
        ∀ ℓ < 2 * m, ∀ τ ∈ upperHalfPlaneSet, h' ℓ τ = thetaCoeffH m ℓ α τ) ∧
      (∀ ℓ < 2 * m, ∀ S : Set ℂ, IsCompact S → S ⊆ upperHalfPlaneSet →
        ∑' k : ℕ, ⨆ τ ∈ S, (‖e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) *
          e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
          (gTail m (e α) k (e τ) *
            ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
              e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s))‖₊ : ℝ≥0∞) < ∞) ∧
      ∀ ℓ < 2 * m, DifferentiableOn ℂ (thetaCoeffH m ℓ α) upperHalfPlaneSet :=
  ⟨fun _ hτ _ hw => thm_theta_expansion hm hα0 hα1 hτ hw,
    fun h' hh' => thm_theta_unique hm hα0 hα1 h' hh',
    fun _ hℓ S hS hSH => thm_theta_coeff_normal hm hα0 hα1 hℓ S hS hSH,
    fun _ hℓ => thm_theta_coeff_holomorphic hm hα0 hα1 hℓ⟩

/-- **Leading terms and nonvanishing** [AOS, Theorem 1.3]: with `c_ℓ = 1 + ℓ - ℓ²/(4m)`,
`h_{m,ℓ,x}(τ) = e(ℓα/m) x^{ℓ-2} q^{c_ℓ} (1 + O(q²))`; no `h_{m,ℓ,x}` vanishes identically; and
the finite part is not identically zero. -/
theorem thetaCoeff_leading_and_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    (∀ ℓ < 2 * m, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖thetaCoeffH m ℓ α τ -
          e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) * e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m)) * τ)‖ ≤
        C * ‖e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m) + 2) * τ)‖) ∧
      (∀ ℓ < 2 * m, ∃ τ ∈ upperHalfPlaneSet, thetaCoeffH m ℓ α τ ≠ 0) ∧
      ∃ p ∈ halfPlaneProd \ divisor α, finitePart m α p.1 p.2 ≠ 0 :=
  ⟨fun _ hℓ => thm_theta_leading hm hα0 hα1 hℓ, fun _ hℓ => thm_theta_coeff_ne_zero hm hα0 hα1 hℓ,
    thm_theta_finite_ne_zero hm hα0 hα1⟩

/-- **The first new case `m = 2`, `d = 5`** [AOS, §8]: the recurrence at `x = 1` with
`G_5(1;q) = (q^5;q^5)_∞/(q;q)_∞`, the cubic `R_{5,1}`; for the nontrivial fifth roots of unity
`x`: the homogeneous recurrence, the boundary values, the cubic `R_{5,x}`, the functional
equation, `Q_{5,x} = (1-u)R_{5,x}` with `D_{r,x}` and `D_{0,x} = 0`, and the simplified `ρ_{2,x}`
and `C_{2,ℓ,x}`; and the leading terms of `h_{2,ℓ,x}`. -/
theorem levelFive_properties :
    (∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → ∀ j : ℤ,
      XSeries 2 1 (j - 2) q + XSeries 2 1 (j - 1) q + XSeries 2 1 j q + XSeries 2 1 (j + 1) q +
        XSeries 2 1 (j + 2) q - q ^ (j - 1) * XSeries 2 1 j q = 5 * GProduct 2 1 q) ∧
    (∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 →
      GProduct 2 1 q = qPochhammerInf (q ^ 5) (q ^ 5) / qPochhammerInf q q) ∧
    (∀ q : ℂ, defectPoly 2 1 q =
      Polynomial.C (XSeries 2 1 0 q) *
          (Polynomial.C q⁻¹ * Polynomial.X ^ 2 - Polynomial.X ^ 3 - Polynomial.X ^ 2 -
            Polynomial.X - 1) -
        Polynomial.C (XSeries 2 1 1 q) * (Polynomial.X ^ 2 + Polynomial.X) -
        Polynomial.C (XSeries 2 1 2 q) * (Polynomial.X ^ 3 + Polynomial.X ^ 2) -
        Polynomial.C (XSeries 2 1 3 q) * Polynomial.X ^ 3) ∧
    (∀ x q : ℂ, defectPoly 2 x q =
      Polynomial.C (XSeries 2 x 0 q) * (Polynomial.C (q⁻¹ * (x ^ 2)⁻¹) * Polynomial.X ^ 2 -
          Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X - 1) +
        Polynomial.C (XSeries 2 x 1 q) * (Polynomial.C x⁻¹ * Polynomial.X ^ 3 -
          Polynomial.C x * Polynomial.X ^ 3 - Polynomial.C x * Polynomial.X ^ 2 -
          Polynomial.C x * Polynomial.X) -
        Polynomial.C (x ^ 2 * XSeries 2 x 2 q) * (Polynomial.X ^ 3 + Polynomial.X ^ 2) -
        Polynomial.C (x ^ 3 * XSeries 2 x 3 q) * Polynomial.X ^ 3) ∧
    (∀ x q : ℂ, x ≠ 1 → x ^ 5 = 1 → q ≠ 0 → ‖q‖ < 1 → ∀ j : ℤ,
      XSeries 2 x (j - 2) q + x * XSeries 2 x (j - 1) q + x ^ 2 * XSeries 2 x j q +
        x ^ 3 * XSeries 2 x (j + 1) q + x ^ 4 * XSeries 2 x (j + 2) q -
        q ^ (j - 1) * XSeries 2 x j q = 0) ∧
    (∀ x q : ℂ, x ≠ 1 → x ^ 5 = 1 → q ≠ 0 → ‖q‖ < 1 →
      XSeries 2 x (-1) q = -x * XSeries 2 x 0 q + (1 - x ^ 2) * XSeries 2 x 1 q -
          x ^ 3 * XSeries 2 x 2 q - x ^ 4 * XSeries 2 x 3 q ∧
        XSeries 2 x (-2) q = q⁻¹ * XSeries 2 x 0 q - x * XSeries 2 x 1 q + XSeries 2 x 3 q) ∧
    (∀ x q u : ℂ, x ≠ 1 → x ^ 5 = 1 → 0 < ‖q‖ → ‖q‖ < 1 → u ≠ 0 → u ≠ 1 →
      (∀ k : ℕ, x * u * q ^ k ≠ 1) →
      seed 2 x (q * u) q =
        x ^ 2 * q * ((u ^ 5 - 1) / (u ^ 2 * (u - 1))) * seed 2 x u q +
          q * u ^ (-2 : ℤ) * (defectPoly 2 x q).eval u) ∧
    (∀ x q : ℂ, x ≠ 1 → x ^ 5 = 1 →
      rationalDefect 2 x q = (1 - Polynomial.X) * defectPoly 2 x q ∧
        (∀ r : ℕ, pfD 2 x q r = omega 2 ^ r / 5 * (1 - (omega 2 ^ r)⁻¹) *
          (defectPoly 2 x q).eval (omega 2 ^ r)⁻¹) ∧ pfD 2 x q 0 = 0) ∧
    (∀ α : ℚ, e α ^ 5 = 1 → ∀ τ : ℂ,
      rho 2 α τ = (e α ^ 2)⁻¹ * ∑' k : ℕ, e α ^ k * e τ ^ (3 * k ^ 2) * gTail 2 (e α) k (e τ)) ∧
    (∀ α : ℚ, e α ^ 5 = 1 → ∀ (ℓ : ℕ) (τ : ℂ),
      coeffC 2 ℓ α τ = e α ^ ((ℓ : ℤ) - 2) * ∑' k : ℕ, gTail 2 (e α) k (e τ) *
        ∑ s ∈ Icc 1 k, e α ^ ((k : ℤ) - s) * e τ ^ (3 * (k : ℤ) ^ 2 - 2 * (s : ℤ) ^ 2 + ℓ * s)) ∧
    ∀ α : ℚ, 0 ≤ α → α < 1 → ∀ ℓ < 4, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
      ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
        ‖thetaCoeffH 2 ℓ α τ -
            e (ℓ * α / 2) * e α ^ ((ℓ : ℤ) - 2) * e ((1 + ℓ - (ℓ : ℂ) ^ 2 / 8) * τ)‖ ≤
          C * ‖e ((1 + ℓ - (ℓ : ℂ) ^ 2 / 8 + 2) * τ)‖ := by
  refine ⟨fun q hq0 hq1 j => recurrence_two_one hq0 hq1 j, fun q hq0 hq1 => ?_,
    defectPoly_two_one, defectPoly_two,
    fun x q hx hx5 hq0 hq1 j => recurrence_two_of_pow_five hx hx5 hq0 hq1 j,
    fun x q hx hx5 hq0 hq1 => boundary_two_of_pow_five hx hx5 hq0 hq1,
    fun x q u hx hx5 hq0 hq1 hu hu1 hxu => seed_mul_two_of_pow_five hx hx5 hq0 hq1 hu hu1 hxu,
    fun x q hx hx5 => partialFraction_two_of_pow_five hx hx5 q,
    fun α hx5 τ => rho_two_of_pow_five hx5 τ, fun α hx5 ℓ τ => coeffC_two_of_pow_five hx5 ℓ τ,
    fun α hα0 hα1 ℓ hℓ => thetaCoeffH_two_leading hα0 hα1 hℓ⟩
  have h := GProduct_eq_div (le_refl 2) hq1 (y := 1) fun r h => by
    have := congrArg norm h
    rw [one_mul, norm_pow, norm_one] at this
    exact absurd this (ne_of_lt (pow_lt_one₀ (norm_nonneg q) hq1 (by omega)))
  simpa using h

/-- **Appell–Lerch kernels** [AOS, Proposition 4.3]: for `m ≥ 1` and `β ∈ ℚ`, the series
`A_{m,β}` converges normally on compact subsets of `(ℍ × ℂ)` off the orbit
`w ≡ β (mod ℤτ + ℤ)` and is holomorphic there; it satisfies the index-`m` elliptic law; it has at
most simple poles along each line `w = β + aτ + b`, and each point of the orbit is a genuine
simple pole with residue `q^{-ma²} e(β)^{-2ma}/(2πi)` (at `w = β`: `2πiε A(τ, β+ε) → 1`, i.e.
`A_{m,β}(τ, β + ε) = 1/(2πiε) + O(1)`). -/
theorem appellLerch_properties {m : ℕ} (hm : 1 ≤ m) (β : ℚ) :
    (∀ S : Set (ℂ × ℂ), IsCompact S → S ⊆ halfPlaneProd \ divisor (-β) →
      ∃ M : ℤ → ℝ, Summable M ∧ ∀ n, ∀ p ∈ S, ‖appellLerchTerm m β n p‖ ≤ M n) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => appellLerch m β p.1 p.2)
        (halfPlaneProd \ divisor (-β)) ∧
      (∀ τ w : ℂ, ∀ a b : ℤ, appellLerch m β τ (w + a * τ + b) =
        e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) * appellLerch m β τ w) ∧
      (∀ a b : ℤ, ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd (-β) a b) ∧
        ∀ p ∈ halfPlaneProd \ divisor (-β),
          N p = (p.2 - β - a * p.1 - b) * appellLerch m β p.1 p.2) ∧
      (∀ τ : ℂ, 0 < τ.im →
        Tendsto (fun ε : ℂ => 2 * Real.pi * I * ε * appellLerch m β τ (β + ε)) (𝓝[≠] 0) (𝓝 1)) ∧
      ∀ τ : ℂ, 0 < τ.im → ∀ a b : ℤ,
        Tendsto (fun ε : ℂ => ε * appellLerch m β τ (β + a * τ + b + ε)) (𝓝[≠] 0)
          (𝓝 (e τ ^ (-(m : ℤ) * a ^ 2) * e β ^ (-2 * (m : ℤ) * a) / (2 * Real.pi * I))) ∧
        e τ ^ (-(m : ℤ) * a ^ 2) * e β ^ (-2 * (m : ℤ) * a) / (2 * Real.pi * I) ≠ 0 :=
  ⟨fun S hS hSD => appellLerch_normal hm β S hS hSD, appellLerch_differentiableOn hm β,
    fun τ w a b => appellLerch_add_mul_add m β τ w a b, appellLerch_simple_pole hm β,
    fun _ hτ => appellLerch_residue hm β hτ, fun _ hτ a b => appellLerch_residue_orbit hm β hτ a b⟩

end HigherDyson3
