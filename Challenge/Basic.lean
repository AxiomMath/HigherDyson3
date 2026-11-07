/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-! # The formal challenge file

The formal statements this repository proves: the higher Dyson rank generating function, the
finite recurrence and functional equation of the seed, the elliptic periodization and its
theta decomposition, and the characterization of the seed by the recurrence, stated over Mathlib
alone.

-/

@[expose] public section

noncomputable section

open Complex Finset

namespace HigherDyson3

/-! ## Conventions -/

/-- The normalized exponential `e(z) = exp(2πiz)`. -/
def e (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

/-- The upper half-plane `ℍ = {τ : 0 < Im τ}`, as a subset of `ℂ`. -/
def upperHalfPlaneSet : Set ℂ := {τ | 0 < τ.im}

/-- The domain `ℍ × ℂ` of the elliptic objects, as a subset of `ℂ × ℂ`. -/
def halfPlaneProd : Set (ℂ × ℂ) := {p | 0 < p.1.im}

/-! ## Dyson symbols and their generating function -/

/-- A partition: a finite multiset of positive integers, its parts. -/
abbrev Partition : Type := Multiset ℕ+

namespace Partition

/-- The size `|λ|` of a partition: the sum of its parts, with multiplicity. -/
def size (p : Partition) : ℕ := (p.map ((↑) : ℕ+ → ℕ)).sum

/-- The length `ℓ(λ)` of a partition: the number of its parts, with multiplicity. -/
def length (p : Partition) : ℕ := Multiset.card p

end Partition

/-- `𝒫_{≤n}`: the partitions all of whose parts are at most `n`. -/
def boundedPartitions (n : ℕ) : Set Partition := {p | ∀ i ∈ p, (i : ℕ) ≤ n}

/-- An uncoupled `m`-Dyson symbol `(n; α₁, β₁, …, α_m, β_m)`: a square `n` and `2m`
partitions with parts at most `n`. The pair `(α j, β j)` is the paper's `(α_{j+1}, β_{j+1})`. -/
structure DysonSymbol (m : ℕ) where
  /-- The square `n(Σ)` of the symbol. -/
  n : ℕ
  /-- The partitions `α₁, …, α_m`. -/
  α : Fin m → Partition
  /-- The partitions `β₁, …, β_m`. -/
  β : Fin m → Partition
  α_mem : ∀ j, α j ∈ boundedPartitions n
  β_mem : ∀ j, β j ∈ boundedPartitions n

namespace DysonSymbol

variable {m : ℕ}

/-- The size `|Σ| = n² + ∑_j (|α_j| + |β_j|)` of a Dyson symbol. -/
def size (s : DysonSymbol m) : ℕ := s.n ^ 2 + ∑ j, ((s.α j).size + (s.β j).size)

/-- The full rank `FR_m(Σ) = ∑_{j=1}^m j (ℓ(α_j) - ℓ(β_j))`. -/
def fullRank (s : DysonSymbol m) : ℤ :=
  ∑ j : Fin m, ((j : ℤ) + 1) * (((s.α j).length : ℤ) - (s.β j).length)

end DysonSymbol

/-- `N_m(r, N)`: the number of `m`-Dyson symbols of size `N` and full rank `r`
(`0` if there are infinitely many). -/
def rankCount (m : ℕ) (r : ℤ) (N : ℕ) : ℕ :=
  Nat.card {s : DysonSymbol m // s.size = N ∧ s.fullRank = r}

/-- The coefficient ring `𝒜 = ℤ[z, z⁻¹]`; the series ring is `PowerSeries LaurentRing`. -/
abbrev LaurentRing : Type := LaurentPolynomial ℤ

/-- The coefficient `[q^N] f` of a series `f ∈ 𝒜[[q]]`. -/
def qCoeff (N : ℕ) (f : PowerSeries LaurentRing) : LaurentRing := PowerSeries.coeff N f

/-- The coefficient `[z^r] P` of a Laurent polynomial `P ∈ 𝒜`. -/
def zCoeff (r : ℤ) (P : LaurentRing) : ℤ := P.coeff r

/-- The formal inverse `f⁻¹` of a series with constant term `1`:
`b₀ = 1`, `b_N = -∑_{k=1}^N ([q^k] f) b_{N-k}`. -/
def seriesInv (f : PowerSeries LaurentRing) : PowerSeries LaurentRing :=
  PowerSeries.invOfUnit f 1

/-- The `q`-Pochhammer symbol `(cq; q)_n = ∏_{r=1}^n (1 - c q^r)`. -/
def qPoch (c : LaurentRing) (n : ℕ) : PowerSeries LaurentRing :=
  ∏ r ∈ Icc 1 n, (1 - PowerSeries.C c * PowerSeries.X ^ r)

/-- The `n`-th term `𝒯_{m,n} = q^{n²} (∏_{j=1}^m (z^j q;q)_n (z^{-j} q;q)_n)⁻¹`. -/
def RTerm (m n : ℕ) : PowerSeries LaurentRing :=
  PowerSeries.X ^ (n ^ 2) *
    seriesInv (∏ j ∈ Icc 1 m,
      qPoch (LaurentPolynomial.T (j : ℤ)) n * qPoch (LaurentPolynomial.T (-(j : ℤ))) n)

/-- The higher rank series `R_m(z;q)`, coefficientwise `[q^N] R_m = ∑_n [q^N] 𝒯_{m,n}`
(a finitely supported sum, `0` if infinitely many summands are nonzero). -/
def RSeries (m : ℕ) : PowerSeries LaurentRing :=
  PowerSeries.mk fun N => ∑ᶠ n : ℕ, PowerSeries.coeff N (RTerm m n)

/-- The partition series `Φ_{c,n}`, `[q^N] Φ_{c,n} = ∑ c^{ℓ(λ)}` over the partitions `λ`
of `N` with all parts at most `n`. -/
def partitionSeries (c : LaurentRing) (n : ℕ) : PowerSeries LaurentRing :=
  PowerSeries.mk fun N =>
    ∑ᶠ (p : Partition) (_ : p ∈ boundedPartitions n ∧ p.size = N), c ^ p.length

/-! ## The higher Dyson deformation: product, tails, seed, values and defect -/

/-- The cyclotomic sum `P_d(z) = ∑_{s=0}^{d-1} z^s`, `d = 2m + 1`. -/
def cyclotomicSum (m : ℕ) (z : ℂ) : ℂ := ∑ s ∈ range (2 * m + 1), z ^ s

/-- The product `G_d(y;q) = ∏_{r ≥ 1} P_d(y q^r)`. -/
def GProduct (m : ℕ) (y q : ℂ) : ℂ := ∏' r : ℕ, cyclotomicSum m (y * q ^ (r + 1))

/-- The tails `g_{k,x}(q) = G_d(x q^k; q)`. -/
def gTail (m : ℕ) (x : ℂ) (k : ℕ) (q : ℂ) : ℂ := GProduct m (x * q ^ k) q

/-- The seed `𝒢_{d,x}(u;q) = x⁻² ∑_{k ≥ 0} q^{k²} g_{k,x}(q) / (1 - x u q^k)`. -/
def seed (m : ℕ) (x u q : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * ∑' k : ℕ, q ^ (k ^ 2) * gTail m x k q / (1 - x * u * q ^ k)

/-- The values `X_j^{(m)}(x;q) = ∑_{k ≥ 0} q^{k² + jk} g_{k,x}(q)`, `j ∈ ℤ`. -/
def XSeries (m : ℕ) (x : ℂ) (j : ℤ) (q : ℂ) : ℂ :=
  ∑' k : ℕ, q ^ ((k : ℤ) ^ 2 + j * k) * gTail m x k q

/-- The constant `C_x = P_d(x)`. -/
def Cx (m : ℕ) (x : ℂ) : ℂ := cyclotomicSum m x

/-- The defect polynomial
`R_{d,x}(U;q) = q⁻¹x⁻²X₀ U^{d-3} + x⁻¹X₁ U^{d-2} - ∑_{k=0}^{d-2} x^k X_k ∑_{a=k}^{d-2} U^a`. -/
def defectPoly (m : ℕ) (x q : ℂ) : Polynomial ℂ :=
  Polynomial.C (q⁻¹ * (x ^ 2)⁻¹ * XSeries m x 0 q) * Polynomial.X ^ (2 * m + 1 - 3) +
    Polynomial.C (x⁻¹ * XSeries m x 1 q) * Polynomial.X ^ (2 * m + 1 - 2) -
    ∑ k ∈ range (2 * m + 1 - 1), Polynomial.C (x ^ k * XSeries m x k q) *
      ∑ a ∈ Icc k (2 * m + 1 - 2), Polynomial.X ^ a

/-- The raw defect
`ℬ_{d,x}(u;q) = x⁻²(X_{-2} - G_d(x;q)) + x⁻¹(1+u)(X_{-1} - G_d(x;q))
  - ∑_{r=3}^{d-1} ∑_{i=0}^{r-3} x^i u^{i+2-r} (X_i - G_d(x;q))`. -/
def rawDefect (m : ℕ) (x u q : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * (XSeries m x (-2) q - GProduct m x q) +
    x⁻¹ * (1 + u) * (XSeries m x (-1) q - GProduct m x q) -
    ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2),
      x ^ i * u ^ ((i : ℤ) + 2 - r) * (XSeries m x i q - GProduct m x q)

/-! ## Elliptic toolkit: divisor, theta series, kernel -/

/-- The divisor component `L_{a,b} = {(τ, w) ∈ ℍ × ℂ : w = -α + aτ + b}`. -/
def divisorComponent (α : ℚ) (a b : ℤ) : Set (ℂ × ℂ) :=
  {p | 0 < p.1.im ∧ p.2 = -(α : ℂ) + a * p.1 + b}

/-- The divisor `𝒟_x = ⋃_{(a,b) ∈ ℤ²} L_{a,b} ⊆ ℍ × ℂ`, `x = e(α)`. -/
def divisor (α : ℚ) : Set (ℂ × ℂ) := ⋃ (a : ℤ) (b : ℤ), divisorComponent α a b

/-- The neighbourhood `Ω_{a,b} = (ℍ × ℂ) \ ⋃_{(a',b') ≠ (a,b)} L_{a',b'}` of one component. -/
def divisorNbhd (α : ℚ) (a b : ℤ) : Set (ℂ × ℂ) :=
  halfPlaneProd \ ⋃ (c : ℤ × ℤ) (_ : c ≠ (a, b)), divisorComponent α c.1 c.2

/-- The theta series `ϑ_{m,ℓ}(τ,w) = ∑_{j ∈ ℤ} e((ℓ+2mj)²τ/(4m)) e((ℓ+2mj)w)`. -/
def theta (m ℓ : ℕ) (τ w : ℂ) : ℂ :=
  ∑' j : ℤ, e (((ℓ : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m)) * e (((ℓ : ℂ) + 2 * m * j) * w)

/-- The twisted theta series `T^{[x]}_{m,ℓ}(τ,w) = ∑_{j ∈ ℤ} x^{-2j} q^{mj²+ℓj} u^{ℓ+2mj}`,
`x = e(α)`, `q = e(τ)`, `u = e(w)`. -/
def twistedTheta (m ℓ : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  ∑' j : ℤ, e α ^ (-2 * j) * e τ ^ ((m : ℤ) * j ^ 2 + ℓ * j) * e w ^ ((ℓ : ℤ) + 2 * m * j)

/-- The kernel `𝒦_{m,x}(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} / (1 - x u q^n)`. -/
def kernel (m : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) /
    (1 - e α * e w * e τ ^ n)

/-- The regular part `𝒦^{(a)}_{m,x}` of the kernel: the kernel's series without the
summand `n = -a`. -/
def kernelRegular (m : ℕ) (α : ℚ) (a : ℤ) (τ w : ℂ) : ℂ :=
  ∑' n : {n : ℤ // n ≠ -a}, e α ^ (-2 * (n : ℤ)) * e τ ^ ((m : ℤ) * (n : ℤ) ^ 2) *
    e w ^ (2 * (m : ℤ) * n) / (1 - e α * e w * e τ ^ (n : ℤ))

/-- The quotient `Φ(z) = z / (1 - e(z))`, extended by `Φ(0) = -1/(2πi)`. -/
def expQuotient (z : ℂ) : ℂ :=
  if z = 0 then -1 / (2 * Real.pi * Complex.I) else z / (1 - e z)

/-! ## The periodization and its layers -/

/-- The periodization `ℰ_{m,x}(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} 𝒢_{d,x}(q^n u; q)`. -/
def periodization (m : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
    seed m (e α) (e τ ^ n * e w) (e τ)

/-- The double summand
`ℰ^{dbl}_{n,k}(τ,w) = x⁻² x^{-2n} q^{mn²+k²} u^{2mn} g_{k,x}(q) / (1 - x u q^{n+k})`. -/
def doubleSummand (m : ℕ) (α : ℚ) (n : ℤ) (k : ℕ) (τ w : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2 + (k : ℤ) ^ 2) *
    e w ^ (2 * (m : ℤ) * n) * gTail m (e α) k (e τ) / (1 - e α * e w * e τ ^ (n + k))

/-- The residue coefficient `ρ_{m,x}(τ) = x⁻² ∑_{k ≥ 0} x^{2(m+1)k} q^{(m+1)k²} g_{k,x}(q)`. -/
def rho (m : ℕ) (α : ℚ) (τ : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * ∑' k : ℕ, e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) *
    gTail m (e α) k (e τ)

/-- The theta coefficients
`C_{m,ℓ,x}(τ) = x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}`
(the summand `k = 0` is an empty sum). -/
def coeffC (m ℓ : ℕ) (α : ℚ) (τ : ℂ) : ℂ :=
  e α ^ ((ℓ : ℤ) - 2) * ∑' k : ℕ, gTail m (e α) k (e τ) *
    ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
      e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)

/-! ## The finite part and the theta coefficients -/

/-- The finite part `ℰ^{fin}_{m,x} = ℰ_{m,x} - ρ_{m,x} 𝒦_{m,x}`. -/
def finitePart (m : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  periodization m α τ w - rho m α τ * kernel m α τ w

/-- The theta coefficients `h_{m,ℓ,x}(τ) = e(ℓα/m) x^{ℓ-2} q^{-ℓ²/(4m)}
  ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}`,
with `q^{-ℓ²/(4m)} = e(-ℓ²τ/(4m))`. -/
def thetaCoeffH (m ℓ : ℕ) (α : ℚ) (τ : ℂ) : ℂ :=
  e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
    ∑' k : ℕ, gTail m (e α) k (e τ) *
      ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
        e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)

/-! ## The characterization of the Dyson seed -/

/-- The finite `q`-Pochhammer symbol `(a;q)_n = ∏_{l=0}^{n-1} (1 - a q^l)`, over `ℂ`. -/
def qPochhammer (a q : ℂ) (n : ℕ) : ℂ := ∏ l ∈ range n, (1 - a * q ^ l)

/-- The solution family `V_γ` of [AOS, (7.4)]: sequences `(Y_j)_{j ≥ 0}` with
`∑_{r=0}^{d-1} x^r Y_{j+r-2} - q^{j-1} Y_j = C_x γ` for all `j ≥ 2`. -/
def recurrenceFamily (m : ℕ) (x q γ : ℂ) : Set (ℕ → ℂ) :=
  {Y | ∀ j : ℕ, 2 ≤ j →
    ∑ r ∈ range (2 * m + 1), x ^ r * Y (j + r - 2) - q ^ (j - 1) * Y j = Cx m x * γ}

/-- The family `V = ⋃_γ V_γ` of [AOS, §7]. -/
def recurrenceSolutions (m : ℕ) (x q : ℂ) : Set (ℕ → ℂ) :=
  ⋃ γ : ℂ, recurrenceFamily m x q γ

/-- The primitive `d`-th root of unity `ω = e(1/d)`, `d = 2m + 1`. -/
def omega (m : ℕ) : ℂ := e (1 / (2 * m + 1 : ℂ))

/-- The seed `𝒢_Y(u) = x^{-2} ∑_{j ≥ 0} Y_j (xu)^j` of a sequence `Y` [AOS, (7.7)]. -/
def sequenceSeed (x : ℂ) (Y : ℕ → ℂ) (u : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * ∑' j : ℕ, Y j * (x * u) ^ j

/-- The bilateral periodization `ℰ_Φ(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} Φ(q^n u; q)`
of a seed `Φ(u; q)` [AOS, (7.7), (7.10)], with `x = e(α)`, `q = e(τ)`, `u = e(w)`. -/
def seedPeriodization (m : ℕ) (α : ℚ) (Φ : ℂ → ℂ → ℂ) (τ w : ℂ) : ℂ :=
  ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
    Φ (e τ ^ n * e w) (e τ)

/-- The normalized residue function
`x² ρ^{(k)}(τ) = ∑_{i ≥ 0} ω^{ki} q^{(m+1)i²} (ω^k q;q)_i / (q^d;q^d)_i` of [AOS, (7.13)],
as a function of `q`. -/
def eigenResidue (m k : ℕ) (q : ℂ) : ℂ :=
  ∑' i : ℕ, omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) *
    qPochhammer (omega m ^ k * q) q i / qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) i

/-- The exceptional set
`Ξ_m = ⋃_{k=1}^{d-1} {q : 0 < |q| < 1, ρ^{(k)} = 0}` of [AOS, Lemma 7.5]. -/
def exceptionalSet (m : ℕ) : Set ℂ :=
  {q | 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ ∃ k ∈ Icc 1 (2 * m), eigenResidue m k q = 0}

/-- The backward solution of [AOS, (7.14)] at `x = 1`, `γ = 1`: `Y_i = 1` for `i ≥ J`, and
`Y_i = d + q^{i+1} Y_{i+2} - ∑_{r=1}^{d-1} Y_{i+r}` for `i < J`, in `ℤ[q]`. -/
def backwardSequence (m J : ℕ) (i : ℕ) : Polynomial ℤ :=
  if J ≤ i then 1
  else (2 * m + 1 : Polynomial ℤ) + Polynomial.X ^ (i + 1) * backwardSequence m J (i + 2) -
    ∑ r ∈ (Ico 1 (2 * m + 1)).attach, backwardSequence m J (i + r)
termination_by J - i
decreasing_by
  all_goals first
    | omega
    | (have := (Finset.mem_Ico.mp r.2).1; omega)

/-- The backward polynomial `P_J = Y_0 ∈ ℤ[q]` of [AOS, Theorem 7.1(iii)]. -/
def backwardPolynomial (m J : ℕ) : Polynomial ℤ := backwardSequence m J 0

/-- The possible poles `{x^{-1} q^{-i}, ω^{-k} q^{-i} : i ≥ 0, 1 ≤ k ≤ d-1}` of the seed of a
solution of the recurrence [AOS, Theorem 7.1(ii)(a)]. -/
def seedPoleSet (m : ℕ) (x q : ℂ) : Set ℂ :=
  {u | ∃ i : ℕ, u = x⁻¹ * q ^ (-(i : ℤ))} ∪
    {u | ∃ i : ℕ, ∃ k ∈ Icc 1 (2 * m), u = (omega m ^ k)⁻¹ * q ^ (-(i : ℤ))}

/-- `Φ` is a meromorphic continuation of the seed `𝒢_Y` to `ℂ` with at most simple poles, all in
`seedPoleSet m x q`: `Φ` is holomorphic off that set, agrees with `𝒢_Y` on `|u| < 1`, and
`(u - s) Φ(u)` has a limit at each point `s` of the set. -/
def IsSeedContinuation (m : ℕ) (x q : ℂ) (Y : ℕ → ℂ) (Φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Φ (seedPoleSet m x q)ᶜ ∧ (∀ u : ℂ, ‖u‖ < 1 → Φ u = sequenceSeed x Y u) ∧
    ∀ s ∈ seedPoleSet m x q, ∃ L : ℂ,
      Filter.Tendsto (fun u => (u - s) * Φ u) (nhdsWithin s {s}ᶜ) (nhds L)

/-- Evaluation `z ↦ ζ` from `ℤ[z, z⁻¹]` to `ℂ` at a unit `ζ`. -/
def zEval (ζ : ℂˣ) : LaurentRing →+* ℂ := LaurentPolynomial.eval₂ (Int.castRingHom ℂ) ζ

/-- The orbits `𝒟_x ∪ ⋃_{k=1}^{d-1} 𝒟_{ω^k}` in `ℍ × ℂ`, `x = e(α)`, `d = 2m + 1`, where
`𝒟_{ω^k} = {w = -k/d + aτ + b}` [AOS, (7.8)]. -/
def solutionDivisor (m : ℕ) (α : ℚ) : Set (ℂ × ℂ) :=
  divisor α ∪ ⋃ k ∈ Icc 1 (2 * m), divisor ((k : ℚ) / (2 * m + 1))

end HigherDyson3

namespace HigherDyson3.Challenge

open Filter Topology
open scoped ENNReal NNReal ComplexOrder

/-! ## Higher Dyson ranks -/

/-- **`thm_combinatorial_gen_series` — the generating function of the full rank.** For `m ≥ 1`,
`[z^r] [q^N] R_m(z;q) = N_m(r, N)`. -/
theorem thm_combinatorial_gen_series (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (r : ℤ) :
    zCoeff r (qCoeff N (RSeries m)) = (rankCount m r N : ℤ) :=
  sorry

/-- **`thm_full_rank_symmetry` — symmetry of the full rank.** For `m ≥ 1`,
`N_m(r, N) = N_m(-r, N)`. -/
theorem thm_full_rank_symmetry (m : ℕ) (_hm : 1 ≤ m) (r : ℤ) (N : ℕ) :
    rankCount m r N = rankCount m (-r) N :=
  sorry

/-! ## The finite recurrence and the defect polynomial

Throughout, `m ≥ 2` and `d = 2m + 1`. -/

/-- **`thm_finite_recurrence` — the finite recurrence.** For `0 < ‖q‖ < 1` and `j ∈ ℤ`,
`∑_{r=0}^{d-1} x^r X_{j+r-2}(x;q) - q^{j-1} X_j(x;q) = C_x G_d(x;q)`. -/
theorem thm_finite_recurrence {m : ℕ} (hm : 2 ≤ m) (x : ℂ) {q : ℂ} (hq0 : q ≠ 0)
    (hq1 : ‖q‖ < 1) (j : ℤ) :
    ∑ r ∈ range (2 * m + 1), x ^ r * XSeries m x (j + r - 2) q - q ^ (j - 1) * XSeries m x j q =
      Cx m x * GProduct m x q :=
  sorry

/-- **`thm_finite_Cx_vanishes` — `C_x` vanishes at nontrivial `d`-th roots of unity.** -/
theorem thm_finite_Cx_vanishes {m : ℕ} (_hm : 2 ≤ m) {x : ℂ} (hx : x ≠ 1)
    (hxd : x ^ (2 * m + 1) = 1) : Cx m x = 0 :=
  sorry

/-- **`thm_finite_functional_equation` — the functional equation of the seed.** For `x ≠ 0`,
`0 < ‖q‖ < 1` and `u ≠ 0` with `x u q^k ≠ 1` for all `k`,
`𝒢_{d,x}(qu;q) = x² q (∑_{r<d} u^{2-r}) 𝒢_{d,x}(u;q) + q u^{3-d} R_{d,x}(u;q)
  - C_x q u²/(1 - xu) G_d(x;q)`. -/
theorem thm_finite_functional_equation {m : ℕ} (hm : 2 ≤ m) {x q u : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) (hu : u ≠ 0) (hxu : ∀ k : ℕ, x * u * q ^ k ≠ 1) :
    seed m x (q * u) q =
      x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
        q * u ^ (3 - (2 * m + 1 : ℤ)) * (defectPoly m x q).eval u -
        Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q :=
  sorry

/-- **`thm_finite_defect_unique` — uniqueness of the defect polynomial.** A polynomial `R'` of
degree at most `d - 2` satisfying the functional equation on a nonempty open set `V` of
admissible `u` is `R_{d,x}(U;q)`. -/
theorem thm_finite_defect_unique {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) {R' : Polynomial ℂ}
    (_hdeg : R'.degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ)) {V : Set ℂ} (hVo : IsOpen V)
    (hVne : V.Nonempty)
    (hV : ∀ u ∈ V, u ≠ 0 ∧ (∀ k : ℕ, x * u * q ^ k ≠ 1) ∧
      seed m x (q * u) q =
        x ^ 2 * q * (∑ r ∈ range (2 * m + 1), u ^ (2 - (r : ℤ))) * seed m x u q +
          q * u ^ (3 - (2 * m + 1 : ℤ)) * R'.eval u -
          Cx m x * q * (u ^ 2 / (1 - x * u)) * GProduct m x q) :
    R' = defectPoly m x q :=
  sorry

/-- **`thm_finite_defect_degree` — the degree of the defect polynomial.** `R_{d,x}(U;q)` has
degree at most `d - 2`. -/
theorem thm_finite_defect_degree {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (_hx : x ≠ 0)
    (_hq0 : 0 < ‖q‖) (_hq1 : ‖q‖ < 1) :
    (defectPoly m x q).degree ≤ ((2 * m + 1 - 2 : ℕ) : WithBot ℕ) :=
  sorry

/-- **`thm_finite_defect_constant_term` — the constant term of the defect polynomial.**
`[U^0] R_{d,x}(U;q) = -X₀(x;q)`. -/
theorem thm_finite_defect_constant_term {m : ℕ} (hm : 2 ≤ m) {x q : ℂ} (hx : x ≠ 0)
    (hq0 : 0 < ‖q‖) (hq1 : ‖q‖ < 1) :
    (defectPoly m x q).coeff 0 = -XSeries m x 0 q :=
  sorry

/-- **`thm_finite_defect_q_pole` — at most a simple pole at `q = 0`.** For `a ≤ d - 2`,
`q [U^a] R_{d,x}(U;q)` extends holomorphically to the open unit disk. -/
theorem thm_finite_defect_q_pole {m : ℕ} (hm : 2 ≤ m) {x : ℂ}
    (hx : x ≠ 0) {a : ℕ} (ha : a ≤ 2 * m + 1 - 2) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 1) ∧
      ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < 1 → h q = q * (defectPoly m x q).coeff a :=
  sorry

/-! ## The elliptic periodization

Throughout, `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, and `x = e(α)`. -/

/-- **`thm_elliptic_normal_convergence` — normal convergence of the periodization.** On every
compact `S ⊆ (ℍ × ℂ) \ 𝒟_x`, the series defining `ℰ_{m,x}` converges normally. -/
theorem thm_elliptic_normal_convergence {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (S : Set (ℂ × ℂ)) (hS : IsCompact S) (hSD : S ⊆ halfPlaneProd \ divisor α) :
    ∑' n : ℤ, ⨆ p ∈ S, (‖e α ^ (-2 * n) * e p.1 ^ ((m : ℤ) * n ^ 2) *
      e p.2 ^ (2 * (m : ℤ) * n) * seed m (e α) (e p.1 ^ n * e p.2) (e p.1)‖₊ : ℝ≥0∞) < ∞ :=
  sorry

/-- **`thm_elliptic_holomorphic_off` — holomorphy off the divisor.** `(ℍ × ℂ) \ 𝒟_x` is open
and `ℰ_{m,x}` is holomorphic on it. -/
theorem thm_elliptic_holomorphic_off {m : ℕ} (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    IsOpen (halfPlaneProd \ divisor α) ∧
      DifferentiableOn ℂ (fun p : ℂ × ℂ => periodization m α p.1 p.2)
        (halfPlaneProd \ divisor α) :=
  sorry

/-- **`thm_elliptic_twisted_law` — the twisted elliptic law.**
`ℰ_{m,x}(τ, w + aτ + b) = x^{2a} q^{-ma²} u^{-2ma} ℰ_{m,x}(τ, w)`, `q = e(τ)`, `u = e(w)`. -/
theorem thm_elliptic_twisted_law {m : ℕ} (_hm : 2 ≤ m) {α : ℚ} (_hα0 : 0 ≤ α)
    (_hα1 : α < 1) {τ w : ℂ} (_hτw : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    periodization m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        periodization m α τ w :=
  sorry

/-- **`thm_elliptic_rho_holomorphic` — holomorphy of `ρ_{m,x}`** on the upper half-plane. -/
theorem thm_elliptic_rho_holomorphic {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    DifferentiableOn ℂ (rho m α) upperHalfPlaneSet :=
  sorry

/-- **`thm_elliptic_rho_leading` — the leading term of `ρ_{m,x}`.**
`‖ρ_{m,x}(τ) - x⁻²‖ ≤ C ‖e(τ)‖` for `Im τ ≥ T`. -/
theorem thm_elliptic_rho_leading {m : ℕ} (hm : 2 ≤ m) (α : ℚ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ : ℂ, τ ∈ upperHalfPlaneSet → T ≤ τ.im →
      ‖rho m α τ - (e α ^ 2)⁻¹‖ ≤ C * ‖e τ‖ :=
  sorry

/-- **`thm_elliptic_simple_poles` — at most simple poles.** `(w + α - aτ - b) ℰ_{m,x}(τ, w)`
extends holomorphically to `Ω_{a,b}`. -/
theorem thm_elliptic_simple_poles (m : ℕ) (hm : 2 ≤ m) (α : ℚ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (a b : ℤ) :
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (divisorNbhd α a b) ∧
      ∀ p ∈ halfPlaneProd \ divisor α,
        N p = (p.2 + α - a * p.1 - b) * periodization m α p.1 p.2 :=
  sorry

/-- **`thm_elliptic_residue` — the residues.** With `w_{a,b} = -α + aτ + b`,
`ε ℰ_{m,x}(τ, w_{a,b} + ε) → -(ρ_{m,x}(τ)/2πi) x^{2(m+1)a} q^{-ma²}` as `ε → 0`. -/
theorem thm_elliptic_residue {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (a b : ℤ) :
    Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
      (𝓝 (-(rho m α τ / (2 * Real.pi * Complex.I)) * e α ^ (2 * ((m : ℤ) + 1) * a) *
        e τ ^ (-(m : ℤ) * a ^ 2))) :=
  sorry

/-- **`thm_elliptic_pole_genuine` — the poles are genuine where `ρ_{m,x}(τ) ≠ 0`.** -/
theorem thm_elliptic_pole_genuine {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : rho m α τ ≠ 0) (a b : ℤ) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun ε : ℂ => ε * periodization m α τ (-(α : ℂ) + a * τ + b + ε)) (𝓝[≠] 0)
        (𝓝 L) :=
  sorry

/-- **`thm_elliptic_pole_removable` — the poles are removable where `ρ_{m,x}(τ) = 0`.** -/
theorem thm_elliptic_pole_removable {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlaneSet) (hρ : rho m α τ = 0) (a b : ℤ) :
    ∃ L : ℂ, Tendsto (fun w => periodization m α τ w)
      (𝓝[≠] (-(α : ℂ) + a * τ + b)) (𝓝 L) :=
  sorry

/-- **`thm_elliptic_ne_zero` — the periodization is not identically zero** off `𝒟_x`. -/
theorem thm_elliptic_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ∃ p ∈ halfPlaneProd \ divisor α, periodization m α p.1 p.2 ≠ 0 :=
  sorry

/-- **`thm_elliptic_untwisted_law` — the untwisted elliptic law.**
`ℰ_{m,x}(τ, w + α/m + aτ + b) = q^{-ma²} u^{-2ma} ℰ_{m,x}(τ, w + α/m)`. -/
theorem thm_elliptic_untwisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w + (α : ℂ) / m) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    periodization m α τ (w + (α : ℂ) / m + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        periodization m α τ (w + (α : ℂ) / m) :=
  sorry

/-! ## The finite part and its theta decomposition

Throughout, `m ≥ 2`, `α ∈ ℚ` with `0 ≤ α < 1`, and `x = e(α)`. -/

/-- **`thm_theta_holomorphic` — the finite part is holomorphic.** `ℰ^{fin}_{m,x}` agrees off
`𝒟_x` with a function holomorphic on `ℍ × ℂ`. -/
theorem thm_theta_holomorphic {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ F : ℂ × ℂ → ℂ, DifferentiableOn ℂ F halfPlaneProd ∧
      ∀ p ∈ halfPlaneProd \ divisor α, F p = finitePart m α p.1 p.2 :=
  sorry

/-- **`thm_theta_twisted_law` — the twisted elliptic law of the finite part.** -/
theorem thm_theta_twisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    finitePart m α τ (w + a * τ + b) =
      e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ w :=
  sorry

/-- **`thm_theta_untwisted_law` — the untwisted elliptic law of the translated finite part.** -/
theorem thm_theta_untwisted_law {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {τ w : ℂ} (hτw : (τ, w + (α : ℂ) / m) ∈ halfPlaneProd \ divisor α) (a b : ℤ) :
    finitePart m α τ (w + (α : ℂ) / m + a * τ + b) =
      e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
        finitePart m α τ (w + (α : ℂ) / m) :=
  sorry

/-- **`thm_theta_expansion` — the theta expansion.**
`ℰ^{fin}_{m,x}(τ, w + α/m) = ∑_{ℓ=0}^{2m-1} h_{m,ℓ,x}(τ) ϑ_{m,ℓ}(τ, w)` off `𝒟_x`. -/
theorem thm_theta_expansion {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {τ w : ℂ} (hτ : τ ∈ upperHalfPlaneSet)
    (hw : (τ, w + (α : ℂ) / m) ∉ divisor α) :
    finitePart m α τ (w + (α : ℂ) / m) =
      ∑ ℓ ∈ range (2 * m), thetaCoeffH m ℓ α τ * theta m ℓ τ w :=
  sorry

/-- **`thm_theta_unique` — uniqueness of the theta coefficients.** Any coefficients `h'_ℓ`
giving the theta expansion are the `h_{m,ℓ,x}`. -/
theorem thm_theta_unique {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h' : ℕ → ℂ → ℂ)
    (hh' : ∀ τ ∈ upperHalfPlaneSet, ∀ w : ℂ, (τ, w + (α : ℂ) / m) ∉ divisor α →
      finitePart m α τ (w + (α : ℂ) / m) = ∑ ℓ ∈ range (2 * m), h' ℓ τ * theta m ℓ τ w) :
    ∀ ℓ < 2 * m, ∀ τ ∈ upperHalfPlaneSet, h' ℓ τ = thetaCoeffH m ℓ α τ :=
  sorry

/-- **`thm_theta_coeff_normal` — normal convergence of the series of `h_{m,ℓ,x}`** on every
compact `S ⊆ ℍ`, for `0 ≤ ℓ < 2m`. -/
theorem thm_theta_coeff_normal {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {ℓ : ℕ} (hℓ : ℓ < 2 * m) (S : Set ℂ) (hS : IsCompact S) (hSH : S ⊆ upperHalfPlaneSet) :
    ∑' k : ℕ, ⨆ τ ∈ S, (‖e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) *
      e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
      (gTail m (e α) k (e τ) *
        ∑ s ∈ Finset.Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
          e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s))‖₊ : ℝ≥0∞) < ∞ :=
  sorry

/-- **`thm_theta_coeff_holomorphic` — holomorphy of `h_{m,ℓ,x}`** on the upper half-plane,
for `0 ≤ ℓ < 2m`. -/
theorem thm_theta_coeff_holomorphic {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    DifferentiableOn ℂ (thetaCoeffH m ℓ α) upperHalfPlaneSet :=
  sorry

/-- **`thm_theta_leading` — the leading term of `h_{m,ℓ,x}`.** With `c_ℓ = 1 + ℓ - ℓ²/(4m)`,
`|h_{m,ℓ,x}(τ) - e(ℓα/m) x^{ℓ-2} e(c_ℓ τ)| ≤ C |e((c_ℓ + 2)τ)|` for `Im τ ≥ T`. -/
theorem thm_theta_leading {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ τ ∈ upperHalfPlaneSet, T ≤ τ.im →
      ‖thetaCoeffH m ℓ α τ -
          e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) * e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m)) * τ)‖ ≤
        C * ‖e ((1 + ℓ - (ℓ : ℂ) ^ 2 / (4 * m) + 2) * τ)‖ :=
  sorry

/-- **`thm_theta_coeff_ne_zero` — no theta coefficient vanishes identically** on `ℍ`. -/
theorem thm_theta_coeff_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {ℓ : ℕ} (hℓ : ℓ < 2 * m) :
    ∃ τ ∈ upperHalfPlaneSet, thetaCoeffH m ℓ α τ ≠ 0 :=
  sorry

/-- **`thm_theta_finite_ne_zero` — the finite part is not identically zero** off `𝒟_x`. -/
theorem thm_theta_finite_ne_zero {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    ∃ p ∈ halfPlaneProd \ divisor α, finitePart m α p.1 p.2 ≠ 0 :=
  sorry

/-- **`thm_theta_positive` — positivity at `x = 1`.** For `0 ≤ ℓ < 2m` and real `t > 0`,
`h_{m,ℓ,1}(it)` is a positive real number. -/
theorem thm_theta_positive {m : ℕ} (hm : 2 ≤ m) {ℓ : ℕ} (hℓ : ℓ < 2 * m) {t : ℝ}
    (ht : 0 < t) :
    0 < thetaCoeffH m ℓ 0 (I * t) :=
  sorry

/-! ## The recurrence characterizes the Dyson seed -/

section RecurrenceCharacterization

open PowerSeries

/-- **The recurrence characterizes the Dyson seed** [AOS, Theorem 1.4, Theorem 7.1]. -/
theorem recurrence_characterization {m : ℕ} (hm : 2 ≤ m) {α : ℚ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    -- (i) the unique solution tending to `1`
    (∀ τ : ℂ, 0 < τ.im →
      ((fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) ∈
          recurrenceFamily m (e α) (e τ) 1 ∧
        Tendsto (fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) atTop (𝓝 1)) ∧
      ∀ (γ : ℂ) (Y : ℕ → ℂ), Y ∈ recurrenceFamily m (e α) (e τ) γ → Tendsto Y atTop (𝓝 1) →
        Y = (fun j : ℕ => XSeries m (e α) j (e τ) / GProduct m (e α) (e τ)) ∧
          (Cx m (e α) ≠ 0 → γ = 1)) ∧
    -- (ii) the seed: convergence and meromorphic continuation
    (∀ τ : ℂ, 0 < τ.im → ∀ Y ∈ recurrenceSolutions m (e α) (e τ),
      (∀ u : ℂ, ‖u‖ < 1 → Summable fun j : ℕ => Y j * (e α * u) ^ j) ∧
        ∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ) ∧
    -- (ii) the periodization: convergence off the orbits, at most simple poles, twisted law
    (∀ τ ∈ upperHalfPlaneSet, ∀ Y ∈ recurrenceSolutions m (e α) (e τ), ∀ Φ : ℂ → ℂ,
      IsSeedContinuation m (e α) (e τ) Y Φ →
      (∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, (τ, w) ∉ solutionDivisor m α) →
        ∑' n : ℤ, ⨆ w ∈ K, (‖e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) *
          e w ^ (2 * (m : ℤ) * n) * Φ (e τ ^ n * e w)‖₊ : ℝ≥0∞) < ∞) ∧
      (IsOpen {w : ℂ | (τ, w) ∉ solutionDivisor m α} ∧
        DifferentiableOn ℂ (fun w => seedPeriodization m α (fun u _ => Φ u) τ w)
          {w : ℂ | (τ, w) ∉ solutionDivisor m α}) ∧
      (∀ w₀ : ℂ, ∃ N : ℂ → ℂ, AnalyticAt ℂ N w₀ ∧ ∀ᶠ w in 𝓝[≠] w₀,
        N w = (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w) ∧
      ∀ (w : ℂ) (a k : ℤ), seedPeriodization m α (fun u _ => Φ u) τ (w + a * τ + k) =
        e α ^ (2 * a) * e τ ^ (-(m : ℤ) * a ^ 2) * e w ^ (-2 * (m : ℤ) * a) *
          seedPeriodization m α (fun u _ => Φ u) τ w) ∧
    -- (ii) the exceptional set: discrete, depending only on `m`, disjoint from `0 < |q| ≤ 1/2`
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → ∀ᶠ y in 𝓝[≠] z, y ∉ exceptionalSet m) ∧
    (∀ q : ℂ, 0 < ‖q‖ → ‖q‖ ≤ 1 / 2 → q ∉ exceptionalSet m) ∧
    -- (ii) the location of the poles
    (∀ τ ∈ upperHalfPlaneSet, e τ ∉ exceptionalSet m →
      (∀ Y : ℕ → ℂ, Y ∈ recurrenceSolutions m (e α) (e τ) → ∀ Φ : ℂ → ℂ,
        IsSeedContinuation m (e α) (e τ) Y Φ →
        ((∀ w₀ : ℂ, (τ, w₀) ∉ divisor α → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
          ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w) ↔
          ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ))) ∧
      ∀ k ∈ Icc 1 (2 * m), omega m ^ k ≠ e α →
        ∃ Y : ℕ → ℂ, Y ∈ recurrenceFamily m (e α) (e τ) 0 ∧
          (¬ ∃ c : ℂ, Y = c • fun j : ℕ => XSeries m (e α) j (e τ)) ∧
          (∃ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ) ∧
          ∀ Φ : ℂ → ℂ, IsSeedContinuation m (e α) (e τ) Y Φ → ∀ w₀ : ℂ,
            ((τ, w₀) ∈ divisor ((k : ℚ) / (2 * m + 1)) → ∃ L : ℂ, L ≠ 0 ∧
              Tendsto (fun w => (w - w₀) * seedPeriodization m α (fun u _ => Φ u) τ w)
                (𝓝[≠] w₀) (𝓝 L)) ∧
            ((τ, w₀) ∉ divisor ((k : ℚ) / (2 * m + 1)) → ∃ F : ℂ → ℂ, AnalyticAt ℂ F w₀ ∧
              ∀ᶠ w in 𝓝[≠] w₀, seedPeriodization m α (fun u _ => Φ u) τ w = F w)) ∧
    -- (iii) the backward polynomials at `x = 1`
    ∀ (ζ : ℂˣ), IsPrimitiveRoot (ζ : ℂ) (2 * m + 1) → ∀ J : ℕ,
      (X ^ (J + 1) ∣ map (zEval ζ) (RSeries m) -
        map (Int.castRingHom ℂ) (backwardPolynomial m J : PowerSeries ℤ)) ∧
      ∀ N ≤ J, ((backwardPolynomial m J).coeff N : ℂ) = coeff N (map (zEval ζ) (RSeries m)) :=
  sorry

end RecurrenceCharacterization

end HigherDyson3.Challenge
