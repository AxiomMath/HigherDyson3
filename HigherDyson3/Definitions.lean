/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-!
# Definitions for higher Dyson ranks and their elliptic periodization

The objects of Alfes–Ono–Swaminathan, *Beyond mock modularity: elliptic corrections for
higher Dyson ranks*: uncoupled Dyson symbols, their full rank and the generating series
`R_m(z;q)`; the product `G_d`, its tails `g_{k,x}`, the seed `𝒢_{d,x}`, the values `X_j`
and the defect polynomial `R_{d,x}`; the divisor `𝒟_x`, the theta series, the kernel
`𝒦_{m,x}`; and the periodization `ℰ_{m,x}`, its coefficients `ρ_{m,x}`, `C_{m,ℓ,x}`,
its finite part and the theta coefficients `h_{m,ℓ,x}`; and, for the characterization of the
seed [AOS, §7], the solution family `V_γ` of the finite recurrence, the seed `𝒢_Y` of a sequence
and its meromorphic continuations, the periodization `ℰ_Φ` of a seed, the residue functions
`ρ^{(k)}`, the exceptional set `Ξ_m`, the backward polynomials `P_J` and the pole orbits.

Infinite sums and products are Mathlib's unconditional `tsum` / `tprod`; where the paper
works off a divisor or under a convergence hypothesis, the definition is total and the
hypothesis moves to the statements about it. Integer powers of `q = e(τ)`, `u = e(w)` and
`x = e(α)` are `zpow`, these numbers being nonzero.
-/

public section

noncomputable section

open Complex Finset

namespace HigherDyson3

/-! ## Conventions -/

/-- The normalized exponential `e(z) = exp(2πiz)`. -/
@[expose]
def e (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

/-- The upper half-plane `ℍ = {τ : 0 < Im τ}`, as a subset of `ℂ`. -/
@[expose]
def upperHalfPlaneSet : Set ℂ := {τ | 0 < τ.im}

/-- The domain `ℍ × ℂ` of the elliptic objects, as a subset of `ℂ × ℂ`. -/
@[expose]
def halfPlaneProd : Set (ℂ × ℂ) := {p | 0 < p.1.im}

/-! ## Dyson symbols and their generating function -/

/-- A partition: a finite multiset of positive integers, its parts. -/
abbrev Partition : Type := Multiset ℕ+

namespace Partition

/-- The size `|λ|` of a partition: the sum of its parts, with multiplicity. -/
@[expose]
def size (p : Partition) : ℕ := (p.map ((↑) : ℕ+ → ℕ)).sum

/-- The length `ℓ(λ)` of a partition: the number of its parts, with multiplicity. -/
@[expose]
def length (p : Partition) : ℕ := Multiset.card p

end Partition

/-- `𝒫_{≤n}`: the partitions all of whose parts are at most `n`. -/
@[expose]
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
@[expose]
def size (s : DysonSymbol m) : ℕ := s.n ^ 2 + ∑ j, ((s.α j).size + (s.β j).size)

/-- The full rank `FR_m(Σ) = ∑_{j=1}^m j (ℓ(α_j) - ℓ(β_j))`. -/
@[expose]
def fullRank (s : DysonSymbol m) : ℤ :=
  ∑ j : Fin m, ((j : ℤ) + 1) * (((s.α j).length : ℤ) - (s.β j).length)

end DysonSymbol

/-- `N_m(r, N)`: the number of `m`-Dyson symbols of size `N` and full rank `r`
(`0` if there are infinitely many). -/
@[expose]
def rankCount (m : ℕ) (r : ℤ) (N : ℕ) : ℕ :=
  Nat.card {s : DysonSymbol m // s.size = N ∧ s.fullRank = r}

/-- The coefficient ring `𝒜 = ℤ[z, z⁻¹]`; the series ring is `PowerSeries LaurentRing`. -/
abbrev LaurentRing : Type := LaurentPolynomial ℤ

/-- The coefficient `[q^N] f` of a series `f ∈ 𝒜[[q]]`. -/
@[expose]
def qCoeff (N : ℕ) (f : PowerSeries LaurentRing) : LaurentRing := PowerSeries.coeff N f

/-- The coefficient `[z^r] P` of a Laurent polynomial `P ∈ 𝒜`. -/
@[expose]
def zCoeff (r : ℤ) (P : LaurentRing) : ℤ := P.coeff r

/-- The formal inverse `f⁻¹` of a series with constant term `1`:
`b₀ = 1`, `b_N = -∑_{k=1}^N ([q^k] f) b_{N-k}`. -/
@[expose]
def seriesInv (f : PowerSeries LaurentRing) : PowerSeries LaurentRing :=
  PowerSeries.invOfUnit f 1

/-- The `q`-Pochhammer symbol `(cq; q)_n = ∏_{r=1}^n (1 - c q^r)`. -/
@[expose]
def qPoch (c : LaurentRing) (n : ℕ) : PowerSeries LaurentRing :=
  ∏ r ∈ Icc 1 n, (1 - PowerSeries.C c * PowerSeries.X ^ r)

/-- The `n`-th term `𝒯_{m,n} = q^{n²} (∏_{j=1}^m (z^j q;q)_n (z^{-j} q;q)_n)⁻¹`. -/
@[expose]
def RTerm (m n : ℕ) : PowerSeries LaurentRing :=
  PowerSeries.X ^ (n ^ 2) *
    seriesInv (∏ j ∈ Icc 1 m,
      qPoch (LaurentPolynomial.T (j : ℤ)) n * qPoch (LaurentPolynomial.T (-(j : ℤ))) n)

/-- The higher rank series `R_m(z;q)`, coefficientwise `[q^N] R_m = ∑_n [q^N] 𝒯_{m,n}`
(a finitely supported sum, `0` if infinitely many summands are nonzero). -/
@[expose]
def RSeries (m : ℕ) : PowerSeries LaurentRing :=
  PowerSeries.mk fun N => ∑ᶠ n : ℕ, PowerSeries.coeff N (RTerm m n)

/-- The partition series `Φ_{c,n}`, `[q^N] Φ_{c,n} = ∑ c^{ℓ(λ)}` over the partitions `λ`
of `N` with all parts at most `n`. -/
@[expose]
def partitionSeries (c : LaurentRing) (n : ℕ) : PowerSeries LaurentRing :=
  PowerSeries.mk fun N =>
    ∑ᶠ (p : Partition) (_ : p ∈ boundedPartitions n ∧ p.size = N), c ^ p.length

/-! ## The higher Dyson deformation: product, tails, seed, values and defect -/

/-- The cyclotomic sum `P_d(z) = ∑_{s=0}^{d-1} z^s`, `d = 2m + 1`. -/
@[expose]
def cyclotomicSum (m : ℕ) (z : ℂ) : ℂ := ∑ s ∈ range (2 * m + 1), z ^ s

/-- The product `G_d(y;q) = ∏_{r ≥ 1} P_d(y q^r)`. -/
@[expose]
def GProduct (m : ℕ) (y q : ℂ) : ℂ := ∏' r : ℕ, cyclotomicSum m (y * q ^ (r + 1))

/-- The tails `g_{k,x}(q) = G_d(x q^k; q)`. -/
@[expose]
def gTail (m : ℕ) (x : ℂ) (k : ℕ) (q : ℂ) : ℂ := GProduct m (x * q ^ k) q

/-- The seed `𝒢_{d,x}(u;q) = x⁻² ∑_{k ≥ 0} q^{k²} g_{k,x}(q) / (1 - x u q^k)`. -/
@[expose]
def seed (m : ℕ) (x u q : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * ∑' k : ℕ, q ^ (k ^ 2) * gTail m x k q / (1 - x * u * q ^ k)

/-- The values `X_j^{(m)}(x;q) = ∑_{k ≥ 0} q^{k² + jk} g_{k,x}(q)`, `j ∈ ℤ`. -/
@[expose]
def XSeries (m : ℕ) (x : ℂ) (j : ℤ) (q : ℂ) : ℂ :=
  ∑' k : ℕ, q ^ ((k : ℤ) ^ 2 + j * k) * gTail m x k q

/-- The constant `C_x = P_d(x)`. -/
@[expose]
def Cx (m : ℕ) (x : ℂ) : ℂ := cyclotomicSum m x

/-- The defect polynomial
`R_{d,x}(U;q) = q⁻¹x⁻²X₀ U^{d-3} + x⁻¹X₁ U^{d-2} - ∑_{k=0}^{d-2} x^k X_k ∑_{a=k}^{d-2} U^a`. -/
@[expose]
def defectPoly (m : ℕ) (x q : ℂ) : Polynomial ℂ :=
  Polynomial.C (q⁻¹ * (x ^ 2)⁻¹ * XSeries m x 0 q) * Polynomial.X ^ (2 * m + 1 - 3) +
    Polynomial.C (x⁻¹ * XSeries m x 1 q) * Polynomial.X ^ (2 * m + 1 - 2) -
    ∑ k ∈ range (2 * m + 1 - 1), Polynomial.C (x ^ k * XSeries m x k q) *
      ∑ a ∈ Icc k (2 * m + 1 - 2), Polynomial.X ^ a

/-- The raw defect
`ℬ_{d,x}(u;q) = x⁻²(X_{-2} - G_d(x;q)) + x⁻¹(1+u)(X_{-1} - G_d(x;q))
  - ∑_{r=3}^{d-1} ∑_{i=0}^{r-3} x^i u^{i+2-r} (X_i - G_d(x;q))`. -/
@[expose]
def rawDefect (m : ℕ) (x u q : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * (XSeries m x (-2) q - GProduct m x q) +
    x⁻¹ * (1 + u) * (XSeries m x (-1) q - GProduct m x q) -
    ∑ r ∈ Icc 3 (2 * m + 1 - 1), ∑ i ∈ range (r - 2),
      x ^ i * u ^ ((i : ℤ) + 2 - r) * (XSeries m x i q - GProduct m x q)

/-! ## Elliptic toolkit: divisor, theta series, kernel -/

/-- The divisor component `L_{a,b} = {(τ, w) ∈ ℍ × ℂ : w = -α + aτ + b}`. -/
@[expose]
def divisorComponent (α : ℚ) (a b : ℤ) : Set (ℂ × ℂ) :=
  {p | 0 < p.1.im ∧ p.2 = -(α : ℂ) + a * p.1 + b}

/-- The divisor `𝒟_x = ⋃_{(a,b) ∈ ℤ²} L_{a,b} ⊆ ℍ × ℂ`, `x = e(α)`. -/
@[expose]
def divisor (α : ℚ) : Set (ℂ × ℂ) := ⋃ (a : ℤ) (b : ℤ), divisorComponent α a b

/-- The neighbourhood `Ω_{a,b} = (ℍ × ℂ) \ ⋃_{(a',b') ≠ (a,b)} L_{a',b'}` of one component. -/
@[expose]
def divisorNbhd (α : ℚ) (a b : ℤ) : Set (ℂ × ℂ) :=
  halfPlaneProd \ ⋃ (c : ℤ × ℤ) (_ : c ≠ (a, b)), divisorComponent α c.1 c.2

/-- The theta series `ϑ_{m,ℓ}(τ,w) = ∑_{j ∈ ℤ} e((ℓ+2mj)²τ/(4m)) e((ℓ+2mj)w)`. -/
@[expose]
def theta (m ℓ : ℕ) (τ w : ℂ) : ℂ :=
  ∑' j : ℤ, e (((ℓ : ℂ) + 2 * m * j) ^ 2 * τ / (4 * m)) * e (((ℓ : ℂ) + 2 * m * j) * w)

/-- The twisted theta series `T^{[x]}_{m,ℓ}(τ,w) = ∑_{j ∈ ℤ} x^{-2j} q^{mj²+ℓj} u^{ℓ+2mj}`,
`x = e(α)`, `q = e(τ)`, `u = e(w)`. -/
@[expose]
def twistedTheta (m ℓ : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  ∑' j : ℤ, e α ^ (-2 * j) * e τ ^ ((m : ℤ) * j ^ 2 + ℓ * j) * e w ^ ((ℓ : ℤ) + 2 * m * j)

/-- The kernel `𝒦_{m,x}(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} / (1 - x u q^n)`. -/
@[expose]
def kernel (m : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) /
    (1 - e α * e w * e τ ^ n)

/-- The regular part `𝒦^{(a)}_{m,x}` of the kernel: the kernel's series without the
summand `n = -a`. -/
@[expose]
def kernelRegular (m : ℕ) (α : ℚ) (a : ℤ) (τ w : ℂ) : ℂ :=
  ∑' n : {n : ℤ // n ≠ -a}, e α ^ (-2 * (n : ℤ)) * e τ ^ ((m : ℤ) * (n : ℤ) ^ 2) *
    e w ^ (2 * (m : ℤ) * n) / (1 - e α * e w * e τ ^ (n : ℤ))

/-- The quotient `Φ(z) = z / (1 - e(z))`, extended by `Φ(0) = -1/(2πi)`. -/
@[expose]
def expQuotient (z : ℂ) : ℂ :=
  if z = 0 then -1 / (2 * Real.pi * Complex.I) else z / (1 - e z)

/-! ## The periodization and its layers -/

/-- The periodization `ℰ_{m,x}(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} 𝒢_{d,x}(q^n u; q)`. -/
@[expose]
def periodization (m : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
    seed m (e α) (e τ ^ n * e w) (e τ)

/-- The double summand
`ℰ^{dbl}_{n,k}(τ,w) = x⁻² x^{-2n} q^{mn²+k²} u^{2mn} g_{k,x}(q) / (1 - x u q^{n+k})`. -/
@[expose]
def doubleSummand (m : ℕ) (α : ℚ) (n : ℤ) (k : ℕ) (τ w : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2 + (k : ℤ) ^ 2) *
    e w ^ (2 * (m : ℤ) * n) * gTail m (e α) k (e τ) / (1 - e α * e w * e τ ^ (n + k))

/-- The residue coefficient `ρ_{m,x}(τ) = x⁻² ∑_{k ≥ 0} x^{2(m+1)k} q^{(m+1)k²} g_{k,x}(q)`. -/
@[expose]
def rho (m : ℕ) (α : ℚ) (τ : ℂ) : ℂ :=
  (e α ^ 2)⁻¹ * ∑' k : ℕ, e α ^ (2 * (m + 1) * k) * e τ ^ ((m + 1) * k ^ 2) *
    gTail m (e α) k (e τ)

/-- The theta coefficients
`C_{m,ℓ,x}(τ) = x^{ℓ-2} ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}`
(the summand `k = 0` is an empty sum). -/
@[expose]
def coeffC (m ℓ : ℕ) (α : ℚ) (τ : ℂ) : ℂ :=
  e α ^ ((ℓ : ℤ) - 2) * ∑' k : ℕ, gTail m (e α) k (e τ) *
    ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
      e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)

/-! ## The finite part and the theta coefficients -/

/-- The finite part `ℰ^{fin}_{m,x} = ℰ_{m,x} - ρ_{m,x} 𝒦_{m,x}`. -/
@[expose]
def finitePart (m : ℕ) (α : ℚ) (τ w : ℂ) : ℂ :=
  periodization m α τ w - rho m α τ * kernel m α τ w

/-- The theta coefficients `h_{m,ℓ,x}(τ) = e(ℓα/m) x^{ℓ-2} q^{-ℓ²/(4m)}
  ∑_{k ≥ 1} g_{k,x}(q) ∑_{s=1}^k x^{2(m+1)(k-s)} q^{(m+1)k²-ms²+ℓs}`,
with `q^{-ℓ²/(4m)} = e(-ℓ²τ/(4m))`. -/
@[expose]
def thetaCoeffH (m ℓ : ℕ) (α : ℚ) (τ : ℂ) : ℂ :=
  e (ℓ * α / m) * e α ^ ((ℓ : ℤ) - 2) * e (-((ℓ : ℂ) ^ 2) * τ / (4 * m)) *
    ∑' k : ℕ, gTail m (e α) k (e τ) *
      ∑ s ∈ Icc 1 k, e α ^ (2 * ((m : ℤ) + 1) * ((k : ℤ) - s)) *
        e τ ^ (((m : ℤ) + 1) * (k : ℤ) ^ 2 - m * (s : ℤ) ^ 2 + ℓ * s)

/-! ## The characterization of the Dyson seed -/

/-- The finite `q`-Pochhammer symbol `(a;q)_n = ∏_{l=0}^{n-1} (1 - a q^l)`, over `ℂ`. -/
@[expose]
def qPochhammer (a q : ℂ) (n : ℕ) : ℂ := ∏ l ∈ range n, (1 - a * q ^ l)

/-- The solution family `V_γ` of [AOS, (7.4)]: sequences `(Y_j)_{j ≥ 0}` with
`∑_{r=0}^{d-1} x^r Y_{j+r-2} - q^{j-1} Y_j = C_x γ` for all `j ≥ 2`. -/
@[expose]
def recurrenceFamily (m : ℕ) (x q γ : ℂ) : Set (ℕ → ℂ) :=
  {Y | ∀ j : ℕ, 2 ≤ j →
    ∑ r ∈ range (2 * m + 1), x ^ r * Y (j + r - 2) - q ^ (j - 1) * Y j = Cx m x * γ}

/-- The family `V = ⋃_γ V_γ` of [AOS, §7]. -/
@[expose]
def recurrenceSolutions (m : ℕ) (x q : ℂ) : Set (ℕ → ℂ) :=
  ⋃ γ : ℂ, recurrenceFamily m x q γ

/-- The primitive `d`-th root of unity `ω = e(1/d)`, `d = 2m + 1`. -/
@[expose]
def omega (m : ℕ) : ℂ := e (1 / (2 * m + 1 : ℂ))

/-- The seed `𝒢_Y(u) = x^{-2} ∑_{j ≥ 0} Y_j (xu)^j` of a sequence `Y` [AOS, (7.7)]. -/
@[expose]
def sequenceSeed (x : ℂ) (Y : ℕ → ℂ) (u : ℂ) : ℂ :=
  (x ^ 2)⁻¹ * ∑' j : ℕ, Y j * (x * u) ^ j

/-- The bilateral periodization `ℰ_Φ(τ,w) = ∑_{n ∈ ℤ} x^{-2n} q^{mn²} u^{2mn} Φ(q^n u; q)`
of a seed `Φ(u; q)` [AOS, (7.7), (7.10)], with `x = e(α)`, `q = e(τ)`, `u = e(w)`. -/
@[expose]
def seedPeriodization (m : ℕ) (α : ℚ) (Φ : ℂ → ℂ → ℂ) (τ w : ℂ) : ℂ :=
  ∑' n : ℤ, e α ^ (-2 * n) * e τ ^ ((m : ℤ) * n ^ 2) * e w ^ (2 * (m : ℤ) * n) *
    Φ (e τ ^ n * e w) (e τ)

/-- The normalized residue function
`x² ρ^{(k)}(τ) = ∑_{i ≥ 0} ω^{ki} q^{(m+1)i²} (ω^k q;q)_i / (q^d;q^d)_i` of [AOS, (7.13)],
as a function of `q`. -/
@[expose]
def eigenResidue (m k : ℕ) (q : ℂ) : ℂ :=
  ∑' i : ℕ, omega m ^ (k * i) * q ^ ((m + 1) * i ^ 2) *
    qPochhammer (omega m ^ k * q) q i / qPochhammer (q ^ (2 * m + 1)) (q ^ (2 * m + 1)) i

/-- The exceptional set
`Ξ_m = ⋃_{k=1}^{d-1} {q : 0 < |q| < 1, ρ^{(k)} = 0}` of [AOS, Lemma 7.5]. -/
@[expose]
def exceptionalSet (m : ℕ) : Set ℂ :=
  {q | 0 < ‖q‖ ∧ ‖q‖ < 1 ∧ ∃ k ∈ Icc 1 (2 * m), eigenResidue m k q = 0}

/-- The backward solution of [AOS, (7.14)] at `x = 1`, `γ = 1`: `Y_i = 1` for `i ≥ J`, and
`Y_i = d + q^{i+1} Y_{i+2} - ∑_{r=1}^{d-1} Y_{i+r}` for `i < J`, in `ℤ[q]`. -/
@[expose]
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
@[expose]
def backwardPolynomial (m J : ℕ) : Polynomial ℤ := backwardSequence m J 0

/-- The possible poles `{x^{-1} q^{-i}, ω^{-k} q^{-i} : i ≥ 0, 1 ≤ k ≤ d-1}` of the seed of a
solution of the recurrence [AOS, Theorem 7.1(ii)(a)]. -/
@[expose]
def seedPoleSet (m : ℕ) (x q : ℂ) : Set ℂ :=
  {u | ∃ i : ℕ, u = x⁻¹ * q ^ (-(i : ℤ))} ∪
    {u | ∃ i : ℕ, ∃ k ∈ Icc 1 (2 * m), u = (omega m ^ k)⁻¹ * q ^ (-(i : ℤ))}

/-- `Φ` is a meromorphic continuation of the seed `𝒢_Y` to `ℂ` with at most simple poles, all in
`seedPoleSet m x q`: `Φ` is holomorphic off that set, agrees with `𝒢_Y` on `|u| < 1`, and
`(u - s) Φ(u)` has a limit at each point `s` of the set. -/
@[expose]
def IsSeedContinuation (m : ℕ) (x q : ℂ) (Y : ℕ → ℂ) (Φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Φ (seedPoleSet m x q)ᶜ ∧ (∀ u : ℂ, ‖u‖ < 1 → Φ u = sequenceSeed x Y u) ∧
    ∀ s ∈ seedPoleSet m x q, ∃ L : ℂ,
      Filter.Tendsto (fun u => (u - s) * Φ u) (nhdsWithin s {s}ᶜ) (nhds L)

/-- Evaluation `z ↦ ζ` from `ℤ[z, z⁻¹]` to `ℂ` at a unit `ζ`. -/
@[expose]
def zEval (ζ : ℂˣ) : LaurentRing →+* ℂ := LaurentPolynomial.eval₂ (Int.castRingHom ℂ) ζ

/-- The orbits `𝒟_x ∪ ⋃_{k=1}^{d-1} 𝒟_{ω^k}` in `ℍ × ℂ`, `x = e(α)`, `d = 2m + 1`, where
`𝒟_{ω^k} = {w = -k/d + aτ + b}` [AOS, (7.8)]. -/
@[expose]
def solutionDivisor (m : ℕ) (α : ℚ) : Set (ℂ × ℂ) :=
  divisor α ∪ ⋃ k ∈ Icc 1 (2 * m), divisor ((k : ℚ) / (2 * m + 1))

end HigherDyson3
