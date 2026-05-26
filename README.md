# Hilbert Polynomials of Graded Modules

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

In this repository, we have formalised the Hilbert polynomial of a graded module based on the Hilbert--Serre Theorem.

## Build Instructions

1. Ensure that `git` is installed. If it is not already installed, see: https://git-scm.com/downloads
2. Install Lean 4 via `elan`: https://lean-lang.org/install/
3. Clone the repository:
```
git clone https://github.com/FMLJohn/HilbertPolynomial.git
cd HilbertPolynomial
```
4. Fetch the Mathlib build cache:
```
lake exe cache get
```
5. Build the project
```
lake build HilbertPolynomial
```

## How to Use the Blueprint

The blueprint provides a structured roadmap of the formalization project, outlining the main definitions, theorems, dependencies, and overall proof architecture in Lean.
- [Blueprint (web)](https://FMLJohn.github.io/HilbertPolynomial/blueprint/)
- [Blueprint (PDF)](https://FMLJohn.github.io/HilbertPolynomial/blueprint.pdf)
- [Dependency graph](https://FMLJohn.github.io/HilbertPolynomial/blueprint/dep_graph_document.html)
- [API documentation](https://FMLJohn.github.io/HilbertPolynomial/docs/)

## Preliminary Definitions

1. `AdditiveFunction 𝒞 G`. Given an abelian category `𝒞` and an additive commutative group `G`, a function `λ` from the class of all objects of
`𝒞` to `G` is additive if `λ B = λ A + λ C` for every short exact sequence `0 --> A --> B --> C --> 0` in `𝒞`. `AdditiveFunction 𝒞 G` is the type of all additive functions from `𝒞` to `G`; we denote it as `𝒞 ⟹+ G`.
2. `generatingSetOverBaseRing 𝒜`. Given a commutative ring `A` and a function `𝒜 : ℕ → AddSubgroup A` with `GradedRing 𝒜`, if `S : generatingSetOverBaseRing 𝒜`, then `S` is a finite collection of homogeneous elements of `A` that generates `A` over `𝒜 0`.

From this point onward in this page, unless stated otherwise, we assume the following:
```
universe u
variable {A M : Type u}
variable [CommRing A] [noetherian_ring : IsNoetherianRing A]
variable [AddCommGroup M] [Module A M] [finite_module : Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
variable (S : generatingSetOverBaseRing 𝒜)
```

3. `S.poles`. The polynomial `∏ i ∈ S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)`, which has an inverse in `ℤ⟦X⟧ˣ`.
4. `μ.poincareSeries 𝒜 ℳ`. The Poincaré series of the graded module `M` with respect to `μ`, which is the power series
`∑ᵢ μ(Mᵢ) Xⁱ ∈ ℤ⟦X⟧`.

## Main Results and Definitions

1. `hilbert_serre 𝒜 ℳ μ S`. There exists a polynomial `p : Polynomial ℤ` such that `μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹`.
2. `HilbertSerre.numeratorPolynomial ℳ μ S`. The polynomial `(hilbert_serre 𝒜 ℳ μ S).choose`.
3. `HilbertSerre.hilbertPolynomial ℳ μ S`. The Hilbert polynomial of `M` with respect to `μ`, which is defined as `((numeratorPolynomial ℳ μ S).map (Int.castRingHom ℚ)).hilbertPoly S.toFinset.card`.

From now on, assume that `hS : (i : S.toFinset) → S.deg i.2 = 1`.

4. `HilbertSerre.AdditiveFunction_eq_hilbertPolynomial_eval ℳ μ hS hn`. The key property of the Hilbert polynomial, i.e. for any `n : ℕ` that is large enough, the value of `μ` at `ℳ n` equals the value of the Hilbert polynomial at `n`.
5. `HilbertSerre.exists_unique_hilbertPolynomial ℳ μ hS`. The Hilbert polynomial is unique. In other words, for any `h : ℚ[X]`, if `h` satisfies the key property of the Hilbert polynomial, then `h` is the Hilbert polynomial itself.
6. `HilbertSerre.natDegree_hilbertPolynomial ℳ μ hhP`. If `hhP : hilbertPolynomial ℳ μ S ≠ 0`, then the degree of the Hilbert polynomial equals `S.toFinset.card - (numeratorPolynomial ℳ μ S).rootMultiplicity 1 - 1`.

## Structure of the Repository

### `HilbertPolynomial.lean` (root)
The entry-point file. It imports every module in the project and re-exports the whole library as a single unit.

### `AuxiliaryLemmas/`
Auxiliary lemmas.
- **`FGModuleCat.lean`** — Constructing a category equivalence `FGModuleCat R ≌ FGModuleCat S` for any ring isomorphism `R ≃+* S`, and shows that `FGModuleCat R` has finite limits when `R` is Noetherian.
- **`GradedModule.lean`** — Defining projection maps for internally graded modules (`GradedModule.proj`) and proves how they interact with the graded scalar action.
- **`GradeZeroModule.lean`** — Showing that each graded piece `ℳ i` of a graded `A`-module is a module over the degree-zero subring `𝒜 0`, and that the grade-zero action is compatible with scalar multiplication.

### `Module/FGModuleCat/`
Establishing that `FGModuleCat R` is an abelian category when `R` is Noetherian.

- **`EpiMono.lean`** — Proving that monomorphisms in `FGModuleCat` are precisely injective linear maps, and epimorphisms are precisely surjective ones.
- **`Kernels.lean`** — Constructing concrete kernels and cokernels in `FGModuleCat` (with explicit limit/colimit cones).
- **`Abelian.lean`** — Combining the above: every mono is normal, every epi is normal, hence `FGModuleCat R` is abelian. Also constructs image factorisations and proves the exactness criterion `exact_iff`.

### `Module/Graded/`
Infrastructure for graded rings and modules.

- **`Homogeneous.lean`** — Defining homogeneous submodules, subrings, and ideals of a graded module, along with their operations: intersection, quotient, hull, core; proves they form a complete lattice.
- **`Grading.lean`** — Showing that homogeneous subrings and homogeneous submodules inherit a graded structure, and that the quotient of a graded module by a homogeneous submodule is again graded.
- **`Noetherian.lean`** — Introducing `HomogeneousGeneratingSetOf` and proves the key finiteness theorems: a finitely generated graded module over a graded Noetherian ring is finitely generated over the degree-zero subring; the degree-zero subring is itself Noetherian.

### `HilbertSerre/`
The proof of the Hilbert–Serre theorem.

- **`AdditiveFunction.lean`** — Defining additive functions on abelian categories and proving related results.
- **`FiniteInstances.lean`** — Two finiteness lemmas used in the inductive step: (1) adjoining a finite set to a Noetherian ring yields a Noetherian ring; (2) a finite module annihilated by an element `s` remains finite after restricting scalars to the ring without `s`.
- **`Theorem.lean`** — The Hilbert–Serre theorem itself. Defines the Poincaré series `μ.poincareSeries 𝒜 ℳ ∈ ℤ⟦X⟧`, the structure `generatingSetOverBaseRing 𝒜`, and the poles `∏ᵢ (1 − Xᵈⁱ)`. The proof proceeds by induction on the number of generators: the base case (empty generator set) reduces to a truncated power series; the inductive step uses the exact sequence `0 → Kₙ → Mₙ → M_{n+d} → Lₙ → 0` together with the alternating-sum formula and the induction hypothesis applied to both the kernel module `K` and the cokernel module `L`.

### `HilbertPolynomial/HilbertPolynomial.lean`
Defines the Hilbert polynomial and proves its key properties.

- **`numeratorPolynomial`** — Extracting the numerator polynomial `p ∈ ℤ[X]` from the Hilbert–Serre theorem.
- **`hilbertPolynomial`** — Defining the Hilbert polynomial `h ∈ ℚ[X]` as `hilbertPoly(p̄, |S|)`, where `p̄` is `p` cast to `ℚ[X]` and `|S|` is the number of generators.
- **`AdditiveFunction_eq_hilbertPolynomial_eval`** — The key property: for all sufficiently large `n`, `μ(ℳ n) = h(n)`.
- **`exists_unique_hilbertPolynomial`** — Uniqueness: any polynomial with the above eventual-equality property must equal `h`.
- **`natDegree_hilbertPolynomial`** — Degree formula: if `h ≠ 0`, then `deg h = |S| − rootMultiplicity(p, 1) − 1`.
