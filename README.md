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

The blueprint provides a structured roadmap of the formalisation project, outlining the main definitions, theorems, dependencies, and overall proof architecture in Lean.
- [Blueprint (web)](https://FMLJohn.github.io/HilbertPolynomial/blueprint/)
- [Blueprint (PDF)](https://FMLJohn.github.io/HilbertPolynomial/blueprint.pdf)
- [Dependency graph](https://FMLJohn.github.io/HilbertPolynomial/blueprint/dep_graph_document.html)
- [API documentation](https://FMLJohn.github.io/HilbertPolynomial/docs/)

## Preliminary Definitions

1. `AdditiveFunction 𝒞 G`. Given an abelian category `𝒞` and an additive commutative group `G`, a function `λ` from the class of all objects of
`𝒞` to `G` is additive if `λ B = λ A + λ C` for every short exact sequence `0 --> A --> B --> C --> 0` in `𝒞`. `AdditiveFunction 𝒞 G` is the type of all additive functions from `𝒞` to `G`; we denote it as `𝒞 ⟹+ G`.
2. `generatingSetOverBaseRing 𝒜`. Given a commutative ring `A` and a function `𝒜 : ℕ → AddSubgroup A` with `GradedRing 𝒜`, if `S : generatingSetOverBaseRing 𝒜`, then `S` is a finite collection of homogeneous elements of `A` that generates `A` over `𝒜 0` such that every element of `S` is nonzero and has positive degree.

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
- **`FGModuleCat.lean`** — Constructing a category equivalence `FGModuleCat R ≌ FGModuleCat S` for any ring isomorphism `R ≃+* S`, and showing that `FGModuleCat R` has finite limits when `R` is Noetherian.
- **`GradedModule.lean`** — Defining projection maps for internally graded modules (`GradedModule.proj`) and proving how they interact with the graded scalar action.
- **`GradeZeroModule.lean`** — Showing that each graded piece `ℳ i` of a graded `A`-module is a module over the zeroth graded piece of `A`.

### `Module/FGModuleCat/`
Establishing that `FGModuleCat R` is an abelian category when `R` is Noetherian.
- **`EpiMono.lean`** — Proving that monomorphisms in `FGModuleCat R` are precisely injective linear maps, and epimorphisms are precisely surjective ones.
- **`Kernels.lean`** — Constructing concrete kernels and cokernels in `FGModuleCat R`.
- **`Abelian.lean`** — Combining the above: every monomorphism is normal and every epimorphism is normal, hence `FGModuleCat R` is abelian.

### `Module/Graded/`
Infrastructure for graded rings and modules.
- **`Homogeneous.lean`** — Defining homogeneous submodules and homogeneous subrings, and operations on them.
- **`Grading.lean`** — Showing that homogeneous subrings and homogeneous submodules inherit graded structures, and that the quotient of a graded module by a homogeneous submodule is again graded.
- **`Noetherian.lean`** — Introducing `GradedRing.HomogeneousGeneratingSetOf` and `GradedModule.HomogeneousGeneratingSetOf` and proving that every graded piece of a finitely generated graded module over a graded Noetherian ring is a finitely generated module over the degree-zero subring.

### `HilbertSerre/`
The proof of the Hilbert–Serre Theorem.
- **`AdditiveFunction.lean`** — Defining additive functions on abelian categories and proving related results.
- **`FiniteInstances.lean`** — Finiteness lemmas used in the inductive step, for example, adjoining a finite set to a Noetherian ring yields a Noetherian ring.
- **`Theorem.lean`** — The Hilbert–Serre Theorem itself. Defining Poincaré series, the structure `generatingSetOverBaseRing 𝒜`, and `generatingSetOverBaseRing.poles`. The proof proceeds by induction on the size of the finite set that generates the ring `A` as an algebra over the zeroth graded piece.

### `HilbertPolynomial/HilbertPolynomial.lean`
Defining Hilbert polynomials and showing their properties: `HilbertSerre.AdditiveFunction_eq_hilbertPolynomial_eval ℳ μ hS hn`, `HilbertSerre.exists_unique_hilbertPolynomial ℳ μ hS` and `HilbertSerre.natDegree_hilbertPolynomial ℳ μ hhP`.
