/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import HilbertPolynomial.AuxiliaryLemmas.GradedModule

import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Homogeneous submodules of a graded module

This file defines homogeneous submodule of a graded module `⨁ᵢ ℳᵢ` over graded ring `⨁ᵢ 𝒜ᵢ` and
operations on them.

## Main definitions

For any `p : Submodule A M`:
* `Submodule.IsHomogeneous ℳ p`: The property that a submodule is closed under `GradedModule.proj`.
* `HomogeneousSubmodule A ℳ`: The structure extending submodules which satisfy
  `Submodule.IsHomogeneous`.
* `Submodule.homogeneousCore p 𝒜 ℳ`: The largest homogeneous submodule smaller than `p`.
* `Submodule.homogeneousHull I 𝒜 ℳ`: The smallest homogeneous ideal larger than `p`.

## Main statements

* `HomogeneousSubmodule.completeLattice`: `Submodule.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`,
  `⊓`, `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Submodule.homogeneousCore.gi`: `Submodule.homogeneousCore` forms a galois insertion with
  coercion.
* `Submodule.homogeneousHull.gi`: `Submodule.homogeneousHull` forms a galois insertion with
  coercion.

## Implementation notes

We introduce `Submodule.homogeneousCore'` earlier than might be expected so that we can get access
to `Submodule.IsHomogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/


open SetLike DirectSum Set

open BigOperators Pointwise DirectSum

variable {ιA ιAA ιM σA σAA σM R A AA M : Type*}
variable [SetLike σA A] [SetLike σAA AA] [SetLike σM M]
variable [DecidableEq ιA] [DecidableEq ιM]

variable (𝒜 : ιA → σA) (ℳ : ιM → σM) (𝒜𝒜 : ιAA → σAA)

section HomogeneousDef

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Ring AA] [Module A M]
variable [SetLike σA A] [AddSubmonoidClass σA A]
variable [SetLike σAA AA] [AddSubgroupClass σAA AA]
variable [DecidableEq ιA] [AddMonoid ιA] [AddMonoid ιAA] [GradedRing 𝒜]
variable [DecidableEq ιAA] [GradedRing 𝒜𝒜]

variable (p : Submodule A M) (I : Ideal A)

/-- A subring `A'` is said to be homogeneous if for ever `a ∈ A'`, all homogeneous components
of `a` are in `A'`
-/
def Subring.IsHomogeneous (A' : Subring AA) : Prop :=
  ∀ (i : ιAA) ⦃a : AA⦄, a ∈ A' → (DirectSum.decompose 𝒜𝒜 a i : AA) ∈ A'

/-- We collect all homogeneous subring into a type
-/
structure HomogeneousSubring extends Subring AA where
  is_homogeneous' : toSubring.IsHomogeneous 𝒜𝒜

/-- An `p : Submodule A M` is homogeneous if for every `m ∈ p`, all homogeneous components
  of `m` are in `I`. -/
def Submodule.IsHomogeneous : Prop :=
  ∀ (i : ιM) ⦃m : M⦄, m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p

/-- An `I : Ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`. -/
def Ideal.IsHomogeneous : Prop :=
  Submodule.IsHomogeneous 𝒜 I

variable (A) in
/-- For any `Semiring A`, we collect the homogeneous submodule of `A`-modules into a type. -/
structure HomogeneousSubmodule extends Submodule A M where
  is_homogeneous' : Submodule.IsHomogeneous ℳ toSubmodule

/-- For any `Semiring A`, we collect the homogeneous ideals of `A` into a type. -/
def HomogeneousIdeal := HomogeneousSubmodule A 𝒜

variable {𝒜 ℳ 𝒜𝒜}


/-- Converting a homogeneous ideal to an ideal. -/
def HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule

set_option linter.unusedSectionVars false in
theorem HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜 := I.2

theorem HomogeneousSubmodule.isHomogeneous (I : HomogeneousSubmodule A ℳ) :
    I.toSubmodule.IsHomogeneous ℳ :=
  I.is_homogeneous'

set_option linter.unusedSectionVars false in
theorem HomogeneousSubring.isHomogeneous (A' : HomogeneousSubring 𝒜𝒜) :
    A'.toSubring.IsHomogeneous 𝒜𝒜 := A'.is_homogeneous'

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule A ℳ→ Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

set_option linter.unusedSectionVars false in
theorem HomogeneousIdeal.toIdeal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 → Ideal A) :=
  HomogeneousSubmodule.toSubmodule_injective

set_option linter.unusedSectionVars false in
theorem HomogeneousSubring.toSubring_injective :
    Function.Injective
      (HomogeneousSubring.toSubring : HomogeneousSubring 𝒜𝒜 → Subring AA) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ => fun (h : x = y) => by simp [h]

instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule A ℳ) M where
  coe p := p.toSubmodule
  coe_injective' _ _ h := HomogeneousSubmodule.toSubmodule_injective <| SetLike.coe_injective h

instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A := HomogeneousSubmodule.setLike

instance HomogeneousSubring.setLike : SetLike (HomogeneousSubring 𝒜𝒜) AA where
  coe x := x.toSubring
  coe_injective' _ _ h := HomogeneousSubring.toSubring_injective <| SetLike.coe_injective h

instance : SubringClass (HomogeneousSubring 𝒜𝒜) AA where
  mul_mem {x} := x.toSubring.mul_mem
  one_mem {x} := x.toSubring.one_mem
  add_mem {x} := x.toSubring.add_mem
  zero_mem {x} := x.toSubring.zero_mem
  neg_mem {x} := x.toSubring.neg_mem

@[ext]
theorem HomogeneousSubmodule.ext
    {I J : HomogeneousSubmodule A ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J :=
  HomogeneousSubmodule.toSubmodule_injective h

set_option linter.unusedSectionVars false in
@[ext]
theorem HomogeneousIdeal.ext
    {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousSubmodule.ext h

set_option linter.unusedSectionVars false in
@[ext]
theorem HomogeneousSubring.ext {x y : HomogeneousSubring 𝒜𝒜} (h : x.toSubring = y.toSubring) :
    x = y :=
  HomogeneousSubring.toSubring_injective h

@[simp]
theorem HomogeneousSubmodule.mem_iff {I : HomogeneousSubmodule A ℳ} {x : M} :
    x ∈ I.toSubmodule ↔ x ∈ I :=
  Iff.rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} :
    x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem HomogeneousSubring.mem_iff {A' : HomogeneousSubring 𝒜𝒜} (x : AA) :
    x ∈ A'.toSubring ↔ x ∈ A' :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Ring AA] [Module A M]

variable (p : Submodule A M) (I : Ideal A) (R : Subring AA)

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousCore' ℳ`
is the largest homogeneous `A`-submodule contained in `p`, as an `A`-submodule. -/
def Submodule.homogeneousCore' (I : Submodule A M) : Submodule A M :=
  Submodule.span A ((↑) '' (((↑) : Subtype (IsHomogeneousElem ℳ) → M) ⁻¹' I))

/-- For any subring `A'`, not necessarily homogeneous, `A.homogeneousCore' 𝒜` is the largest
homogeneous subring contained in `A'` as a subring.
-/
def Subring.homogeneousCore' (R : Subring AA) : Subring AA :=
  Subring.closure ((↑) '' (((↑) : Subtype (IsHomogeneousElem 𝒜𝒜) → AA) ⁻¹' R))

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Submodule.homogeneousCore' 𝒜 I

set_option linter.unusedSectionVars false in
theorem Submodule.homogeneousCore'_mono : Monotone (Submodule.homogeneousCore' (A := A) ℳ) :=
  fun _ _ I_le_J => Submodule.span_mono <| Set.image_subset _ fun _ => @I_le_J _

set_option linter.unusedSectionVars false in
theorem Ideal.homogeneousCore'_mono [AddSubmonoidClass σA A] [Decomposition 𝒜] :
    Monotone (Ideal.homogeneousCore' 𝒜) :=
  Submodule.homogeneousCore'_mono 𝒜

theorem Subring.homogeneousCore'_mono : Monotone (Subring.homogeneousCore' 𝒜𝒜) :=
  fun _ _ I_le_J => Subring.closure_mono <| Set.image_subset _ fun _ => @I_le_J _

set_option linter.unusedSectionVars false in
theorem Submodule.homogeneousCore'_le : p.homogeneousCore' ℳ ≤ p :=
  Submodule.span_le.2 <| image_preimage_subset _ _

set_option linter.unusedSectionVars false in
theorem Ideal.homogeneousCore'_le [AddSubmonoidClass σA A] [Decomposition 𝒜] :
    I.homogeneousCore' 𝒜 ≤ I :=
  Submodule.homogeneousCore'_le 𝒜 I

theorem Subring.homogeneousCore'_le : R.homogeneousCore' 𝒜𝒜 ≤ R :=
  Subring.closure_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousSubmoduleDefs

variable [AddMonoid ιA] [SetLike σA A] [SetLike σA A]
variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Ring AA] [AddSubmonoidClass σA A] [Module A M] [GradedRing 𝒜]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
variable [AddSubgroupClass σAA AA] [AddMonoid ιAA] [DecidableEq ιAA] [GradedRing 𝒜𝒜]

variable (p : Submodule A M) (I : Ideal A) (R : Subring AA)

theorem Submodule.isHomogeneous_iff_forall_subset :
    p.IsHomogeneous ℳ ↔ ∀ i, (p : Set M) ⊆ GradedModule.proj ℳ i ⁻¹' (p : Set M) :=
  Iff.rfl

set_option linter.unusedSectionVars false in
theorem Ideal.isHomogeneous_iff_forall_subset :
    I.IsHomogeneous 𝒜 ↔ ∀ i, (I : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' (I : Set A) :=
  Iff.rfl

theorem Subring.isHomogeneous_iff_forall_subset :
    R.IsHomogeneous 𝒜𝒜 ↔ ∀ i, (R : Set AA) ⊆ GradedRing.proj 𝒜𝒜 i ⁻¹' (R : Set AA) :=
  Iff.rfl

theorem Submodule.isHomogeneous_iff_subset_iInter :
    p.IsHomogeneous ℳ ↔ (p : Set M) ⊆ ⋂ i, GradedModule.proj ℳ i ⁻¹' ↑p :=
  subset_iInter_iff.symm

set_option linter.unusedSectionVars false in
theorem Ideal.isHomogeneous_iff_subset_iInter :
    I.IsHomogeneous 𝒜 ↔ (I : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I :=
  subset_iInter_iff.symm

theorem Subring.isHomogeneous_iff_subset_iInter :
    R.IsHomogeneous 𝒜𝒜 ↔ (R : Set AA) ⊆ ⋂ i, GradedRing.proj 𝒜𝒜 i ⁻¹' ↑R :=
  subset_iInter_iff.symm

set_option linter.unusedSectionVars false in
include 𝒜 in
theorem Submodule.smul_homogeneous_element_mem_of_mem {p : Submodule A M} (r : A) (x : M)
    (hx₁ : IsHomogeneousElem ℳ x) (hx₂ : x ∈ p) (j : ιM) : GradedModule.proj ℳ j (r • x) ∈ p := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) • x ∈ ℳ (k +ᵥ i) :=
    GradedSMul.smul_mem (SetLike.coe_mem _) hi
  erw [GradedModule.proj_apply, DirectSum.decompose_of_mem ℳ mem₁, coe_of_apply]
  split_ifs with h
  · exact Submodule.smul_mem _ _ hx₂
  · exact p.zero_mem

set_option linter.unusedSectionVars false in
theorem Ideal.mul_homogeneous_element_mem_of_mem {I : Ideal A} (r x : A)
    (hx₁ : IsHomogeneousElem 𝒜 x) (hx₂ : x ∈ I) (j : ιA) : GradedRing.proj 𝒜 j (r * x) ∈ I :=
  Submodule.smul_homogeneous_element_mem_of_mem 𝒜 𝒜 r x hx₁ hx₂ j

set_option linter.unusedSectionVars false in
include 𝒜 in
theorem Submodule.homogeneous_span (s : Set M) (h : ∀ x ∈ s, IsHomogeneousElem ℳ x) :
    (Submodule.span A s).IsHomogeneous ℳ := by
  rintro i r hr
  rw [mem_span_set] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  rw [Finsupp.sum, decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  refine' Submodule.sum_mem _ _
  rintro z hz1
  apply Submodule.smul_homogeneous_element_mem_of_mem (𝒜 := 𝒜) (ℳ := ℳ)
  · exact h _ (hc hz1)
  · exact Submodule.subset_span (hc hz1)

set_option linter.unusedSectionVars false in
theorem Ideal.homogeneous_span (s : Set A) (h : ∀ x ∈ s, IsHomogeneousElem 𝒜 x) :
    (Ideal.span s).IsHomogeneous 𝒜 :=
  Submodule.homogeneous_span 𝒜 𝒜 s h

theorem Subring.homogeneous_closure (s : Set AA) (h : ∀ x ∈ s, IsHomogeneousElem 𝒜𝒜 x) :
    (Subring.closure s).IsHomogeneous 𝒜𝒜 := by
  intro i x hx
  revert i
  refine Subring.closure_induction (hx := hx) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx i
    obtain ⟨j, hj⟩ := h _ hx
    by_cases h : i = j
    · subst h
      rw [decompose_of_mem_same (hx := hj)]
      refine subset_closure hx
    · rw [decompose_of_mem_ne (hx := hj) (hij := Ne.symm h)]
      exact Subring.zero_mem _
  · intro i
    rw [decompose_zero]
    exact (closure s).zero_mem
  · intro i
    by_cases h : i = 0
    · subst h
      rw [decompose_of_mem_same]
      · exact (closure s).one_mem
      rw [show (1 : AA) = ((1 : ℤ) : AA) by simp]
      apply SetLike.intCast_mem_graded

    · rw [decompose_of_mem_ne 𝒜𝒜 (i := 0) (j := i) (hij := Ne.symm h)]
      · exact (closure s).zero_mem
      rw [show (1 : AA) = ((1 : ℤ) : AA) by simp]
      apply SetLike.intCast_mem_graded
  · intro x y _ _ hx hy i
    simp only [decompose_add, add_apply, AddMemClass.coe_add]
    exact (closure s).add_mem (hx i) (hy i)
  · intro x _ h i
    simp only [decompose_neg]
    exact (closure s).neg_mem (h i)
  · intro a b _ _ ha hb i
    classical
    rw [← sum_support_decompose 𝒜𝒜 a, ← sum_support_decompose 𝒜𝒜 b, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [decompose_sum]
    simp_rw [decompose_sum]
    simp only [decompose_mul, decompose_coe, Finset.coe_insert]
    erw [DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
    refine Subring.sum_mem _ fun j _ ↦ ?_
    erw [DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
    refine Subring.sum_mem _ fun k _ ↦ ?_
    rw [DirectSum.of_mul_of, DirectSum.coe_of_apply]
    split_ifs with h
    · specialize ha j
      specialize hb k
      simp only [coe_gMul]
      exact Subring.mul_mem _  ha hb
    · exact Subring.zero_mem _

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousCore' ℳ`
is the largest homogeneous `A`-submodule contained in `p`. -/
def Submodule.homogeneousCore : HomogeneousSubmodule A ℳ :=
  ⟨p.homogeneousCore' ℳ,
    Submodule.homogeneous_span 𝒜 _ _ fun _ h => (Subtype.image_preimage_coe _ _ ▸ h).1⟩

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`. -/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 := Submodule.homogeneousCore 𝒜 𝒜 I

set_option linter.unusedSectionVars false in
theorem Submodule.homogeneousCore_mono : Monotone (Submodule.homogeneousCore 𝒜 ℳ) :=
  Submodule.homogeneousCore'_mono ℳ

set_option linter.unusedSectionVars false in
theorem Ideal.homogeneousCore_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneousCore'_mono 𝒜

set_option linter.unusedSectionVars false in
theorem Submodule.toSubmodule_homogeneousCore_le : (p.homogeneousCore 𝒜 ℳ).toSubmodule ≤ p :=
  Submodule.homogeneousCore'_le ℳ p

set_option linter.unusedSectionVars false in
theorem Ideal.toIdeal_homogeneousCore_le : (I.homogeneousCore 𝒜).toIdeal ≤ I :=
  Ideal.homogeneousCore'_le 𝒜 I

variable {ℳ I}

set_option linter.unusedSectionVars false in
theorem Submodule.mem_homogeneousCore_of_homogeneous_of_mem {x : M} (h : IsHomogeneousElem ℳ x)
    (hmem : x ∈ p) : x ∈ p.homogeneousCore 𝒜 ℳ :=
  Submodule.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

variable {𝒜}

set_option linter.unusedSectionVars false in
theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    {x : A} (h : IsHomogeneousElem 𝒜 x) (hmem : x ∈ I) :
    x ∈ I.homogeneousCore 𝒜 :=
  Submodule.mem_homogeneousCore_of_homogeneous_of_mem 𝒜 I h hmem

set_option linter.unusedSectionVars false in
theorem Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self (h : p.IsHomogeneous ℳ) :
    (p.homogeneousCore 𝒜 ℳ).toSubmodule = p := by
  apply le_antisymm (p.homogeneousCore'_le ℳ) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨⟨_, isHomogeneousElem_coe _⟩, h _ hx, rfl⟩

set_option linter.unusedSectionVars false in
theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) :
    (I.homogeneousCore 𝒜).toIdeal = I :=
  Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self I h

set_option linter.unusedSectionVars false in
@[simp]
theorem HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self (p : HomogeneousSubmodule A ℳ) :
    p.toSubmodule.homogeneousCore 𝒜 ℳ = p := by
  ext1
  convert Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self _ p.isHomogeneous
  · infer_instance
  · infer_instance

set_option linter.unusedSectionVars false in
@[simp]
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousCore 𝒜 = I :=
  HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self I

variable (𝒜 I)

set_option linter.unusedSectionVars false in
theorem Submodule.IsHomogeneous.iff_eq :
    p.IsHomogeneous ℳ ↔ (p.homogeneousCore 𝒜 ℳ).toSubmodule = p :=
  ⟨fun hI => hI.toSubmodule_homogeneousCore_eq_self, fun hI => hI ▸ (p.homogeneousCore 𝒜 ℳ).2⟩

set_option linter.unusedSectionVars false in
theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I :=
  Submodule.IsHomogeneous.iff_eq 𝒜 I

include 𝒜 in
set_option linter.unusedSectionVars false in
theorem Submodule.IsHomogeneous.iff_exists :
    p.IsHomogeneous ℳ ↔ ∃ S : Set {x // IsHomogeneousElem ℳ x}, p = Submodule.span A ((↑) '' S) := by
  rw [Submodule.IsHomogeneous.iff_eq 𝒜, eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

set_option linter.unusedSectionVars false in
theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S) :=
  Submodule.IsHomogeneous.iff_exists 𝒜 I

end IsHomogeneousSubmoduleDefs

/-! ### Operations

In this section, we show that `Ideal.IsHomogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `HomogeneousSubmodule`. -/


section Operations

section Semiring

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Module A M]

variable [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A]
variable [GradedRing 𝒜] [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

namespace Submodule.IsHomogeneous

theorem bot : Submodule.IsHomogeneous (A := A) ℳ ⊥ := fun i r hr => by
  simp only [Submodule.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Submodule.zero_mem

theorem top : Submodule.IsHomogeneous (A := A) ℳ ⊤ := fun i r _ => by simp only [Submodule.mem_top]

variable {𝒜 ℳ}

theorem inf {I J : Submodule A M} (HI : I.IsHomogeneous ℳ) (HJ : J.IsHomogeneous ℳ) :
    (I ⊓ J).IsHomogeneous ℳ :=
  fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩

set_option linter.unusedSectionVars false in
include 𝒜 in
theorem sup {I J : Submodule A M} (HI : I.IsHomogeneous ℳ) (HJ : J.IsHomogeneous ℳ) :
    (I ⊔ J).IsHomogeneous ℳ := by
  rw [iff_exists (𝒜 := 𝒜)] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine' ⟨s₁ ∪ s₂, _⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

set_option linter.unusedSectionVars false in
include 𝒜 in
protected theorem iSup {κ : Sort*} {f : κ → Submodule A M} (h : ∀ i, (f i).IsHomogeneous ℳ) :
    (⨆ i, f i).IsHomogeneous ℳ := by
  simp_rw [iff_exists (𝒜 := 𝒜) (ℳ := ℳ)] at h ⊢
  choose s hs using h
  refine' ⟨⋃ i, s i, _⟩
  simp_rw [Set.image_iUnion, Submodule.span_iUnion]
  congr
  exact funext hs

protected theorem iInf {κ : Sort*} {f : κ → Submodule A M} (h : ∀ i, (f i).IsHomogeneous ℳ) :
    (⨅ i, f i).IsHomogeneous ℳ := by
  intro i x hx
  simp only [Submodule.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)

set_option linter.unusedSectionVars false in
include 𝒜 in
theorem iSup₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Submodule A M}
    (h : ∀ i j, (f i j).IsHomogeneous ℳ) : (⨆ (i) (j), f i j).IsHomogeneous ℳ :=
  IsHomogeneous.iSup (𝒜 := 𝒜) fun i => IsHomogeneous.iSup (𝒜 := 𝒜) <| h i

theorem iInf₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Submodule A M}
    (h : ∀ i j, (f i j).IsHomogeneous ℳ) : (⨅ (i) (j), f i j).IsHomogeneous ℳ :=
  IsHomogeneous.iInf fun i => IsHomogeneous.iInf <| h i

set_option linter.unusedSectionVars false in
include 𝒜 in
theorem sSup {ℐ : Set (Submodule A M)} (h : ∀ I ∈ ℐ, I.IsHomogeneous ℳ) :
    (sSup ℐ).IsHomogeneous ℳ := by
  rw [sSup_eq_iSup]
  exact iSup₂ (𝒜 := 𝒜) h

theorem sInf {ℐ : Set (Submodule A M)} (h : ∀ I ∈ ℐ, I.IsHomogeneous ℳ) :
    (sInf ℐ).IsHomogeneous ℳ := by
  rw [sInf_eq_iInf]
  exact iInf₂ h

end Submodule.IsHomogeneous

namespace Ideal.IsHomogeneous

set_option linter.unusedSectionVars false in
theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := Submodule.IsHomogeneous.bot 𝒜

set_option linter.unusedSectionVars false in
theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := Submodule.IsHomogeneous.top 𝒜

variable {𝒜 ℳ}

set_option linter.unusedSectionVars false in
theorem inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊓ J).IsHomogeneous 𝒜 := Submodule.IsHomogeneous.inf HI HJ

set_option linter.unusedSectionVars false in
theorem sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊔ J).IsHomogeneous 𝒜 := Submodule.IsHomogeneous.sup (𝒜 := 𝒜) HI HJ

set_option linter.unusedSectionVars false in
protected theorem iSup {κ : Sort*} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) :
    (⨆ i, f i).IsHomogeneous 𝒜 := Submodule.IsHomogeneous.iSup (𝒜 := 𝒜) h

set_option linter.unusedSectionVars false in
protected theorem iInf {κ : Sort*} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) :
    (⨅ i, f i).IsHomogeneous 𝒜 := Submodule.IsHomogeneous.iInf h

set_option linter.unusedSectionVars false in
theorem iSup₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).IsHomogeneous 𝒜) : (⨆ (i) (j), f i j).IsHomogeneous 𝒜 :=
  Submodule.IsHomogeneous.iSup₂ (𝒜 := 𝒜) h

set_option linter.unusedSectionVars false in
theorem iInf₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).IsHomogeneous 𝒜) : (⨅ (i) (j), f i j).IsHomogeneous 𝒜 :=
  Submodule.IsHomogeneous.iInf₂ h

set_option linter.unusedSectionVars false in
theorem sSup {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, I.IsHomogeneous 𝒜) :
    (sSup ℐ).IsHomogeneous 𝒜 := Submodule.IsHomogeneous.sSup (𝒜 := 𝒜) h

set_option linter.unusedSectionVars false in
theorem sInf {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, I.IsHomogeneous 𝒜) :
    (sInf ℐ).IsHomogeneous 𝒜 := Submodule.IsHomogeneous.sInf h

end Ideal.IsHomogeneous

variable {𝒜 ℳ}

namespace HomogeneousSubmodule

instance : PartialOrder (HomogeneousSubmodule A ℳ) :=
  SetLike.instPartialOrder

instance : Top (HomogeneousSubmodule A ℳ) :=
  ⟨⟨⊤, Submodule.IsHomogeneous.top ℳ⟩⟩

instance : Bot (HomogeneousSubmodule A ℳ) :=
  ⟨⟨⊥, Submodule.IsHomogeneous.bot ℳ⟩⟩

set_option synthInstance.checkSynthOrder false in
instance sup : Max (HomogeneousSubmodule A ℳ) :=
  ⟨fun I J => ⟨I.toSubmodule ⊔ J.toSubmodule, I.isHomogeneous.sup (𝒜 := 𝒜) J.isHomogeneous⟩⟩

instance : Min (HomogeneousSubmodule A ℳ) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩

set_option synthInstance.checkSynthOrder false in
instance supSet : SupSet (HomogeneousSubmodule A ℳ) :=
  ⟨fun S => ⟨⨆ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.iSup₂ (𝒜 := 𝒜)
    fun s _ => s.isHomogeneous⟩⟩

instance : InfSet (HomogeneousSubmodule A ℳ) :=
  ⟨fun S => ⟨⨅ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]
theorem coe_top : ((⊤ : HomogeneousSubmodule A ℳ) : Set M) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : HomogeneousSubmodule A ℳ) : Set M) = 0 :=
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem coe_sup (I J : HomogeneousSubmodule A ℳ) : ↑(I ⊔ J) = (I + J : Set M) :=
  Submodule.coe_sup _ _

@[simp, nolint simpNF]
theorem coe_inf (I J : HomogeneousSubmodule A ℳ) : (↑(I ⊓ J) : Set M) = ↑I ∩ ↑J :=
  rfl

@[simp]
theorem toSubmodule_top : (⊤ : HomogeneousSubmodule A ℳ).toSubmodule = (⊤ : Submodule A M) :=
  rfl

@[simp]
theorem toSubmodule_bot : (⊥ : HomogeneousSubmodule A ℳ).toSubmodule = (⊥ : Submodule A M) :=
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toSubmodule_sup (I J : HomogeneousSubmodule A ℳ) :
    (I ⊔ J).toSubmodule = I.toSubmodule ⊔ J.toSubmodule := rfl

@[simp, nolint simpNF]
theorem toSubmodule_inf (I J : HomogeneousSubmodule A ℳ) :
    (I ⊓ J).toSubmodule = I.toSubmodule ⊓ J.toSubmodule := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toSubmodule_sSup (ℐ : Set (HomogeneousSubmodule A ℳ)) :
    (sSup ℐ).toSubmodule = ⨆ s ∈ ℐ, toSubmodule s := rfl

@[simp]
theorem toSubmodule_sInf (ℐ : Set (HomogeneousSubmodule A ℳ)) :
    (sInf ℐ).toSubmodule = ⨅ s ∈ ℐ, toSubmodule s := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toSubmodule_iSup {κ : Sort*} (s : κ → HomogeneousSubmodule A ℳ) :
    (⨆ i, s i).toSubmodule = ⨆ i, (s i).toSubmodule := by
  rw [iSup, toSubmodule_sSup, iSup_range]

@[simp, nolint simpNF]
theorem toSubmodule_iInf {κ : Sort*} (s : κ → HomogeneousSubmodule A ℳ) :
    (⨅ i, s i).toSubmodule = ⨅ i, (s i).toSubmodule := by
  rw [iInf, toSubmodule_sInf, iInf_range]

set_option linter.unusedSectionVars false in
-- @[simp] -- Porting note: simp can prove this
theorem toSubmodule_iSup₂ {κ : Sort*} {κ' : κ → Sort*}
    (s : ∀ i, κ' i → HomogeneousSubmodule A ℳ) :
    (⨆ (i) (j), s i j).toSubmodule = ⨆ (i) (j), (s i j).toSubmodule := by
  simp_rw [toSubmodule_iSup]

-- @[simp] -- Porting note: simp can prove this
theorem toSubmodule_iInf₂ {κ : Sort*} {κ' : κ → Sort*}
    (s : ∀ i, κ' i → HomogeneousSubmodule A ℳ) :
    (⨅ (i) (j), s i j).toSubmodule = ⨅ (i) (j), (s i j).toSubmodule := by
  simp_rw [toSubmodule_iInf]

@[simp]
theorem eq_top_iff (I : HomogeneousSubmodule A ℳ) : I = ⊤ ↔ I.toSubmodule = ⊤ :=
  toSubmodule_injective.eq_iff.symm

@[simp]
theorem eq_bot_iff (I : HomogeneousSubmodule A ℳ) : I = ⊥ ↔ I.toSubmodule = ⊥ :=
  toSubmodule_injective.eq_iff.symm

set_option synthInstance.checkSynthOrder false in
instance completeLattice : CompleteLattice (HomogeneousSubmodule A ℳ) :=
  toSubmodule_injective.completeLattice _ toSubmodule_sup toSubmodule_inf toSubmodule_sSup
    toSubmodule_sInf toSubmodule_top toSubmodule_bot

set_option synthInstance.checkSynthOrder false in
instance : Add (HomogeneousSubmodule A ℳ) :=
  ⟨(· ⊔ ·)⟩

set_option linter.unusedSectionVars false in
@[simp]
theorem toSubmodule_add (I J : HomogeneousSubmodule A ℳ) :
    (I + J).toSubmodule = I.toSubmodule + J.toSubmodule := rfl

instance : Inhabited (HomogeneousSubmodule A ℳ) where default := ⊥

end HomogeneousSubmodule

namespace HomogeneousIdeal

instance : PartialOrder (HomogeneousSubmodule A ℳ) :=
  SetLike.instPartialOrder

instance : Top (HomogeneousIdeal 𝒜) := inferInstanceAs <| Top <| HomogeneousSubmodule A 𝒜

instance : Bot (HomogeneousIdeal 𝒜) := inferInstanceAs <| Bot <| HomogeneousSubmodule A 𝒜

instance : Max (HomogeneousIdeal 𝒜) := inferInstanceAs <| Max <| HomogeneousSubmodule A 𝒜

instance : Min (HomogeneousIdeal 𝒜) := inferInstanceAs <| Min <| HomogeneousSubmodule A 𝒜

instance : SupSet (HomogeneousIdeal 𝒜) := inferInstanceAs <| SupSet <| HomogeneousSubmodule A 𝒜

instance : InfSet (HomogeneousIdeal 𝒜) := inferInstanceAs <| InfSet <| HomogeneousSubmodule A 𝒜

set_option linter.unusedSectionVars false in
@[simp]
theorem coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0 := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I ⊔ J) = (I + J : Set A) :=
  Submodule.coe_sup _ _

set_option linter.unusedSectionVars false in
@[simp]
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I ⊓ J) : Set A) = ↑I ∩ ↑J :=
  rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A) := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A) := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sSup ℐ).toIdeal = ⨆ s ∈ ℐ, toIdeal s := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜)) : (sInf ℐ).toIdeal = ⨅ s ∈ ℐ, toIdeal s := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_iSup {κ : Sort*} (s : κ → HomogeneousIdeal 𝒜) :
    (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal :=
  HomogeneousSubmodule.toSubmodule_iSup (𝒜 := 𝒜) s

set_option linter.unusedSectionVars false in
@[simp]
theorem toIdeal_iInf {κ : Sort*} (s : κ → HomogeneousIdeal 𝒜) :
    (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal :=
  HomogeneousSubmodule.toSubmodule_iInf s

set_option linter.unusedSectionVars false in
theorem toIdeal_iSup₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨆ (i) (j), s i j).toIdeal = ⨆ (i) (j), (s i j).toIdeal :=
  HomogeneousSubmodule.toSubmodule_iSup₂ (𝒜 := 𝒜) s

set_option linter.unusedSectionVars false in
theorem toIdeal_iInf₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨅ (i) (j), s i j).toIdeal = ⨅ (i) (j), (s i j).toIdeal :=
  HomogeneousSubmodule.toSubmodule_iInf₂ s


set_option linter.unusedSectionVars false

@[simp]
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤ :=
  HomogeneousSubmodule.eq_top_iff I

@[simp]
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥ :=
  HomogeneousSubmodule.eq_bot_iff I

instance completeLattice : CompleteLattice (HomogeneousIdeal 𝒜) :=
  inferInstanceAs <| CompleteLattice <| HomogeneousSubmodule A 𝒜

instance : Add (HomogeneousIdeal 𝒜) := inferInstanceAs <| Add <| HomogeneousSubmodule A 𝒜

@[simp]
theorem toIdeal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.toIdeal := rfl

instance : Inhabited (HomogeneousSubmodule A ℳ) where default := ⊥

end HomogeneousIdeal

end Semiring

section CommSemiring

variable {𝒜}

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [CommSemiring A] [Module A M]

variable [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]

set_option linter.unusedSectionVars false

-- In general, submodules cannot be multiplied, so this theorem is not generalized
theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists 𝒜] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  exact ⟨s₁ * s₂, congr_arg _ <| (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩

instance : Mul (HomogeneousIdeal 𝒜) where
  mul I J := ⟨I.toIdeal * J.toIdeal, Ideal.IsHomogeneous.mul I.isHomogeneous J.isHomogeneous⟩

@[simp]
theorem HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) :
    (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl

end CommSemiring

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section homogeneousCore

open HomogeneousSubmodule HomogeneousIdeal

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Module A M]

variable [AddMonoid ιA]
variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [VAdd ιA ιM] [Decomposition ℳ] [GradedSMul 𝒜 ℳ]

set_option linter.unusedSectionVars false

variable (I : Ideal A) (p : Submodule A M)

theorem Submodule.homogeneousCore.gc :
    GaloisConnection toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) := fun I _ =>
  ⟨fun H => I.toSubmodule_homogeneousCore_eq_self (𝒜 := 𝒜) ▸ Submodule.homogeneousCore_mono 𝒜 ℳ H,
    fun H => le_trans H (Submodule.homogeneousCore'_le _ _)⟩

theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜) :=
  Submodule.homogeneousCore.gc 𝒜 𝒜

/-- `toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M` and `Submodule.homogeneousCore 𝒜 ℳ`
forms a galois coinsertion. -/
def Submodule.homogeneousCore.gi :
    GaloisCoinsertion toSubmodule (Submodule.homogeneousCore 𝒜 ℳ) where
  choice I HI :=
    ⟨I, le_antisymm (I.toSubmodule_homogeneousCore_le 𝒜 ℳ) HI ▸
      HomogeneousSubmodule.isHomogeneous _⟩
  gc := Submodule.homogeneousCore.gc 𝒜 ℳ
  u_l_le _ := Submodule.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toSubmodule_homogeneousCore_le _ _)

/-- `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` and `Ideal.homogeneousCore 𝒜` forms a galois
coinsertion. -/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) :=
  Submodule.homogeneousCore.gi 𝒜 𝒜

theorem Submodule.homogeneousCore_eq_sSup :
    p.homogeneousCore 𝒜 ℳ = sSup { q : HomogeneousSubmodule A ℳ | q.toSubmodule ≤ p } :=
  Eq.symm <| IsLUB.sSup_eq <| (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u.isLUB

theorem Ideal.homogeneousCore_eq_sSup :
    I.homogeneousCore 𝒜 = sSup { J : HomogeneousIdeal 𝒜 | J.toIdeal ≤ I } :=
  Submodule.homogeneousCore_eq_sSup 𝒜 𝒜 I

include 𝒜 in
theorem Submodule.homogeneousCore'_eq_sSup :
    p.homogeneousCore' ℳ = sSup { q : Submodule A M | q.IsHomogeneous ℳ ∧ q ≤ p } := by
  refine' (IsLUB.sSup_eq _).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M) := fun x y => id
  convert coe_mono.map_isGreatest (Submodule.homogeneousCore.gc 𝒜 ℳ).isGreatest_u using 1
  ext x
  rw [mem_image, mem_setOf_eq]
  refine' ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, _⟩
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact ⟨x.isHomogeneous, hx⟩

theorem Ideal.homogeneousCore'_eq_sSup :
    I.homogeneousCore' 𝒜 = sSup { J : Ideal A | J.IsHomogeneous 𝒜 ∧ J ≤ I } :=
  Submodule.homogeneousCore'_eq_sSup 𝒜 𝒜 I

end homogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousSubmodule

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Module A M] [DecidableEq ιA] [AddMonoid ιA]
variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜] [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

variable (I : Ideal A) (p : Submodule A M)

/-- For any `p : Submodule A M`, not necessarily homogeneous, `p.homogeneousHull 𝒜 ℳ` is the
smallest  homogeneous `A`-submodule containing `p`. -/
def Submodule.homogeneousHull : HomogeneousSubmodule A ℳ :=
  ⟨Submodule.span A { r : M | ∃ (i : ιM) (x : p), (DirectSum.decompose ℳ (x : M) i : M) = r }, by
    refine' Submodule.homogeneous_span 𝒜 ℳ _ fun x hx => _
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousHull 𝒜` is the smallest
homogeneous ideal containing `I`. -/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  Submodule.homogeneousHull 𝒜 𝒜 I


set_option linter.unusedSectionVars false

theorem Submodule.le_toSubmodule_homogeneousHull :
    p ≤ (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose ℳ r]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.subset_span ⟨j, ⟨⟨r, hr⟩, rfl⟩⟩

theorem Ideal.le_toSubmodule_homogeneousHull : I ≤ (I.homogeneousHull 𝒜).toIdeal :=
  Submodule.le_toSubmodule_homogeneousHull 𝒜 𝒜 I

theorem Submodule.homogeneousHull_mono :
    Monotone (Submodule.homogeneousHull 𝒜 ℳ) := fun I J I_le_J => by
  apply Submodule.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

theorem Ideal.homogeneousHull_mono : Monotone (Ideal.homogeneousHull 𝒜) :=
  Submodule.homogeneousHull_mono 𝒜 𝒜

variable {p I 𝒜 ℳ}

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousHull_eq_self (h : p.IsHomogeneous ℳ) :
    (Submodule.homogeneousHull 𝒜 ℳ p).toSubmodule = p := by
  apply le_antisymm _ (Submodule.le_toSubmodule_homogeneousHull _ _ _)
  apply Submodule.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h : I.IsHomogeneous 𝒜) :
    (I.homogeneousHull 𝒜).toIdeal = I :=
  Submodule.IsHomogeneous.toSubmodule_homogeneousHull_eq_self h

@[simp]
theorem HomogeneousSubmodule.homogeneousHull_toSubmodule_eq_self (p : HomogeneousSubmodule A ℳ) :
    p.toSubmodule.homogeneousHull 𝒜 ℳ = p :=
  HomogeneousSubmodule.toSubmodule_injective <| p.2.toSubmodule_homogeneousHull_eq_self

@[simp]
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousHull 𝒜 = I :=
  HomogeneousSubmodule.homogeneousHull_toSubmodule_eq_self I

variable (p I)

theorem Submodule.toSubmodule_homogeneousHull_eq_iSup :
    (p.homogeneousHull 𝒜 ℳ).toSubmodule = ⨆ i, Submodule.span A (GradedModule.proj ℳ i '' p) := by
  rw [← Submodule.span_iUnion]
  apply congr_arg (Submodule.span A ·) _
  aesop

theorem Ideal.toIdeal_homogeneousHull_eq_iSup :
    (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I) :=
  Submodule.toSubmodule_homogeneousHull_eq_iSup I

theorem Submodule.homogeneousHull_eq_iSup :
    p.homogeneousHull 𝒜 ℳ =
      ⨆ i, ⟨Submodule.span A (GradedModule.proj ℳ i '' p), Submodule.homogeneous_span 𝒜 ℳ _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.isHomogeneousElem_coe)⟩ := by
  ext1
  rw [Submodule.toSubmodule_homogeneousHull_eq_iSup, toSubmodule_iSup]

theorem Ideal.homogeneousHull_eq_iSup :
    I.homogeneousHull 𝒜 =
      ⨆ i, ⟨Ideal.span (GradedRing.proj 𝒜 i '' I), Ideal.homogeneous_span 𝒜 _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.isHomogeneousElem_coe)⟩ :=
  Submodule.homogeneousHull_eq_iSup I

end HomogeneousHull

section GaloisConnection

set_option linter.unusedSectionVars false

open HomogeneousSubmodule HomogeneousIdeal

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Module A M] [DecidableEq ιA] [AddMonoid ιA]

variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜] [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

theorem Submodule.homogeneousHull.gc :
    GaloisConnection (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule := fun _ J =>
  ⟨le_trans (Submodule.le_toSubmodule_homogeneousHull _ _ _),
    fun H => J.homogeneousHull_toSubmodule_eq_self (𝒜 := 𝒜) ▸ Submodule.homogeneousHull_mono 𝒜 ℳ H⟩

theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal :=
  Submodule.homogeneousHull.gc 𝒜 𝒜


/-- `Submodule.homogeneousHull 𝒜 ℳ` and `toSubmodule : HomogeneousSubmodule A ℳ → Submodule A M`
form a galois insertion. -/
def Submodule.homogeneousHull.gi : GaloisInsertion (Submodule.homogeneousHull 𝒜 ℳ) toSubmodule where
  choice I H := ⟨I, le_antisymm H (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) ▸ isHomogeneous _⟩
  gc := Submodule.homogeneousHull.gc 𝒜 ℳ
  le_l_u _ := Submodule.le_toSubmodule_homogeneousHull 𝒜 _ _
  choice_eq I H := le_antisymm (I.le_toSubmodule_homogeneousHull 𝒜 ℳ) H

/-- `Ideal.homogeneousHull 𝒜` and `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` form a galois insertion.
-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal :=
  Submodule.homogeneousHull.gi 𝒜 𝒜

theorem Submodule.homogeneousHull_eq_sInf (p : Submodule A M) :
    p.homogeneousHull 𝒜 ℳ = sInf { q : HomogeneousSubmodule A ℳ | p ≤ q.toSubmodule } :=
  Eq.symm <| IsGLB.sInf_eq <| (Submodule.homogeneousHull.gc 𝒜 ℳ).isLeast_l.isGLB

theorem Ideal.homogeneousHull_eq_sInf (I : Ideal A) :
    I.homogeneousHull 𝒜 = sInf { J : HomogeneousIdeal 𝒜 | I ≤ J.toIdeal } :=
  Submodule.homogeneousHull_eq_sInf 𝒜 𝒜 I

end GaloisConnection

section IrrelevantIdeal

variable [Semiring A]

variable [OrderedAddCommMonoid ιA] [CanonicallyOrderedAdd ιA]

variable [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]

open GradedRing SetLike.GradedMonoid DirectSum


set_option linter.unusedSectionVars false

/-- For a graded ring `⨁ᵢ 𝒜ᵢ` graded by a `CanonicallyOrderedAddCommMonoid ι`, the irrelevant ideal
refers to `⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj`
construction where `ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.

# Future work
Here in the definition, `ι` is assumed to be `CanonicallyOrderedAddCommMonoid`. However, the notion
of irrelevant ideal makes sense in a more general setting by defining it as the ideal of elements
with `0` as i-th coordinate for all `i ≤ 0`, i.e. `{a | ∀ (i : ι), i ≤ 0 → aᵢ = 0}`.
-/
def HomogeneousIdeal.irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩

@[simp]
theorem HomogeneousIdeal.mem_irrelevant_iff (a : A) :
    a ∈ HomogeneousIdeal.irrelevant 𝒜 ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl

@[simp]
theorem HomogeneousIdeal.toIdeal_irrelevant :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal = RingHom.ker (GradedRing.projZeroRingHom 𝒜) :=
  rfl

end IrrelevantIdeal

section HomogeneouslyFG

variable [AddCommMonoid M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [Semiring A] [Module A M]
variable [AddMonoid ιA] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable (p : HomogeneousSubmodule A ℳ) (I : HomogeneousIdeal 𝒜)

/--
A module is homogeneously finitely generated if and only if it can be generated by a finite set of
non-zero homogeneous elements
-/
def Submodule.homogeneously_FG (p : Submodule A M) : Prop :=
  ∃ (s : Finset M), (∀ m ∈ s, IsHomogeneousElem ℳ m ∧ m ≠ 0) ∧ p = Submodule.span A s

/--
An ideal is homogeneously finitely generated if and only if it can be generated by a finite set of
non-zero homogeneous elements
-/
def Ideal.homogeneously_FG (I : Ideal A) : Prop := Submodule.homogeneously_FG 𝒜 I

variable {ℳ} in
lemma Submodule.fg_iff_homogeneously_fg : p.toSubmodule.FG ↔ p.toSubmodule.homogeneously_FG ℳ := by
  classical
  fconstructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    refine ⟨s.sup (GradedModule.homogeneousComponents ℳ), fun m hs ↦ ?_, ?_⟩
    · rw [Finset.mem_sup] at hs
      rcases hs with ⟨v, -, hv⟩
      refine ⟨GradedModule.homogeneous_of_mem_homogeneousComponents ℳ hv, ?_⟩
      simp only [GradedModule.homogeneousComponents, Finset.mem_image, DFinsupp.mem_support_toFun,
        ne_eq] at hv
      obtain ⟨a, ha1, rfl⟩ := hv
      contrapose! ha1
      ext
      exact ha1
    · refine le_antisymm ?_ ?_ <;>
      rw [Submodule.span_le]
      · intro x hx
        rw [← sum_support_decompose ℳ x]
        refine Submodule.sum_mem _ fun i hi ↦ Submodule.subset_span ?_
        simp only [Finset.mem_coe, Finset.mem_sup]
        refine ⟨x, hx, ?_⟩
        simp only [GradedModule.homogeneousComponents, Finset.mem_image, DFinsupp.mem_support_toFun,
          ne_eq] at hi ⊢
        exact ⟨i, hi, rfl⟩
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_sup] at hx
        rcases hx with ⟨v, hv1, hv2⟩
        simp only [GradedModule.homogeneousComponents, Finset.mem_image, DFinsupp.mem_support_toFun,
          ne_eq, mem_coe] at hv2 ⊢
        rcases hv2 with ⟨i, _, rfl⟩
        rw [hs]
        exact p.2 _ <| hs ▸ Submodule.subset_span hv1
  · rintro ⟨s, _, hs1⟩
    rw [hs1]
    exact ⟨s, rfl⟩

variable {𝒜} in
lemma Ideal.fg_iff_homogeneously_fg : I.toIdeal.FG ↔ I.toIdeal.homogeneously_FG 𝒜 :=
  Submodule.fg_iff_homogeneously_fg I

end HomogeneouslyFG
