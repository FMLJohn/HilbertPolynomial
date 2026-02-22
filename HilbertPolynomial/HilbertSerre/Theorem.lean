/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import HilbertPolynomial.Module.Graded.Noetherian
import HilbertPolynomial.Module.Graded.Grading
import HilbertPolynomial.Module.FGModuleCat.Abelian
import HilbertPolynomial.HilbertSerre.AdditiveFunction
import HilbertPolynomial.HilbertSerre.FiniteInstances

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Module.Torsion

/-!
# Hilbert Serre Theorem

-/

universe u
variable {A M : Type u}
variable [CommRing A] [noetherian_ring : IsNoetherianRing A]
variable [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)
variable [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

open GradedRing.finite_algebra_over_degree_zero_subring
open GradedModule.finite_module_over_degree_zero_subring
open CategoryTheory CategoryTheory.Limits
open BigOperators
open PowerSeries

noncomputable instance : Abelian (FGModuleCat (𝒜 0)) :=
  letI := GradedRing.GradeZero.subring_isNoetherianRing_of_isNoetherianRing 𝒜
  FGModuleCat.abelian_of_noetherian (R := 𝒜 0)

variable (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)

namespace AdditiveFunction

/--
Let `A` be a graded ring and `M` a grade module over `A`. Let `μ` be an additive function from
category of finitely generated `A₀`-module, its Poincaré series is defined as the power series
`∑ᵢ μ(Mᵢ) Xⁱ ∈ ℤ⟦X⟧`.
-/
def poincareSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ μ <| .of _ <| (ℳ n : Type u)

lemma coeff_poincareSeries (n : ℕ) :
    PowerSeries.coeff _ n (μ.poincareSeries 𝒜 ℳ) = μ (.of _ <| ℳ n) := by
  delta poincareSeries
  rw [coeff_mk]


lemma map_subsingleton (x : FGModuleCat (𝒜 0)) [subsingleton : Subsingleton x] : μ x = 0 :=
  μ.eq_of_iso (IsZero.iso
    { unique_to := fun y ↦ ⟨⟨⟨0⟩, fun l ↦ by
        ext a
        simp only [show a = 0 from subsingleton.elim _ _, _root_.map_zero]⟩⟩
      unique_from := fun y ↦ ⟨⟨⟨0⟩, fun l ↦ by
        ext a

        exact subsingleton.elim _ _⟩⟩ } <| isZero_zero _)
  |>.trans μ.map_zero

end AdditiveFunction

/--
A finite collection of homogeneous elements that generates `A` over `A₀`.
-/
structure generatingSetOverBaseRing where
  /--
  A finite collection of homogeneous elements that generates `A` over `A₀`.
  -/
  toFinset : Finset A
  /--
  A finite collection of homogeneous elements with degree `dᵢ` that generates `A` over `A₀`.
  -/
  deg : ∀ {a : A}, a ∈ toFinset → ℕ
  mem_deg : ∀ {a : A} (h : a ∈ toFinset), a ∈ 𝒜 (deg h)
  deg_pos : ∀ {a : A} (h : a ∈ toFinset), 0 < deg h
  ne_zero' : ∀ {a : A}, a ∈ toFinset → a ≠ 0
  span_eq : Algebra.adjoin (𝒜 0) toFinset = (⊤ : Subalgebra (𝒜 0) A)

namespace generatingSetOverBaseRing

/--
The theorem we are proving is no vacuous, i.e. there is a generating set over base ring.
-/
@[simps]
noncomputable def fromHomogeneousGeneratingSetOfIrrelevant
    (s : GradedRing.HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    generatingSetOverBaseRing 𝒜 where
  toFinset := s.toFinset
  deg := s.deg
  mem_deg := s.mem_deg
  deg_pos := GradedRing.HomogeneousGeneratingSetOf.irrelevant.deg_pos s
  ne_zero' := s.ne_zero
  span_eq := GradedRing.HomogeneousGeneratingSetOf.irrelevant.adjoin_eq_top s

variable (S : generatingSetOverBaseRing 𝒜)

variable {𝒜} in
/--
Suppose `a₀, ..., aₙ` with degree `d₀, ..., dₙ`, we can consider the power series `∏ᵢ (1 - X^{dᵢ})`,
this power series is invertible, because its constant coefficient is one.
-/
@[simps] noncomputable def poles : ℤ⟦X⟧ˣ where
  val := ∏ i ∈ S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)
  inv := PowerSeries.invOfUnit (∏ i ∈ S.toFinset.attach, (1 - PowerSeries.X ^ S.deg i.2)) 1
  val_inv := PowerSeries.mul_invOfUnit _ _ <| by
    simp only [map_prod, map_sub, map_one, map_pow, constantCoeff_X, Units.val_one]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    rw [zero_pow, sub_zero]
    linarith [S.deg_pos i.2]
  inv_val := by
    rw [mul_comm]
    refine mul_invOfUnit _ _ ?_
    simp only [map_prod, map_sub, map_one, map_pow, constantCoeff_X, Units.val_one]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    rw [zero_pow, sub_zero]
    linarith [S.deg_pos i.2]

omit noetherian_ring in
lemma poles_val :
    S.poles.val =
    algebraMap (Polynomial ℤ) ℤ⟦X⟧ (∏ i ∈ S.toFinset.attach, (1 - Polynomial.X ^ S.deg i.2)) := by
  simp only [val_poles, HomogeneousIdeal.toIdeal_irrelevant, map_prod, map_sub, map_one, map_pow]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  congr
  simp only [algebraMap_apply', Algebra.id.map_eq_id, Polynomial.coe_X, map_X]

omit noetherian_ring in
lemma poles_inv_eq' :
    (↑S.poles⁻¹ : ℤ⟦X⟧) =
    ∏ i ∈ S.toFinset.attach, PowerSeries.invOfUnit (1 - PowerSeries.X ^ S.deg i.2) 1 := by
  rw [← Units.mul_eq_one_iff_inv_eq, val_poles, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  rintro ⟨i, hi⟩ -
  refine mul_invOfUnit _ _ ?_
  simp only [map_sub, map_one, map_pow, constantCoeff_X, Units.val_one, sub_eq_self,
    pow_eq_zero_iff', ne_eq, true_and]
  linarith [S.deg_pos hi]

end generatingSetOverBaseRing

namespace HilbertSerre

variable (S : generatingSetOverBaseRing 𝒜)

/--
statement of Hilbert-Serre theorem:
Let `A` be a notherian graded ring and `M` a finite graded module over `A` and `μ` an additive
function from the category of finitely generated `A₀`-modules.
If `a₀, ..., aₙ` with degree `dᵢ` generate `A` over `A₀`, then the Poincare series of `µ` is of the
form `p / ∏ᵢ (1 - X^{dᵢ})` where `p` is a polynomial in `ℤ[X]`.
-/
abbrev statement : Prop := ∃ (p : Polynomial ℤ), μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹

/--
statement of Hilber-Serre theorem. Only this form is used in induction.
(Implementation details)
-/
abbrev statement' (s : ℕ) : Prop :=
  ∀ (A M : Type u)
  [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  (𝒜 : ℕ → AddSubgroup A) (ℳ : ℕ → AddSubgroup M)
  [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
  (μ : (FGModuleCat (𝒜 0)) ⟹+ ℤ)
  (S : generatingSetOverBaseRing 𝒜) (_ : S.toFinset.card = s),
  ∃ (p : Polynomial ℤ), μ.poincareSeries 𝒜 ℳ = p • S.poles ⁻¹

lemma statement'_imp_statement (h : ∀ n, statement'.{u} n) : statement 𝒜 ℳ μ S :=
  h S.toFinset.card A M 𝒜 ℳ μ S rfl

section base_case

variable {𝒜}
variable (card_generator : S.toFinset.card = 0)

include card_generator in
lemma eventually_eq_zero_of_empty_generatorSet :
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ (x : ℳ n), x = 0 := by
  classical
  rw [Finset.card_eq_zero] at card_generator
  have eq1 := S.span_eq
  simp only [card_generator, Finset.coe_empty, Algebra.adjoin_empty] at eq1

  let S' := GradedRing.HomogeneousGeneratingSetOf.Irrelevant 𝒜
  have S'_eq : S'.toFinset = ∅ := by
    have eq2 := GradedRing.HomogeneousGeneratingSetOf.irrelevant.adjoin_eq_top S'
    rw [← eq1] at eq2
    by_contra r
    change S'.toFinset ≠ ∅ at r
    rw [← Finset.nonempty_iff_ne_empty] at r
    obtain ⟨s, hs⟩ := r
    have hs' : s ∈ (⊥ : Subalgebra (𝒜 0) A) := by
      rw [← eq2, Algebra.mem_adjoin_iff]
      exact Subring.subset_closure <| Or.inr hs
    obtain ⟨s, rfl⟩ := hs'
    change (s : A) ∈ S'.toFinset at hs
    have eq3 := DirectSum.degree_eq_of_mem_mem (ℳ := 𝒜) s.2 (S'.mem_deg hs) (S'.ne_zero' hs)
    have ineq1 : 0 < S'.deg hs := GradedRing.HomogeneousGeneratingSetOf.irrelevant.deg_pos S' hs
    linarith only [eq3, ineq1]
  let T := GradedModule.HomogeneousGeneratingSetOf.Top A ℳ
  let deg : T.toFinset → ℕ := fun x ↦ T.deg x.2
  by_cases ne_empty : T.toFinset = ∅
  · refine ⟨1, fun n _ x ↦ ?_⟩
    have eq2 := T.span_eq
    rw [ne_empty] at eq2
    simp only [Finset.coe_empty, Submodule.span_empty] at eq2
    have mem1 : (x : M) ∈ (⊤ : Submodule A M) := ⟨⟩
    rw [← eq2] at mem1
    ext
    exact mem1

  let maxDeg : ℕ := Finset.image deg Finset.univ |>.max' (by
    simp only [Finset.univ_eq_attach, Finset.image_nonempty, Finset.attach_nonempty_iff]
    rw [Finset.nonempty_iff_ne_empty]
    exact ne_empty)

  refine ⟨maxDeg, fun n hn x ↦ ?_⟩
  have hn' (m : M) (hm : m ∈ T.toFinset) : T.deg hm < n :=
    lt_of_le_of_lt (Finset.le_max' _ _ <| by
      simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists, T] at hm ⊢
      exact ⟨m, hm, rfl⟩) hn

  have eq0 := kth_degree_eq_span S' T n
  replace card_generator : (GradedRing.HomogeneousGeneratingSetOf.Irrelevant 𝒜).toFinset = ∅ :=
    S'_eq
  change S'.toFinset = ∅ at card_generator
  simp_rw [card_generator, Finset.subset_empty, Finsupp.support_eq_empty] at eq0
  replace eq0 := calc _
    _ = _ := eq0
    _ = Submodule.span (𝒜 0) {x : ℳ n | ∃ ω : M, ∃ (_ : ω ∈ T.toFinset), x = ω } := by
        congr
        ext x
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
        refine exists_congr fun m ↦ exists_congr fun _ ↦ ⟨?_, ?_⟩
        · rintro ⟨_, rfl, -, h⟩; rwa [evalMonomial_zero, one_smul] at h
        · intro h
          refine ⟨_, rfl, ?_, h ▸ ?_⟩
          · erw [degreeMonomial_zero]; norm_num
          · rw [evalMonomial_zero, one_smul]
    _ = Submodule.span (𝒜 0) {x : ℳ n | (x : M) ∈ T.toFinset } := by
        congr
        ext x
        simp only [exists_prop, exists_eq_right', Set.mem_setOf_eq]
  have mem1 : x ∈ (⊤ : Submodule (𝒜 0) (ℳ n)) := ⟨⟩
  rw [eq0, mem_span_set] at mem1
  obtain ⟨f, support_le, (eq1 : ∑ i ∈ f.support, f i • i = x)⟩ := mem1
  rw [Subtype.ext_iff, AddSubgroup.val_finset_sum] at eq1
  ext1
  rw [show (x : M) = GradedModule.proj ℳ n x from
    DirectSum.decompose_of_mem_same (hx := x.2) |>.symm, ← eq1, map_sum, AddSubgroup.coe_zero]
  refine Finset.sum_eq_zero fun x hx ↦ show GradedModule.proj ℳ n ((f x : A) • (x : M)) = 0 from ?_

  rw [GradedModule.proj_smul_mem_right 𝒜 ℳ (f x : A) (x : M) (T.mem_deg (support_le hx)),
    if_pos (le_of_lt <| hn' x (support_le hx)), GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne (hx := (f x).2), zero_smul]

  intro r
  rw [eq_comm, Nat.sub_eq_zero_iff_le] at r
  exact not_le_of_lt (hn' x (support_le hx)) r

include card_generator in
lemma eventually_subsingleton_of_empty_generatorSet :
    ∃ N : ℕ, ∀ n : ℕ, N < n → Subsingleton (ℳ n) := by
  obtain ⟨N, h⟩ := eventually_eq_zero_of_empty_generatorSet ℳ S card_generator
  exact ⟨N, fun n hn ↦ ⟨fun x y ↦ (h n hn x).trans (h n hn y).symm⟩⟩

lemma proof.base_case : statement'.{u} 0 := by
  intro A M _ _ _ _ _ 𝒜 ℳ _ _ _ μ S card_generator
  obtain ⟨N, hN⟩ := eventually_subsingleton_of_empty_generatorSet ℳ S card_generator
  classical
  rw [Finset.card_eq_zero] at card_generator

  refine ⟨(μ.poincareSeries 𝒜 ℳ).trunc (N + 1), ?_⟩
  rw [Algebra.smul_def, eq_comm, Units.mul_inv_eq_iff_eq_mul, eq_comm]
  convert mul_one _
  · simp only [generatingSetOverBaseRing.val_poles]
    convert Finset.prod_empty
    simp only[Finset.attach_eq_empty_iff, card_generator]

  · ext n
    simp only [algebraMap_apply', Algebra.id.map_eq_id, map_id, id_eq, Polynomial.coeff_coe,
      coeff_trunc, AdditiveFunction.poincareSeries, coeff_mk]
    by_cases hn : N < n
    · rw [if_neg (by linarith), eq_comm]
      exact μ.map_subsingleton (subsingleton := hN _ hn)
    · rw [if_pos]
      linarith

end base_case

namespace induction.constructions

variable {𝒜}
variable {d : ℕ} (x : A) (deg_x : x ∈ 𝒜 d)

/--
Let `x` be a homogeneous element, then the set of elements annilaited by `x` (i,e `x • m = 0`) forms
a homogeneous submodule. Denote this module as `K`
-/
def KER : HomogeneousSubmodule A ℳ where
  carrier := {m : M | x • m = 0 }
  add_mem' := by aesop
  zero_mem' := by aesop
  smul_mem' := by intros; simp only [Set.mem_setOf_eq]; rw [smul_comm]; aesop
  is_homogeneous' i m (h : x • m = 0) := show x • _ = 0 by
    have := GradedModule.proj_smul_mem_left (j := i + d) 𝒜 ℳ x m deg_x
    rw [h, if_pos (by linarith), map_zero, GradedModule.proj_apply, Nat.add_sub_cancel] at this
    exact this.symm

omit [Module.Finite A M] noetherian_ring in
lemma mem_KER_iff (a : M) : a ∈ KER ℳ x deg_x ↔ x • a = 0 := Iff.rfl

instance [(i : ℕ) → (x : ↥(ℳ i)) → Decidable (x ≠ 0)] [(a : M) → Decidable (a ∈ KER ℳ x deg_x)] : DirectSum.Decomposition (KER ℳ x deg_x).grading :=
  (KER ℳ x deg_x).decomposition

open Pointwise

/--
(Implementation details)
x • M is also a homogeneous submodule, so we can take the quotient modue `M ⧸ x • M` with its
quotient grading as a grade module over `A`.
-/
abbrev COKER.den : HomogeneousSubmodule A ℳ :=
{ toSubmodule := x • (⊤ : Submodule A M)
  is_homogeneous' := by
    intro i m hm
    obtain ⟨m, -, rfl⟩ := hm
    refine ⟨if d ≤ i then GradedModule.proj ℳ (i - d) m else 0, trivial, ?_⟩
    show x • _ = GradedModule.proj ℳ i (x • m)
    rw [GradedModule.proj_smul_mem_left 𝒜 ℳ x m deg_x]
    split_ifs <;> aesop }

/--
`M ⧸ x • M` has a quotient grading when `x` is homogeneous. Dentoe this module as `L`
-/
abbrev COKER := M ⧸ (COKER.den ℳ x deg_x).toSubmodule

instance : DirectSum.Decomposition (COKER.den ℳ x deg_x).quotientGrading :=
  HomogeneousSubmodule.quotientDecomposition _

instance : SetLike.GradedSMul 𝒜 (COKER.den ℳ x deg_x).quotientGrading :=
  HomogeneousSubmodule.quotientGradedSMul _

/--
The `A₀`-linear map `Kₙ → Mₙ`.
-/
@[simps]
def KER.componentEmb (n : ℕ) : (KER ℳ x deg_x).grading n →ₗ[𝒜 0] ℳ n where
  toFun a := ⟨a.1, a.2⟩
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

/--
The `A₀`-linear map `Mₙ → M_{n + d}` defined by scalar action `x • ⬝` where `x` is a homogeneous
element of degree `d`.
-/
@[simps]
def smulBy (n : ℕ) : ℳ n →ₗ[𝒜 0] ℳ (d + n) where
  toFun m := ⟨x • m, SetLike.GradedSMul.smul_mem deg_x m.2⟩
  map_add' := by aesop
  map_smul' r m := Subtype.ext <|
    show (x : A) • (r : A) • (m : M) = (r : A) • (x : A) • (m : M) from smul_comm _ _ _

instance (n : ℕ) : Module (𝒜 0) ((COKER.den ℳ x deg_x).quotientGrading n) :=
DirectSum.GradeZero.module_at_i 𝒜 (COKER.den ℳ x deg_x).quotientGrading n

/--
The `A₀`-linear map `Mₙ → Lₙ`
-/
def COKER.descComponent (n : ℕ) :
    ℳ n →ₗ[𝒜 0] (COKER.den ℳ x deg_x).quotientGrading n where
  toFun m := ⟨Quotient.mk'' m, by
    simp only [Submodule.Quotient.mk''_eq_mk, HomogeneousSubmodule.quotientGrading,
      HomogeneousSubmodule.quotientGradingEmb, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup, AddMonoidHom.mem_range]
    use m
    erw [QuotientAddGroup.map_mk']
    rfl  ⟩
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

-- `0 -> KERₘ -> ℳₙ` is exact
omit [Module.Finite A M] noetherian_ring in
lemma KER.componentEmb_injective (n : ℕ) : Function.Injective (KER.componentEmb ℳ x deg_x n) := by
  intros a b h
  ext
  rw [Subtype.ext_iff, componentEmb_apply_coe, componentEmb_apply_coe] at h
  exact h

-- `KERₙ -> ℳₙ -> ℳ_{d + n}` is exact
omit [Module.Finite A M] noetherian_ring in
lemma exact_KERComponentEmb_smulBy (n : ℕ) :
    LinearMap.range (KER.componentEmb ℳ x deg_x n) = LinearMap.ker (smulBy ℳ x deg_x n) := by
  ext m
  fconstructor
  · rintro ⟨⟨⟨m, (hm1 : x • m = 0)⟩, (hm2 : m ∈ ℳ n)⟩, rfl⟩
    simp only [LinearMap.mem_ker]
    ext
    simpa only [smulBy_apply_coe, KER.componentEmb_apply_coe, ZeroMemClass.coe_zero]
  · intro hm
    simp only [LinearMap.mem_ker, Subtype.ext_iff, smulBy_apply_coe, ZeroMemClass.coe_zero] at hm
    exact ⟨⟨⟨m, hm⟩, m.2⟩, rfl⟩

-- `ℳₙ -> ℳ_{d + n} -> COKER_{d + n}` is exact
omit [Module.Finite A M] noetherian_ring in
lemma exact_smulBy_COKERDescComponent (n : ℕ) :
    LinearMap.range (smulBy ℳ x deg_x n) =
    LinearMap.ker (COKER.descComponent ℳ x deg_x (d + n)) := by
  ext m
  fconstructor
  · rintro ⟨m, rfl⟩
    simp only [LinearMap.mem_ker]
    ext
    erw [QuotientAddGroup.eq_zero_iff]
    simp only [smulBy_apply_coe, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup]
    exact ⟨m, trivial, rfl⟩
  · intro hm
    erw [LinearMap.mem_ker, Subtype.ext_iff, QuotientAddGroup.eq_zero_iff] at hm
    obtain ⟨m', -, (hm' : x • m' = m.1)⟩ := hm
    refine ⟨⟨(DirectSum.decompose ℳ m' n), SetLike.coe_mem _⟩, ?_⟩
    ext
    simp only [Subtype.coe_eta, smulBy_apply_coe]
    have eq0 := GradedModule.proj_smul_mem_left (j := d + n) 𝒜 ℳ x m' deg_x
    rwa [if_pos (by linarith), GradedModule.proj_apply, GradedModule.proj_apply, add_comm,
      Nat.add_sub_cancel, DirectSum.decompose_of_mem_same, hm', eq_comm] at eq0
    convert m.2 using 1
    rw [add_comm]

/--
relabelling `Mᵢ` to `M_{d + (i - d)}` and vice versa.
-/
@[simps]
def reindex (i : ℕ) (ineq : d ≤ i) : (ℳ (d + (i - d))) ≃ₗ[(𝒜 0)] (ℳ i) where
  toFun m := ⟨m.1, by convert m.2; omega⟩
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  invFun m := ⟨m.1, by convert m.2; omega⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

omit [Module.Finite A M] noetherian_ring in
lemma exact_smulBy_COKERDescComponent' (n : ℕ) (ineq : d ≤ n) :
    LinearMap.range ((reindex ℳ n ineq).toLinearMap ∘ₗ (smulBy ℳ x deg_x (n - d))) =
    LinearMap.ker (COKER.descComponent ℳ x deg_x n) := by
  rw [LinearMap.range_comp, exact_smulBy_COKERDescComponent]
  ext m
  simp only [Submodule.mem_map_equiv, LinearMap.mem_ker]
  fconstructor <;> intro h <;> erw [Subtype.ext_iff, QuotientAddGroup.eq_zero_iff] at h ⊢ <;>
  simp only [reindex_symm_apply_coe, Submodule.pointwise_smul_toAddSubgroup,
    Submodule.top_toAddSubgroup] at h ⊢ <;>
  exact h

omit [Module.Finite A M] noetherian_ring in
lemma COKER.descComponent_surjective (n : ℕ) :
    Function.Surjective (COKER.descComponent ℳ x deg_x (d + n)) := by
  rintro ⟨_, ⟨m, rfl⟩⟩
  induction' m using Quotient.inductionOn' with m
  exact ⟨m, rfl⟩

omit [Module.Finite A M] noetherian_ring in
lemma COKER.descComponent_surjective' (n : ℕ) :
    Function.Surjective (COKER.descComponent ℳ x deg_x n) := by
  rintro ⟨_, ⟨m, rfl⟩⟩
  induction' m using Quotient.inductionOn' with m
  exact ⟨m, rfl⟩

open CategoryTheory CategoryTheory.Limits ZeroObject

variable [(i : ℕ) → (x : (ℳ i)) → Decidable (x ≠ 0)] [(a : M) → Decidable (a ∈ KER ℳ x deg_x)]

instance : Module.Finite A (KER ℳ x deg_x) := by
  change Module.Finite A (KER ℳ x deg_x).toSubmodule
  rw [Module.Finite.iff_fg]
  apply IsNoetherian.noetherian

instance (n : ℕ) : Module.Finite (𝒜 0) ((KER ℳ x deg_x).grading n) :=
  GradedModule.finite_module_over_degree_zero_subring _ _ _

set_option maxHeartbeats 500000 in
/--
The exact sequence
`0 → Kₙ → Mₙ → M_{n + d} → L_{n + d}`
more accurately
`0 → K_{n - d} → M_{n - d} → Mₙ → Lₙ`
-/
@[simps!]
noncomputable def anExactSeq (i : ℕ) (ineq : d ≤ i) : ComposableArrows (FGModuleCat (𝒜 0)) 5 :=
  .mk₅
    (0 : 0 ⟶ FGModuleCat.of _ <| (KER ℳ x deg_x).grading (i - d))
    (FGModuleCat.ofHom (KER.componentEmb ℳ x deg_x (i - d)) :
      FGModuleCat.of _ ((KER ℳ x deg_x).grading (i - d)) ⟶ FGModuleCat.of _ (ℳ (i - d)))
    (FGModuleCat.asHom (smulBy ℳ x deg_x (i - d)) ≫ (reindex ℳ i ineq).toFGModuleCatIso.hom :
      FGModuleCat.of _ (ℳ (i - d)) ⟶ FGModuleCat.of _ (ℳ i))
    (FGModuleCat.asHom (COKER.descComponent ℳ x deg_x i) :
      FGModuleCat.of _ (ℳ i) ⟶ FGModuleCat.of _ ((COKER.den ℳ x deg_x).quotientGrading i))
    (0 : FGModuleCat.of _ ((COKER.den ℳ x deg_x).quotientGrading i) ⟶ 0)

example : true := rfl

lemma anExactSeq_complex (i : ℕ) (ineq : d ≤ i) : (anExactSeq ℳ x deg_x i ineq).IsComplex := by
  constructor
  rintro j (hj : j + 2 ≤ 5)
  replace hj : j ≤ 3 := by linarith
  interval_cases j
  · ext m
    simp only [Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Nat.cast_ofNat, anExactSeq_obj,
      ComposableArrows.Precomp.obj_succ, ComposableArrows.precomp_obj, Fin.mk_one,
      ComposableArrows.Precomp.obj_one, Fin.zero_eta, ComposableArrows.Precomp.obj_zero,
      ComposableArrows.map', anExactSeq_map, ComposableArrows.Precomp.map_zero_one',
      ComposableArrows.Precomp.map_succ_succ, ComposableArrows.precomp_map,
      ComposableArrows.Precomp.map_zero_one, zero_comp]
  · ext m
    simp only [Nat.reduceAdd, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceSub,
      Int.Nat.cast_ofNat_Int, Int.reduceAdd, Fin.reduceFinMk, anExactSeq_obj, Fin.isValue,
      FGModuleCat.obj_carrier, Fin.mk_one, ComposableArrows.Precomp.obj_one,
      ComposableArrows.precomp_obj, Fin.zero_eta, ComposableArrows.Precomp.obj_zero,
      ComposableArrows.map', homOfLE_leOfHom, anExactSeq_map, FGModuleCat.hom_comp,
      LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_zero]
    refine Subtype.ext ?_
    change (smulBy ℳ x deg_x _ (KER.componentEmb ℳ x deg_x _ m) : M) = 0
    simp only [smulBy_apply_coe, KER.componentEmb_apply_coe, Submodule.smul_coe_torsionBy]
  · ext m
    simp only [Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Nat.cast_ofNat, anExactSeq_obj,
      ComposableArrows.Precomp.obj_succ, ComposableArrows.precomp_obj, Fin.mk_one,
      ComposableArrows.Precomp.obj_one, ComposableArrows.mk₁_obj, Fin.zero_eta,
      ComposableArrows.Mk₁.obj, ComposableArrows.Precomp.obj_zero, ComposableArrows.map',
      anExactSeq_map, ComposableArrows.Precomp.map_succ_succ, ComposableArrows.precomp_map,
      ComposableArrows.Precomp.map_one_succ, ComposableArrows.Precomp.map_zero_one, Category.assoc]
    change COKER.descComponent ℳ x deg_x i (reindex ℳ i ineq (smulBy ℳ x deg_x _ m)) = 0
    ext
    erw [QuotientAddGroup.eq_zero_iff]
    simp only [reindex_apply_coe, smulBy_apply_coe, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup]
    refine ⟨m.1, trivial, rfl⟩
  · ext m
    simp only [Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Nat.cast_ofNat, anExactSeq_obj,
      ComposableArrows.Precomp.obj_succ, ComposableArrows.precomp_obj, ComposableArrows.mk₁_obj,
      Fin.mk_one, ComposableArrows.Mk₁.obj, ComposableArrows.Precomp.obj_one, Fin.zero_eta,
      ComposableArrows.Precomp.obj_zero, ComposableArrows.map', anExactSeq_map,
      ComposableArrows.Precomp.map_succ_succ, ComposableArrows.precomp_map,
      ComposableArrows.Precomp.map_one_succ, ComposableArrows.Precomp.map_zero_one,
      ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, comp_zero]

set_option synthInstance.maxHeartbeats 40000 in
lemma anExactSeq_exact₀ (i : ℕ) (ineq : d ≤ i) :
    (anExactSeq ℳ x deg_x i ineq).sc (anExactSeq_complex ℳ x deg_x i ineq) 0 |>.Exact := by
  rw [FGModuleCat.exact_iff]
  simp only [Nat.reduceAdd, id_eq, Int.reduceNeg, Nat.cast_ofNat, Int.reduceAdd, Int.reduceSub,
    Fin.mk_one, Fin.isValue, anExactSeq_obj, ComposableArrows.Precomp.obj_one,
    Int.Nat.cast_ofNat_Int, ComposableArrows.precomp_obj, Fin.zero_eta,
    ComposableArrows.Precomp.obj_zero, FGModuleCat.obj_carrier, ComposableArrows.map',
    homOfLE_leOfHom, anExactSeq_map, ComposableArrows.Precomp.map_zero_one, ModuleCat.hom_zero,
    LinearMap.range_zero, Fin.reduceFinMk]
  rw [eq_comm, LinearMap.ker_eq_bot]
  exact KER.componentEmb_injective ℳ x deg_x _

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 400000 in
lemma anExactSeq_exact₁ (i : ℕ) (ineq : d ≤ i) :
    (anExactSeq ℳ x deg_x i ineq).sc (anExactSeq_complex ℳ x deg_x i ineq) 1 |>.Exact := by
  rw [FGModuleCat.exact_iff']
  change Function.Exact (FGModuleCat.ofHom (KER.componentEmb ℳ x deg_x (i - d))).hom
    ((reindex ℳ i ineq).toFGModuleCatIso.hom.hom ∘ₗ (smulBy ℳ x deg_x (i - d)))
  erw [Function.Injective.comp_exact_iff_exact]
  · rw [LinearMap.exact_iff]
    exact exact_KERComponentEmb_smulBy ℳ x deg_x _ |>.symm
  · rw [← FGModuleCat.mono_iff_injective]
    infer_instance

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 800000 in
lemma anExactSeq_exact₂ (i : ℕ) (ineq : d ≤ i) :
    (anExactSeq ℳ x deg_x i ineq).sc (anExactSeq_complex ℳ x deg_x i ineq) 2 |>.Exact := by
  rw [FGModuleCat.exact_iff']
  change Function.Exact
    ((reindex ℳ i ineq).toFGModuleCatIso.hom.hom ∘ₗ (smulBy ℳ x deg_x (i - d)))
    ((COKER.descComponent ℳ x deg_x i))
  erw [LinearMap.exact_iff]
  exact exact_smulBy_COKERDescComponent' ℳ x deg_x i ineq |>.symm

set_option synthInstance.maxHeartbeats 40000 in
set_option maxHeartbeats 800000 in
lemma anExactSeq_exact₃ (i : ℕ) (ineq : d ≤ i) :
    (anExactSeq ℳ x deg_x i ineq).sc (anExactSeq_complex ℳ x deg_x i ineq) 3 |>.Exact := by
  rw [FGModuleCat.exact_iff]
  simp only [anExactSeq, LinearEquiv.toFGModuleCatIso_hom, ComposableArrows.mk₅,
    ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂, Nat.reduceAdd, id_eq,
    Int.reduceNeg, Nat.cast_ofNat, Int.reduceAdd, Int.reduceSub, Fin.reduceFinMk,
    ComposableArrows.precomp_obj, Fin.isValue, FGModuleCat.obj_carrier, ComposableArrows.map',
    homOfLE_leOfHom, ComposableArrows.precomp_map, ComposableArrows.Precomp.map, Fin.mk_one,
    Fin.zero_eta, ComposableArrows.mk₁_map, ComposableArrows.Mk₁.map, ModuleCat.hom_zero,
    LinearMap.ker_zero, LinearMap.range_eq_top]
  apply COKER.descComponent_surjective'

set_option maxHeartbeats 1000000 in
lemma anExactSeq_exact (i : ℕ) (ineq : d ≤ i) : (anExactSeq ℳ x deg_x i ineq).Exact := by
  letI := GradedRing.GradeZero.subring_isNoetherianRing_of_isNoetherianRing 𝒜
  fconstructor
  · apply anExactSeq_complex
  rintro j (hj : j + 2 ≤ 5)
  replace hj : j ≤ 3 := by omega
  interval_cases j
  · apply anExactSeq_exact₀
  · apply anExactSeq_exact₁
  · apply anExactSeq_exact₂
  · apply anExactSeq_exact₃

example : true := rfl

lemma key_lemma :
    ∃ (p : Polynomial ℤ),
      (1 - PowerSeries.X ^ d) * μ.poincareSeries 𝒜 ℳ =
      μ.poincareSeries 𝒜 (COKER.den ℳ x deg_x).quotientGrading -
      PowerSeries.X ^ d * μ.poincareSeries 𝒜 (KER ℳ x deg_x).grading + algebraMap _ ℤ⟦X⟧ p := by
  set p : Polynomial ℤ :=
    (μ.poincareSeries 𝒜 ℳ).trunc d -
    (μ.poincareSeries 𝒜 (COKER.den ℳ x deg_x).quotientGrading).trunc d
  use p
  rw [sub_mul, one_mul]
  ext i
  simp only [map_sub, AdditiveFunction.coeff_poincareSeries, coeff_mul, coeff_X_pow, ite_mul,
    one_mul, zero_mul, map_add, p]
  have eq0 (q : ℤ⟦X⟧) : coeff _ i (algebraMap _ ℤ⟦X⟧ (q.trunc d)) =
      if i < d then coeff _ i q else 0 := by
    rw [show algebraMap (Polynomial ℤ) ℤ⟦X⟧ = (Polynomial.coeToPowerSeries.algHom (R := ℤ) ℤ) from
      rfl]
    simp only [RingHom.coe_coe, Polynomial.coeToPowerSeries.algHom_apply, Algebra.id.map_eq_id,
      map_id, id_eq, Polynomial.coeff_coe]
    rw [coeff_trunc]
  rw [eq0, eq0]

  have eq1 :
    ∑ x ∈ Finset.antidiagonal i, (if x.1 = d then μ (.of (𝒜 0) (ℳ x.2)) else 0)=
    if d ≤ i then μ (.of _ (ℳ (i - d))) else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    split_ifs with ineq
    · trans ∑ x ∈ {(d, i - d)}, μ (.of (𝒜 0) (ℳ x.2))
      · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
        ext ⟨j, k⟩
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.mk.injEq]
        fconstructor <;> rintro ⟨rfl, rfl⟩ <;> omega
      · rw [Finset.sum_singleton]
    · convert Finset.sum_empty
      ext ⟨j, k⟩
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.not_mem_empty, iff_false,
        not_and]
      rintro rfl rfl
      simp only [le_add_iff_nonneg_right, zero_le, not_true_eq_false] at ineq
  rw [eq1]

  have eq2 : ∑ jk ∈ Finset.antidiagonal i,
        (if jk.1 = d then μ (.of _ ((KER ℳ x deg_x).grading jk.2)) else 0) =
      if d ≤ i then μ (.of _ ((KER ℳ x deg_x).grading (i - d))) else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    split_ifs with ineq
    · trans ∑ jk ∈ {(d, i - d)}, μ (.of _ ((KER ℳ x deg_x).grading jk.2))
      · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
        ext ⟨j, k⟩
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton, Prod.mk.injEq]
        fconstructor <;> rintro ⟨rfl, rfl⟩ <;> omega
      · rw [Finset.sum_singleton]
    · convert Finset.sum_empty
      ext ⟨j, k⟩
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.not_mem_empty, iff_false,
        not_and]
      rintro rfl rfl
      simp only [le_add_iff_nonneg_right, zero_le, not_true_eq_false] at ineq
  rw [eq2]

  by_cases ineq : d ≤ i
  · rw [if_pos ineq, if_pos ineq, if_neg (by linarith), if_neg (by linarith), sub_zero, add_zero]
    have := μ.alternating_sum_apply_eq_zero_of_zero_zero_of_length6' _
      (anExactSeq_exact ℳ x deg_x i ineq) (isZero_zero _) (isZero_zero _)
    simp only [ComposableArrows.obj', Fin.mk_one, anExactSeq_obj, ComposableArrows.Precomp.obj_one,
      Fin.zero_eta, ComposableArrows.precomp_obj, ComposableArrows.Precomp.obj_zero,
      ComposableArrows.Precomp.obj_succ, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj] at this
    rw [sub_eq_zero] at this
    rw [← this, sub_eq_iff_eq_add]
    ring
  · rw [if_neg ineq, if_neg ineq, if_pos (by linarith), if_pos (by linarith), sub_zero, sub_zero,
      AdditiveFunction.coeff_poincareSeries, AdditiveFunction.coeff_poincareSeries]
    abel

/--
Add homogeneous elements to a ring gives a homogeneous ring.
-/
def adjoinHomogeneous (S : Finset A) (hS : ∀ a ∈ S, SetLike.IsHomogeneousElem 𝒜 a) :
    HomogeneousSubring 𝒜 where
  __ :=  (Algebra.adjoin (𝒜 0) S : Subalgebra (𝒜 0) A).toSubring
  is_homogeneous' := by
    intro i a h
    simp only [Subalgebra.mem_toSubring, Algebra.mem_adjoin_iff] at h ⊢
    refine Subring.homogeneous_closure 𝒜 (Set.range (algebraMap (𝒜 0) A) ∪ S) ?_ i h
    rintro x (⟨x, rfl⟩|hx)
    · exact ⟨0, SetLike.coe_mem _⟩
    · exact hS _ hx

section

variable [DecidableEq A]
variable (N : ℕ) (card : S.toFinset.card = N + 1)
variable (x : A) (x_not_mem : x ∈ S.toFinset) (S' : Finset A) (hS' : insert x S' = S.toFinset)
variable (d : ℕ) (deg_x : x ∈ 𝒜 d)

/--
If `A = A₀[S, s]`, define `A'` as `A₀[S]`
-/
abbrev A' : HomogeneousSubring 𝒜 := induction.constructions.adjoinHomogeneous S' fun _ h ↦
  ⟨S.deg (hS' ▸ Finset.mem_insert_of_mem h), S.mem_deg _⟩

omit noetherian_ring in
lemma mem_A' (a : A) : a ∈ A' S x S' hS' ↔ a ∈ Algebra.adjoin (𝒜 0) S' := Iff.rfl

instance noetherian_A' : IsNoetherianRing (A' S x S' hS') :=
  letI := GradedRing.GradeZero.subring_isNoetherianRing_of_isNoetherianRing 𝒜
  Algebra.adjoin_isNoetherian (R := 𝒜 0) S'

/--
If `A = A₀[S, s]`, define `A'` as `A₀[S]`. Then `A'` has grading defined by `n`-th grading being
`Aₙ ∩ A₀[S]`.
-/
abbrev 𝒜' : ℕ → AddSubgroup (A' S x S' hS') := (A' S x S' hS').grading

variable [(a : A) → Decidable (a ∈ A' S x S' hS')]

instance gradedRing_A' : GradedRing (𝒜' S x S' hS') :=
  HomogeneousSubring.gradedRing (A' S x S' hS')

instance noetherian_A'_zero : IsNoetherianRing (𝒜' S x S' hS' 0) := by
  apply GradedRing.GradeZero.subring_isNoetherianRing_of_isNoetherianRing

noncomputable instance abelian_A'_zero : CategoryTheory.Abelian (FGModuleCat (𝒜' S x S' hS' 0)) :=
  letI := GradedRing.GradeZero.subring_isNoetherianRing_of_isNoetherianRing $ 𝒜' S x S' hS'
  FGModuleCat.abelian_of_noetherian

instance finite_KER : Module.Finite (A' S x S' hS') (KER ℳ x deg_x).toSubmodule :=
  Algebra.adjoin_module_finite_of_annihilating (𝒜 0) A S' x
    (by rw [← S.span_eq, ← hS', Finset.coe_insert]) (KER ℳ x deg_x).toSubmodule
    fun x ↦ by ext; exact x.2

instance finite_COKER : Module.Finite (A' S x S' hS') (COKER ℳ x deg_x) := by
  refine Algebra.adjoin_module_finite_of_annihilating (𝒜 0) A S' x
    (by rw [← S.span_eq, ← hS', Finset.coe_insert]) (COKER ℳ x deg_x) fun x ↦ ?_
  induction' x using Quotient.inductionOn' with x
  erw [Submodule.Quotient.eq', add_zero]
  refine ⟨-x, trivial, ?_⟩
  simp only [map_neg, DistribMulAction.toLinearMap_apply]

instance gradedModule_KER :
    SetLike.GradedSMul (𝒜' S x S' hS') (HomogeneousSubmodule.grading (KER ℳ x deg_x)) where
  smul_mem {_ _ _ _} ha hb := (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem ha hb

instance gradedModule_COKER :
    SetLike.GradedSMul (𝒜' S x S' hS') (COKER.den ℳ x deg_x).quotientGrading where
  smul_mem {i j a b} (ha : (a : A) ∈ 𝒜 i) hb := by
    obtain ⟨b, rfl⟩ := hb
    induction' b using Quotient.inductionOn' with b
    erw [vadd_eq_add, QuotientAddGroup.map_mk']
    exact ⟨Quotient.mk''
      ⟨(a : A) • (b : M), (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem ha b.2⟩, rfl⟩

/--
The degree zero part of `A` and `A'` agrees.
-/
@[simps]
def AZeroToA'Zero : 𝒜 0 →+* 𝒜' S x S' hS' 0 where
  toFun := fun x ↦ ⟨⟨(x : A), by
    rw [mem_A', Algebra.mem_adjoin_iff]
    exact Subring.subset_closure <| Or.inl ⟨x, rfl⟩⟩, x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intros; ext; rfl
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

/--
The degree zero part of `A'` and `A` agrees.
-/
@[simps]
def A'ZeroToAZero : 𝒜' S x S' hS' 0 →+* 𝒜 0 where
  toFun := fun x ↦ ⟨x.1, x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intros; ext; rfl
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl

omit noetherian_ring [(a : A) → Decidable (a ∈ A' S x S' hS')] in
lemma A'ZeroToAZero_comp_AZeroToA'Zero :
    (A'ZeroToAZero S x S' hS').comp (AZeroToA'Zero S x S' hS') = RingHom.id (𝒜 0) := by
  ext ⟨x, hx⟩
  simp

omit noetherian_ring [(a : A) → Decidable (a ∈ A' S x S' hS')] in
lemma AZeroToA'Zero_comp_A'ZeroToAZero :
    (AZeroToA'Zero S x S' hS').comp (A'ZeroToAZero S x S' hS') = RingHom.id (𝒜' S x S' hS' 0) := by
  ext ⟨⟨x, hx1⟩, hx2⟩
  rw [RingHom.comp_apply, AZeroToA'Zero_apply_coe_coe, RingHom.id_apply,
    A'ZeroToAZero_apply_coe]

/--
The degree zero part of `A'` and `A` agrees.
-/
@[simps!]
def AZeroEquivA'Zero : 𝒜 0 ≃+* 𝒜' S x S' hS' 0 :=
  RingEquiv.ofHomInv (AZeroToA'Zero S x S' hS') (A'ZeroToAZero S x S' hS')
    (A'ZeroToAZero_comp_AZeroToA'Zero S x S' hS')
    (AZeroToA'Zero_comp_A'ZeroToAZero S x S' hS')

/--
Since the degree zero part of `A'` and `A` agrees. any additive `μ` from finitely generated `Aₒ`
modules gaves an additive function from finitely generated `A'₀` modules.
-/
noncomputable def μ' : FGModuleCat (𝒜' S x S' hS' 0) ⟹+ ℤ :=
  μ.pushforward <| RingEquiv.toFGModuleCatEquivalence <| AZeroEquivA'Zero S x S' hS'

/--
If `A = A₀[S, s]`, define `A'` as `A₀[S]`, then `S` generates `A₉[S]` over `A₀`.
-/
@[simps]
def generatingSet' : generatingSetOverBaseRing (𝒜' S x S' hS') where
  toFinset := S'.attach.image fun x : S' ↦ ⟨x, by
    rw [mem_A', Algebra.mem_adjoin_iff]
    refine Subring.subset_closure <| Or.inr x.2⟩
  deg {x} hx := S.deg (by
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hS' ▸ Finset.mem_insert_of_mem ha : (x : A) ∈ S.toFinset)
  mem_deg _ := S.mem_deg _
  deg_pos _ := S.deg_pos _
  ne_zero' h := by
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at h
    obtain ⟨a, ha, rfl⟩ := h
    suffices h : a ≠ 0 by
      contrapose! h
      rw [Subtype.ext_iff] at h
      exact h
    exact S.ne_zero' (hS' ▸ Finset.mem_insert_of_mem ha)
  span_eq := by
    refine le_antisymm ?_ ?_
    · intro x _
      simp only [Algebra.mem_top]
    rintro ⟨a, ha⟩ -
    rw [mem_A', Algebra.mem_adjoin_iff, Subring.mem_closure] at ha
    rw [Algebra.mem_adjoin_iff, Subring.mem_closure]
    intros R hR
    specialize ha (R.map (A' S x S' hS').toSubring.subtype) (by
      simp only [Finset.coe_image, Set.union_subset_iff, Set.image_subset_iff, Subring.coe_map,
        Subring.coe_subtype] at hR ⊢
      constructor
      · rintro _ ⟨a, rfl⟩
        let a' : 𝒜' S x S' hS' 0 := ⟨⟨(a : A), by
          erw [mem_A', Algebra.mem_adjoin_iff]
          refine Subring.subset_closure <| Or.inl ?_
          exact ⟨a, rfl⟩⟩, a.2⟩
        refine ⟨a', ?_, rfl⟩
        refine hR.1 ⟨a', rfl⟩
      · intro x hx
        have hR2 := hR.2 (Finset.mem_attach S' ⟨x, hx⟩)
        simp only [Set.mem_preimage, SetLike.mem_coe] at hR2
        exact ⟨⟨x, _⟩, hR2, rfl⟩)
    simp only [Subring.mem_map, Subring.coe_subtype, Subtype.exists, exists_and_right,
      exists_eq_right] at ha
    obtain ⟨_, ha⟩ := ha
    exact ha

open Classical in
instance : Module.Finite (A' S x S' hS') (KER ℳ x deg_x) := by
  change Module.Finite (Algebra.adjoin _ _) _
  fapply Algebra.adjoin_module_finite_of_annihilating
  · exact x

  · rw [← S.span_eq, ← hS']
    congr 1
    simp only [Finset.coe_insert]
  · simp only [Subtype.forall, SetLike.mk_smul_mk]
    intro x hx
    ext : 1
    exact hx

lemma eqKER [(a : M) → Decidable (a ∈ KER ℳ x deg_x)] :
    (μ' μ S x S' hS').poincareSeries (𝒜' S x S' hS') (KER ℳ x deg_x).grading =
    μ.poincareSeries 𝒜 (KER ℳ x deg_x).grading := by
  ext n
  rw [AdditiveFunction.coeff_poincareSeries, AdditiveFunction.coeff_poincareSeries]
  exact μ.eq_of_iso
    { hom := FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by rintro r (y : (KER ℳ x deg_x).grading n); rfl }
      inv := FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by rintro r (y : (KER ℳ x deg_x).grading n); rfl }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }

omit [(i : ℕ) → (x : (ℳ i)) → Decidable (x ≠ 0)] in
lemma eqCOKER :
    (μ' μ S x S' hS').poincareSeries (𝒜' S x S' hS') (COKER.den ℳ x deg_x).quotientGrading =
    μ.poincareSeries 𝒜 (COKER.den ℳ x deg_x).quotientGrading := by
  ext n
  rw [AdditiveFunction.coeff_poincareSeries, AdditiveFunction.coeff_poincareSeries]
  exact μ.eq_of_iso
    { hom := FGModuleCat.ofHom <|
      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by rintro r (y : (COKER.den ℳ x deg_x).quotientGrading n); rfl }
      inv := FGModuleCat.ofHom <|

      { toFun := fun x ↦ x
        map_add' := by intros; rfl
        map_smul' := by rintro r (y : (COKER.den ℳ x deg_x).quotientGrading n); rfl }
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl }

end

end induction.constructions

section induction_case

variable (N : ℕ) (ih : statement'.{u} N)

open induction.constructions

include ih in
lemma induction : statement'.{u} (N + 1) := by
  classical
  intro A M _ _ _ _ _ 𝒜 ℳ _ _ _ μ S cardS
  rw [Finset.card_eq_succ] at cardS
  obtain ⟨s, S', hs, hS1', hS2'⟩ := cardS

  let d : ℕ := S.deg (hS1' ▸ Finset.mem_insert_self _ _ : s ∈ S.toFinset)
  have deg_s : s ∈ 𝒜 d := S.mem_deg _
  have d_pos : 0 < d := S.deg_pos
    (hS1' ▸ Finset.mem_insert_self _ _ : s ∈ S.toFinset)
  have d_ne_zero : d ≠ 0 := by linarith only [d_pos]

  let A' : HomogeneousSubring 𝒜 := A' S s S' hS1'
  let 𝒜' : ℕ → AddSubgroup A' := 𝒜' S s S' hS1'

  let μ' := μ' μ S s S' hS1'
  letI : DirectSum.Decomposition (KER ℳ s deg_s).grading := (KER ℳ s deg_s).decomposition
  letI : SetLike.GradedSMul 𝒜' (HomogeneousSubmodule.grading (KER ℳ s deg_s)) := by
    apply gradedModule_KER
  obtain ⟨pKER, hpKER⟩ := ih A' (KER ℳ s deg_s).toSubmodule 𝒜' (KER ℳ s deg_s).grading μ'
    (generatingSet' S s S' hS1') (by
      rw [generatingSet'_toFinset, Finset.card_image_of_injective, Finset.card_attach, hS2']
      intro x y h
      ext
      simp only [Subtype.mk.injEq] at h
      exact h)
  obtain ⟨pCOKER, hpCOKER⟩ := ih A' (COKER ℳ s deg_s) 𝒜' (COKER.den ℳ s deg_s).quotientGrading μ'
    (generatingSet' S s S' hS1') (by
      rw [generatingSet'_toFinset, Finset.card_image_of_injective, Finset.card_attach, hS2']
      intro x y h
      ext
      simp only [Subtype.mk.injEq] at h
      exact h)
  erw [eqKER] at hpKER
  rw [eqCOKER] at hpCOKER

  obtain ⟨pIH, hpIH⟩ := key_lemma ℳ μ s deg_s
  rw [hpKER, hpCOKER] at hpIH

  replace hpIH : invOfUnit (1 - X ^ d : ℤ⟦X⟧) 1 * _ = invOfUnit (1 - X ^ d : ℤ⟦X⟧) 1 * _ :=
    congr_arg (invOfUnit (1 - X ^ d : ℤ⟦X⟧) 1 * ·) hpIH

  conv_lhs at hpIH => rw [← mul_assoc, mul_comm (invOfUnit (1 - X ^ d : ℤ⟦X⟧) 1),
    mul_invOfUnit (h := by simpa using d_ne_zero), one_mul]

  have eq_poles :
    S.poles.val = (generatingSet' S s S' hS1').poles.val * (1 - X^d : ℤ⟦X⟧) := by
    rw [generatingSetOverBaseRing.val_poles, generatingSetOverBaseRing.val_poles]
    have eq0 := calc ∏ i ∈ S.toFinset.attach, (1 - X ^ S.deg i.2 : ℤ⟦X⟧)
        _ = ∏ i ∈ (insert s S').attach,
              (1 - X ^ S.deg (hS1' ▸ i.2 : i.1 ∈ S.toFinset) : ℤ⟦X⟧) := by
            apply Finset.prod_bij (i := fun i _ ↦ ⟨i, hS1'.symm ▸ i.2⟩)
            · rintro i -; exact Finset.mem_attach _ _
            · rintro a - b - h
              ext
              rw [Subtype.ext_iff] at h
              exact h
            · rintro a -
              exact ⟨⟨a, hS1' ▸ a.2⟩, Finset.mem_attach _ _, rfl⟩
            · rintro a -; rfl
    rw [Finset.attach_insert, Finset.prod_insert, mul_comm] at eq0
    rw [eq0]
    congr 1
    · conv_lhs => rw [← Finset.prod_attach]
      simp_rw [generatingSet'_toFinset]
      set a1 := _; change ∏ i ∈ a1, _ = _
      set a2 := _; change _ = ∏ i ∈ a2, _
      apply Finset.prod_bij
      pick_goal 5
      · refine fun i _ ↦ ⟨⟨(i : A), ?_⟩, ?_⟩
        · rw [mem_A']
          have h := i.2
          simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at h
          obtain ⟨a, ha1, ha2⟩ := h
          rw [Subtype.ext_iff] at ha2
          rw [← ha2, Algebra.mem_adjoin_iff]
          exact Subring.subset_closure <| Or.inr ha1
        · simp only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
            Subtype.exists, exists_prop, exists_eq_right]
          have h := i.2
          simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at h
          obtain ⟨a, ha1, ha2⟩ := h
          rw [Subtype.ext_iff] at ha2
          rw [← ha2]
          exact ha1
      · intro _ _; exact Finset.mem_attach _ _
      · rintro ⟨i, hi⟩ - ⟨j, hj⟩ - h
        ext
        rw [Subtype.ext_iff, Subtype.ext_iff] at h
        exact h
      · rintro ⟨i, hi⟩ -
        simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hi
        obtain ⟨a, ha, rfl⟩ := hi
        refine ⟨⟨⟨a, Finset.mem_insert_of_mem ha⟩, ?_⟩, Finset.mem_attach _ _, rfl⟩
        · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
          Subtype.exists, exists_prop, exists_eq_right] using ha
      · rintro ⟨i, hi⟩ -
        congr 1
    · intro r
      simp only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and, Subtype.exists,
        exists_prop, exists_eq_right] at r
      exact hs r
  have eq_pole' :
    (generatingSet' S s S' hS1').poles⁻¹ = S.poles⁻¹ * (1 - X^d : ℤ⟦X⟧) := by
    symm
    rw [Units.inv_mul_eq_iff_eq_mul, eq_poles, mul_comm _ (1 - X^d : ℤ⟦X⟧),
      mul_assoc, Units.mul_inv (generatingSet' S s S' hS1').poles, mul_one]
  rw [mul_add, mul_sub, Algebra.mul_smul_comm, eq_pole', Algebra.mul_smul_comm,
    Algebra.mul_smul_comm, ← mul_assoc, mul_comm (invOfUnit (1 - X^d) 1), mul_assoc,
    mul_comm (invOfUnit (1 - X^d) 1), mul_invOfUnit (h := by simpa using d_ne_zero),
    mul_one, ← mul_assoc, mul_comm (invOfUnit (1 - X^d) 1), mul_assoc,
    ← mul_assoc (invOfUnit (1 - X^d) 1), mul_comm (invOfUnit (1 - X^d) 1),
    mul_assoc _ (invOfUnit (1 - X ^ d) 1) (1 - X^d), mul_comm (invOfUnit (1 - X^d) 1),
    mul_invOfUnit (h := by simpa using d_ne_zero), mul_one, ← Algebra.smul_mul_assoc,
    Algebra.smul_def, show pKER • X^d = algebraMap _ ℤ⟦X⟧ (pKER * Polynomial.X ^ d) from ?_,
    show invOfUnit (1 - X ^ d) 1 * algebraMap _ ℤ⟦X⟧ pIH =
      (algebraMap _ ℤ⟦X⟧ pIH * (generatingSet' S s S' hS1').poles.1) * S.poles.inv from ?_,
    ← sub_mul, Units.inv_eq_val_inv, ← add_mul, ← map_sub,
    (generatingSet' S s S' hS1').poles_val, ← map_mul, ← map_add] at hpIH
  · exact ⟨_, hpIH⟩
  · symm
    rw [Units.inv_eq_val_inv, Units.mul_inv_eq_iff_eq_mul, eq_poles,
      mul_comm (invOfUnit (1 - X^d) 1), mul_assoc, ← mul_assoc (invOfUnit (1 - X^d) 1),
      mul_comm (invOfUnit (1 - X^d) 1), mul_assoc _ _ (1 - X^d), mul_comm (invOfUnit (1 - X^d) 1),
      mul_invOfUnit (h := by simpa using d_ne_zero), mul_one]

  · rw [Algebra.smul_def, map_mul]
    congr
    simp only [HomogeneousIdeal.toIdeal_irrelevant, map_pow]
    congr
    simp only [algebraMap_apply', Algebra.id.map_eq_id, Polynomial.coe_X, map_X]

end induction_case

lemma proof' : ∀ s, statement'.{u} s := by
  intro s
  induction' s with s ih
  · apply proof.base_case
  · exact induction s ih

theorem _root_.hilbert_serre : ∃ (p : Polynomial ℤ), μ.poincareSeries 𝒜 ℳ = p • S.poles⁻¹ :=
  statement'_imp_statement 𝒜 ℳ μ S proof'.{u}

end HilbertSerre
