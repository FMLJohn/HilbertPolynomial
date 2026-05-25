/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import HilbertPolynomial.Module.Graded.Homogeneous
import HilbertPolynomial.missing_lemmas.GradeZeroModule

import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.Group.Subgroup.Finite

namespace GradedRing

section CommRing

variable {A M : Type*}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [finite_module : Module.Finite A M] [noetherian_ring : IsNoetherianRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

instance : Algebra (𝒜 0) A := Algebra.ofSubring (SetLike.GradeZero.subring 𝒜)

open BigOperators Pointwise SetLike

/--
a finite homogeneous generating set of an ideal `I` is a set of non-zero homogeneous elements that
spans `I`.
-/
structure HomogeneousGeneratingSetOf (I : Ideal A) where
  /--the underlying set of a finite homogeneous generating set -/
  toFinset : Finset A
  /--every element is homogeneous -/
  homogeneous' : ∀ {a : A}, a ∈ toFinset → IsHomogeneousElem 𝒜 a
  /--every element is not zero-/
  ne_zero' : ∀ {a : A}, a ∈ toFinset → a ≠ 0
  /--the set spans the ideal-/
  span_eq : Ideal.span toFinset = I

namespace HomogeneousGeneratingSetOf

instance (I : Ideal A) : Membership A (HomogeneousGeneratingSetOf 𝒜 I) where
  mem S a := a ∈ S.toFinset

variable {𝒜}
variable {I : Ideal A} (S : HomogeneousGeneratingSetOf 𝒜 I)

omit noetherian_ring [GradedRing 𝒜] in
lemma homogeneous {a : A} (h : a ∈ S) : IsHomogeneousElem 𝒜 a := S.homogeneous' h

omit noetherian_ring [GradedRing 𝒜] in
lemma ne_zero {a : A} (h : a ∈ S) : a ≠ 0 := S.ne_zero' h

/-- Since each elements is homogeneous, it has a degree-/
noncomputable def deg {a : A} (h : a ∈ S) : ℕ :=
  S.homogeneous h |>.choose

omit noetherian_ring [GradedRing 𝒜] in
lemma mem_deg {a : A} (h : a ∈ S) : a ∈ 𝒜 (S.deg h) :=
  S.homogeneous h |>.choose_spec

variable (𝒜) in
/-- An arbitrary chosen finite homogeneous generating set for the irrelevant ideal.-/
noncomputable def Irrelevant :
    HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
  let H := Ideal.fg_iff_homogeneously_fg _  |>.mp <|
    isNoetherianRing_iff_ideal_fg A |>.mp inferInstance
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  { toFinset := H.choose
    homogeneous' := fun h ↦ H.choose_spec.1 _ h |>.1
    ne_zero' := fun h ↦ H.choose_spec.1 _ h |>.2
    span_eq := H.choose_spec.2 |>.symm }

variable (S : HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal)

omit noetherian_ring in
lemma irrelevant.deg_pos {a : A} (h : a ∈ S) : 0 < deg _ h := by
  by_contra! rid
  simp only [nonpos_iff_eq_zero] at rid
  have m : a ∈ Ideal.span S.toFinset := Ideal.subset_span h
  have h_deg1 := mem_deg _ h
  rw [rid] at h_deg1
  erw [span_eq, HomogeneousIdeal.mem_irrelevant_iff,
    GradedRing.proj_apply, DirectSum.decompose_of_mem_same (hx := h_deg1)] at m
  exact (ne_zero _ h) m

omit noetherian_ring in
lemma irrelevant.adjoin_eq_top :
    Algebra.adjoin (𝒜 0) S.toFinset = (⊤ : Subalgebra (𝒜 0) A) := by
    classical
  symm
  suffices subset :
      ∀ (m : ℕ), (𝒜 m : Set A) ⊆ (Algebra.adjoin (𝒜 0) S.toFinset : Subalgebra (𝒜 0) A) by
    refine le_antisymm ?_ le_top
    intro a _
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    exact Subalgebra.sum_mem _ fun j _ ↦ subset j <| Subtype.mem _

  suffices ∀ (n : ℕ),
      𝒜 n.succ =
      ⨆ (s : {s : S.toFinset | S.deg s.2 ≤ n + 1 }), (s : A) • 𝒜 (n.succ - deg _ s.1.2) by
    intro m
    cases m with | zero => ?_ | succ m => ?_
    · intro x hx
      show _ ∈ Subsemiring.closure (_ ∪ _)
      rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S.toFinset]
      exact @le_sup_left (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
        Subsemiring.subset_closure ⟨⟨_, hx⟩, rfl⟩

    induction' m using Nat.strong_induction_on with m ih
    rw [this]

    intro x hx
    simp only [SetLike.mem_coe] at hx ⊢
    refine AddSubgroup.iSup_induction (C := fun y ↦ y ∈ Algebra.adjoin (𝒜 0) (S.toFinset : Set A))
      (fun (s : {s : S.toFinset | S.deg s.2 ≤ m + 1 }) ↦
        (s : A) • 𝒜 (m.succ - deg _ s.1.2)) hx
      ?_ ?_ ?_
    · rintro ⟨⟨x, hx1⟩, (hx2 : deg _ _ ≤ _)⟩ y hy1
      simp only at hy1
      rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hy1
      obtain ⟨y, hy1, rfl⟩ := hy1
      by_cases ineq1 : x = 0
      · rw [ineq1, zero_smul]; exact Subalgebra.zero_mem _

      by_cases ineq0 : m < S.deg hx1
      · have eq0 : m.succ - S.deg hx1 = 0 := by simpa only [tsub_eq_zero_iff_le] using ineq0
        rw [eq0] at hy1
        refine Subalgebra.mul_mem _ (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_)
          (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_) <;>
        rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S.toFinset]
        · exact @le_sup_right (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
            Subsemiring.subset_closure hx1
        · exact @le_sup_left (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
            Subsemiring.subset_closure ⟨⟨_, hy1⟩, rfl⟩
      simp only [not_lt] at ineq0
      specialize ih (m - deg _ hx1) (Nat.sub_lt_self (irrelevant.deg_pos S _) ineq0) <|
        show y ∈ _ by
          simp only [SetLike.mem_coe]
          convert hy1 using 2
          rw [Nat.succ_sub]
          exact ineq0
      refine Subalgebra.mul_mem _ (show _ ∈ Subsemiring.closure (_ ∪ _) from ?_) ih
      rw [Subsemiring.closure_union (Set.range <| algebraMap (𝒜 0) A) S.toFinset]
      exact @le_sup_right (Subsemiring A) _ (Subsemiring.closure _) (Subsemiring.closure _) _ <|
        Subsemiring.subset_closure hx1

    · exact Subalgebra.zero_mem _
    · intros _ _ h1 h2
      exact Subalgebra.add_mem _ h1 h2

  intro n
  ext x; constructor
  · intro hx
    have m : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      erw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (hx := hx)]
      norm_num
    erw [← S.span_eq, mem_span_set] at m
    obtain ⟨f, hf, (eq0 : ∑ i ∈ f.support, f i * i = x)⟩ := m
    replace eq0 :=
      calc x
        = (DirectSum.decompose 𝒜 x (n + 1) : A) :=
          by simp only [DirectSum.of_eq_same, DirectSum.decompose_of_mem 𝒜 hx]
      _ = DirectSum.decompose 𝒜 (∑ a ∈ f.support, f a * a) (n + 1) := by rw [eq0]
      _ = ∑ a ∈ f.support, (DirectSum.decompose 𝒜 (f a * a) (n + 1) : A) :=
          by change GradedRing.proj 𝒜 (n + 1) (∑ a ∈ f.support, f a * a : A) = _
             rw [map_sum]
             rfl
      _ = ∑ a ∈ f.support.attach, (DirectSum.decompose 𝒜 (f a * a) (n + 1) : A) :=
          Finset.sum_attach _ _ |>.symm
      _ = ∑ a ∈ f.support.attach,
            if deg _ (hf a.2) ≤ n + 1
            then (DirectSum.decompose 𝒜 (f a) ((n + 1) - deg _ (hf a.2)) * a : A)
            else 0 := Finset.sum_congr rfl fun a _ ↦
          DirectSum.coe_decompose_mul_of_right_mem 𝒜 (n + 1) (mem_deg _ (hf a.2)) (a := f a)

    rw [eq0]
    refine AddSubgroup.sum_mem _ fun a _ ↦ ?_

    split_ifs with h
    · refine AddSubgroup.mem_iSup_of_mem ⟨⟨a, hf a.2⟩, h⟩ ?_
      rw [AddSubgroup.mem_smul_pointwise_iff_exists]
      exact ⟨DirectSum.decompose 𝒜 (f a) ((n + 1) - deg _ (hf a.2)), SetLike.coe_mem _,
        by rw [mul_comm]; rfl⟩
    · exact AddSubgroup.zero_mem _
  · intro hx
    refine AddSubgroup.iSup_induction (C := fun y ↦ y ∈ 𝒜 n.succ)
      (fun (s : {s : S.toFinset | S.deg s.2 ≤ n + 1 }) ↦ (s : A) • 𝒜 (n.succ - deg _ s.1.2)) hx
      ?_ ?_ ?_
    · rintro ⟨⟨x, hx1⟩, (hx2 : deg _ _ ≤ _)⟩ z hz1
      simp only at hz1
      rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hz1
      obtain ⟨z, hz1, rfl⟩ := hz1
      convert SetLike.mul_mem_graded (mem_deg _ hx1) hz1 using 2
      rw [← Nat.add_sub_assoc, add_comm, Nat.add_sub_cancel]
      exact hx2
    · exact AddSubgroup.zero_mem _
    · intros _ _ h1 h2
      exact AddSubgroup.add_mem _ h1 h2

end HomogeneousGeneratingSetOf

namespace finite_algebra_over_degree_zero_subring

/--
if `f` maps `aᵢ` to `nᵢ`
then `f` represents the monomial `∏ᵢ aᵢ ^ nᵢ`
-/
def evalMonomial (f : A →₀ ℕ) : A :=
  ∏ a ∈ f.support, a ^ (f a)

omit noetherian_ring in
@[simp] lemma evalMonomial_zero : evalMonomial (A := A) 0 = 1 := by
  simp [evalMonomial]

/--
suppose `f` represents the monomial `∏ᵢ aᵢ ^ nᵢ` and each `aᵢ` has degree `dᵢ`, then the monomial
has degree `∑ᵢ nᵢ * dᵢ`
-/
def degreeMonomial
    (f : A →₀ ℕ)
    (deg : ⦃a : A⦄ → (ha : a ∈ f.support) → ℕ) : ℕ :=
  ∑ i ∈ f.support.attach, deg i.2 * f i

omit [CommRing A] noetherian_ring in
lemma degreeMonomial_zero : degreeMonomial (A := A) 0 (fun a h ↦ by simp at h) = 0 := by
  simp [degreeMonomial]

omit noetherian_ring in
lemma evalMonomial_mem_aux {ι : Type*} (s : Finset ι)
    (deg : s → ℕ)
    (pow : s → ℕ)
    (f : s → A)
    (h_deg : ∀ i, f i ∈ 𝒜 (deg i)):
    ∏ i ∈ s.attach, f i ^ (pow i) ∈ 𝒜 (∑ i ∈ s.attach, deg i * pow i) := by
  classical
  induction' s using Finset.induction_on with a s h ih
  · simp only [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty]
    exact (SetLike.GradeZero.subring 𝒜).one_mem
  · simp only [Finset.attach_insert]
    rw [Finset.prod_insert (by simpa), Finset.sum_insert (by simpa)]
    refine SetLike.mul_mem_graded ?_ ?_
    · rw [mul_comm, ← smul_eq_mul]
      refine SetLike.pow_mem_graded _ ?_
      exact h_deg ⟨a, by aesop⟩
    · simp only [Finset.mem_attach, Subtype.mk.injEq, forall_true_left, Subtype.forall, imp_self,
      implies_true, Finset.prod_image, Finset.sum_image]
      apply ih
      rintro ⟨i, hi⟩
      exact h_deg ⟨i, by aesop⟩

omit noetherian_ring in
lemma evalMonomial_mem
    (f : A →₀ ℕ)
    (deg : ⦃a : A⦄ → (ha : a ∈ f.support) → ℕ)
    (h_deg :  ⦃a : A⦄ → (ha : a ∈ f.support) → a ∈ 𝒜 (deg ha)) :
    evalMonomial f ∈ 𝒜 (degreeMonomial f deg) := by
  classical
  delta evalMonomial degreeMonomial
  convert evalMonomial_mem_aux 𝒜 f.support
    (fun i ↦ deg i.2) (fun i ↦ f i) Subtype.val (fun ⟨i, hi⟩ ↦ h_deg hi)
  exact Finset.prod_attach _ _ |>.symm

variable (S : HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal)

omit noetherian_ring in
lemma evalMonomial_homogeneous
    (f : A →₀ ℕ) (hf : f.support ⊆ S.toFinset) :
    IsHomogeneousElem 𝒜 (evalMonomial f) := by
  exact ⟨degreeMonomial _ _,
    evalMonomial_mem
      (deg := fun _ h ↦ S.deg (hf h))
      (h_deg := fun _ h ↦ S.mem_deg (hf h))⟩

omit noetherian_ring in
lemma top_eq_span_monomial :
    (⊤ : Submodule (𝒜 0) A) =
    Submodule.span (𝒜 0)
      {a | ∃ (f : A →₀ ℕ), f.support ⊆ S.toFinset ∧ a =
        evalMonomial f } := by
  classical
  refine le_antisymm ?_ le_top
  rintro x -
  have hx : x ∈ (⊤ : Subalgebra (𝒜 0) A) := ⟨⟩
  rw [← HomogeneousGeneratingSetOf.irrelevant.adjoin_eq_top] at hx
  refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
  · intro x hx
    refine Submodule.subset_span ⟨Finsupp.single x 1,
      Finsupp.support_single_subset.trans (by simpa), ?_⟩
    · delta evalMonomial
      have eq1 : (Finsupp.single x 1).support = {x} :=
        le_antisymm Finsupp.support_single_subset (by simp)
      simp [eq1]
  · intro r
    change (r : A) ∈ Submodule.span (𝒜 0) _
    rw [show (r : A) = (r : A) • (1 : A) by rw [smul_eq_mul, mul_one]]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span ⟨0, by simp, by simp [evalMonomial]⟩
  · intro a b _ _ ha hb
    exact Submodule.add_mem _ ha hb
  · intro a b _ _ ha hb
    apply Submodule.span_induction₂ (ha := ha) (hb := hb)
    · rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      refine Submodule.subset_span ⟨(f + g : A →₀ ℕ), ?_, ?_⟩
      · exact Finsupp.support_add (g₁ := f) (g₂ := g) |>.trans <|
          sup_le (α := Finset A) hf hg
      · simp only [evalMonomial, Finsupp.coe_add, Pi.add_apply]
        rw [Finset.prod_subset (h := hf), Finset.prod_subset (h := hg),
          Finset.prod_subset (h := (_ : (f + g).support ⊆ S.toFinset))]
        rotate_left
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, ne_eq, add_eq_zero,
            not_and, not_forall, not_not, exists_prop] at hx2
          rw [pow_add, hx2.1, hx2.2, pow_zero, one_mul]
        · exact Finsupp.support_add (g₁ := f) (g₂ := g) |>.trans <|
            sup_le (α := Finset A) hf hg
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx2
          rw [hx2, pow_zero]
        · intro x _ hx2
          simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx2
          rw [hx2, pow_zero]

        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
    · intro y _
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro x _
      rw [mul_zero]
      exact Submodule.zero_mem _
    · intro x₁ x₂ y _ _ _ hx₁ hx₂
      rw [add_mul]
      exact Submodule.add_mem _ hx₁ hx₂
    · intro x y₁ y₂ _ _ _ hy₁ hy₂
      rw [mul_add]
      exact Submodule.add_mem _ hy₁ hy₂
    · intro r x y _ _ h
      change ((r : A) * x) * y ∈ _
      rw [mul_assoc, ← smul_eq_mul]
      exact Submodule.smul_mem _ _ h
    · intro r x y _ _ h
      change x * ((r : A) * y) ∈ _
      rw [show x * (r * y) = r * (x * y) by ring, ← smul_eq_mul]
      exact Submodule.smul_mem _ _ h

lemma Finset.single_le_sum' {ι : Type*}
    {s : Finset ι} {f : s → ℕ} (a : s) : f a ≤ ∑ x ∈ s.attach, f x := by
  classical
  induction' s using Finset.induction_on with i s h ih
  · cases' a with a ha
    simp only [Finset.not_mem_empty] at ha
  · cases' a with a ha
    simp only [Finset.mem_insert] at ha

    rw [Finset.attach_insert, Finset.sum_insert (by simpa)]
    simp only [Finset.mem_attach, Subtype.mk.injEq, forall_true_left, Subtype.forall, imp_self,
      implies_true, Finset.sum_image]
    cases' ha with ha ha
    · subst ha
      rw [le_add_iff_nonneg_right]
      norm_num

    · specialize ih (f := fun x ↦ f ⟨x.1, by aesop⟩) ⟨a, ha⟩
      refine ih.trans ?_
      rw [le_add_iff_nonneg_left]
      norm_num

omit noetherian_ring in
lemma monomial_finite_of_bounded_degree (k : ℕ) :
    {p | ∃ (hp1 : p.support ⊆ S.toFinset),
      (degreeMonomial p fun _ ha ↦ S.deg (hp1 ha)) ≤ k}.Finite := by
  let SMonomials := {p | ∃ (hp1 : p.support ⊆ S.toFinset),
    (degreeMonomial p fun a ha ↦ S.deg (hp1 ha)) ≤ k}
  let e : (s : SMonomials) → (S.toFinset → Finset.range (k + 1)) :=
    fun s a ↦ ⟨s.1 a, by
      have le1 : Finset.sum _ _ ≤ _ := s.2.2
      dsimp only at le1
      by_cases mem1 : a.1 ∈ s.1.support
      · have le2 : S.deg (s.2.1 mem1) * s.1 a.1 ≤ k :=
          le_trans (Finset.single_le_sum' (s := s.1.support)
            (f := fun i ↦ S.deg (s.2.1 i.2) * s.1 i.1) (a := ⟨a, mem1⟩)) le1
        by_cases le3 : a.1 = 0
        · exfalso
          exact S.ne_zero (s.2.1 mem1) le3
        · have le4 := HomogeneousGeneratingSetOf.irrelevant.deg_pos S (s.2.1 mem1)
          have le5 : s.1 a.1 ≤ k := by
            have := Nat.div_le_div_right (c := S.deg (s.2.1 mem1)) le2
            erw [mul_comm, Nat.mul_div_cancel _ le4] at this
            refine this.trans (Nat.div_le_self _ _)
          simp only [Set.mem_setOf_eq, Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
          rw [Nat.lt_succ_iff]
          exact le5
      · simp only [Set.mem_setOf_eq, Finsupp.mem_support_iff, ne_eq, not_not] at mem1
        rw [mem1]
        aesop⟩
  suffices Finite SMonomials from Set.toFinite _
  suffices inj : Function.Injective e from Finite.of_injective _ inj

  intro s1 s2 h
  ext a
  by_cases mem1 : a ∈ s1.1.support ∨ a ∈ s2.1.support
  · refine Subtype.ext_iff.mp <| congr_fun h ⟨a, ?_⟩
    rcases mem1 with mem1|mem1
    · exact s1.2.1 mem1
    · exact s2.2.1 mem1
  · push_neg at mem1
    simp only [Set.mem_setOf_eq, Finsupp.mem_support_iff, ne_eq, not_not] at mem1
    rw [mem1.1, mem1.2]

end finite_algebra_over_degree_zero_subring

/--
If `A ≅ ⨁ᵢ, Aᵢ` is a noetherian graded ring, then `A` is a finite `A₀`-algebra.
-/
instance finite_algebra_over_degree_zero_subring : Algebra.FiniteType (𝒜 0) A := by
  constructor
  exact ⟨(HomogeneousGeneratingSetOf.Irrelevant 𝒜).toFinset,
    HomogeneousGeneratingSetOf.irrelevant.adjoin_eq_top _⟩

end CommRing

end GradedRing

namespace GradedModule

variable {A M : Type*}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [finite_module : Module.Finite A M] [noetherian_ring : IsNoetherianRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
variable (ℳ : ℕ → AddSubgroup M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

open BigOperators Pointwise SetLike

/--
a finite homogeneous generating set of a submodule `p` is a set of non-zero homogeneous elements
that spans `p`.
-/
structure HomogeneousGeneratingSetOf (p : Submodule A M) where
  /--the underlying set of a finite homogeneous generating set -/
  toFinset : Finset M
  homogeneous' : ∀ {m : M}, m ∈ toFinset → IsHomogeneousElem ℳ m
  /--every element is not zero-/
  ne_zero' : ∀ {m : M}, m ∈ toFinset → m ≠ 0
  /--the set spans the ideal-/
  span_eq : Submodule.span A toFinset = p

namespace HomogeneousGeneratingSetOf

instance (p : Submodule A M) : Membership M (HomogeneousGeneratingSetOf ℳ p) where
  mem S m := m ∈ S.toFinset

variable {ℳ}
variable {p : Submodule A M} (S : HomogeneousGeneratingSetOf ℳ p)

omit finite_module noetherian_ring [DirectSum.Decomposition ℳ] in
lemma homogeneous {a : M} (h : a ∈ S) : IsHomogeneousElem ℳ a := S.homogeneous' h

omit finite_module noetherian_ring [DirectSum.Decomposition ℳ] in
lemma ne_zero {a : M} (h : a ∈ S) : a ≠ 0 := S.ne_zero' h

/-- Since each element is homogeneous, it has a degree. -/
noncomputable def deg {a : M} (h : a ∈ S) : ℕ :=
  S.homogeneous h |>.choose

omit finite_module noetherian_ring [DirectSum.Decomposition ℳ] in
lemma mem_deg {a : M} (h : a ∈ S) : a ∈ ℳ (S.deg h) :=
  S.homogeneous h |>.choose_spec

variable (A ℳ) in
/-- An arbitrary chosen finite generating set for the top submodule. -/
noncomputable def Top :
    HomogeneousGeneratingSetOf ℳ (⊤ : Submodule A M) :=
  let H := Submodule.fg_iff_homogeneously_fg (A := A) (ℳ := ℳ) (p := ⊤) |>.mp finite_module.fg_top
  { toFinset := H.choose
    homogeneous' := fun h ↦ H.choose_spec.1 _ h |>.1
    ne_zero' := fun h ↦ H.choose_spec.1 _ h |>.2
    span_eq := H.choose_spec.2 |>.symm }

end HomogeneousGeneratingSetOf

namespace finite_module_over_degree_zero_subring

open GradedRing.finite_algebra_over_degree_zero_subring

variable (T : GradedRing.HomogeneousGeneratingSetOf 𝒜 (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
variable (TM : HomogeneousGeneratingSetOf ℳ (⊤ : Submodule A M))

omit finite_module noetherian_ring [DirectSum.Decomposition ℳ] [GradedSMul 𝒜 ℳ] in
variable {𝒜 ℳ} in
lemma generatingSet_is_finite (k : ℕ) :
    {x : ℳ k |
      ∃ (ω : M) (_ : ω ∈ TM.toFinset) (p : A →₀ ℕ) (hp1 : p.support ⊆ T.toFinset),
        degreeMonomial p (fun _ h ↦ T.deg (hp1 h)) ≤ k ∧
        (x : M) = evalMonomial p • ω }.Finite := by
  let S := {x : ℳ k |
      ∃ (ω : M) (_ : ω ∈ TM.toFinset) (p : A →₀ ℕ) (hp1 : p.support ⊆ T.toFinset),
      degreeMonomial p (fun _ h ↦ T.deg (hp1 h)) ≤ k ∧ (x : M) = evalMonomial p • ω }
  change S.Finite
  have eq1 := calc
      S = ⋃ (ω ∈ TM.toFinset),
            {x : ℳ k | ∃ (p : A →₀ ℕ) (hp1 : p.support ⊆ T.toFinset),
              degreeMonomial p (fun a ha ↦ T.deg (hp1 ha)) ≤ k ∧ (x : M) = evalMonomial p • ω} :=
          by ext s; simp [S]
      _ = ⋃ (ω ∈ TM.toFinset),
          ⋃ (p ∈ {p : A →₀ ℕ | ∃ (hp1 : p.support ⊆ T.toFinset),
                    degreeMonomial p (fun _ h ↦ T.deg (hp1 h)) ≤ k}),
            {x : ℳ k | (x : M) = evalMonomial p • ω} := by ext; simp
  rw [eq1]
  apply Set.Finite.biUnion' (hs := TM.toFinset.finite_toSet)
  intro ω _
  apply Set.Finite.biUnion
  · apply monomial_finite_of_bounded_degree
  · rintro p ⟨_, _⟩
    have fin1 : Subsingleton {x : ℳ k | ↑x = evalMonomial p • ω} := by
      constructor
      rintro ⟨x, (hx : _ = _)⟩ ⟨y, (hy : _ = _)⟩
      ext
      rw [hx, hy]
    exact Set.toFinite _

omit finite_module noetherian_ring in
variable {𝒜 ℳ} in
lemma kth_degree_eq_span (k : ℕ) :
    (⊤ : Submodule (𝒜 0) (ℳ k)) =
    Submodule.span (𝒜 0)
      {x : ℳ k |
        ∃ (ω : M) (_ : ω ∈ TM.toFinset) (p : A →₀ ℕ) (hp1 : p.support ⊆ T.toFinset),
          degreeMonomial p (fun _ ha ↦ T.deg (hp1 ha)) ≤ k ∧
          (x : M) = evalMonomial p • ω } := by
  refine le_antisymm ?_ le_top
  rintro ⟨x, hx⟩ -

  have mem1 : x ∈ (⊤ : Submodule A M) := ⟨⟩
  rw [← TM.span_eq, mem_span_set] at mem1

  obtain ⟨f, f_support_le, (eq0 : ∑ i ∈ f.support, (f i) • i = x)⟩ := mem1

  have mem1 (a : A) : a ∈ (⊤ : Submodule (𝒜 0) A) := ⟨⟩
  simp_rw [top_eq_span_monomial 𝒜 T, mem_span_set] at mem1
  choose r hr1 hr2 using mem1
  change ∀ a, ∑ j ∈ (r a).support, (r a) j • j = a at hr2
  replace hr1 (a : A) :
    ∀ j ∈ (r a).support, ∃ f, f.support ⊆ T.toFinset ∧ j = evalMonomial f := by exact hr1 a
  choose p hp1 hp2 using hr1
  replace eq0 := calc
      x = ∑ i ∈ f.support, (f i) • i := eq0.symm
      _ = ∑ i ∈ f.support, (∑ j ∈ (r (f i)).support, r (f i) j • j) • i :=
          Finset.sum_congr rfl fun x _ ↦ by
            congr 1
            rw [hr2 (f x)]
      _ = ∑ i ∈ f.support, ∑ j ∈ (r (f i)).support, (r (f i) j • j) • i :=
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_smul
      _ = ∑ i ∈ f.support, ∑ j ∈ (r (f i)).support, (r (f i) j : A) • (j : A) • (i : M) :=
          Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by
            change ((r (f x) y : A) * y) • _ = _
            rw [mul_smul]
      _ = ∑ i ∈ f.support, ∑ j ∈ (r (f i)).support.attach,
            (r (f i) j : A) • (j : A) • (i : M) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_attach _ _ |>.symm
      _ = ∑ i ∈ f.support, ∑ j ∈ (r (f i)).support.attach,
            (r (f i) j : A) • (evalMonomial (p _ _ j.2) : A) • (i : M) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
            congr 2
            exact hp2 _ _ j.2
  apply_fun GradedModule.proj ℳ k at eq0
  conv_lhs at eq0 => rw [GradedModule.proj_apply, DirectSum.decompose_of_mem_same _ hx]
  simp_rw [map_sum] at eq0

  replace eq0 := calc
    x = ∑ i ∈ f.support, ∑ j ∈ (r (f i)).support.attach,
          GradedModule.proj ℳ k ((r (f i) j : A) • (evalMonomial (p _ _ j.2) : A) • (i : M)) := eq0
    _ = ∑ i ∈ f.support, ∑ j ∈ (r (f i)).support.attach,
          GradedModule.proj ℳ k (((r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)) • (i : M)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [mul_smul]
    _ = ∑ i ∈ f.support.attach, ∑ j ∈ (r (f i)).support.attach,
          GradedModule.proj ℳ k (((r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)) • (i : M)) :=
        Finset.sum_attach _ _ |>.symm
    _ = ∑ i ∈ f.support.attach, ∑ j ∈ (r (f i)).support.attach,
          if TM.deg (f_support_le i.2) ≤ k
          then
            GradedRing.proj 𝒜 (k - TM.deg (f_support_le i.2))
              ((r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)) • (i : M)
          else 0 :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
          rw [GradedModule.proj_smul_mem_right 𝒜 ℳ _ _
            (TM.mem_deg (f_support_le i.2))]
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦
          TM.deg (f_support_le i.2) ≤ k,
        ∑ j ∈ (r (f i)).support.attach,
          GradedRing.proj 𝒜 (k - TM.deg (f_support_le i.2))
            ((r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)) • (i : M) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi⟩ -
        split_ifs with ineq1
        · rfl
        · rw [Finset.sum_const, smul_zero]
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦
          TM.deg (f_support_le i.2) ≤ k,
        (∑ j ∈ (r (f i)).support.attach,
          GradedRing.proj 𝒜 (k - TM.deg (f_support_le i.2))
            ((r (f i) j : A) * (evalMonomial (p _ _ j.2) : A))) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_smul]
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k,
        (∑ j ∈ (r (f i)).support.attach,
          if degreeMonomial (p _ _ j.2)
            (fun _ h ↦ T.deg (hp1 _ _ j.2 h)) ≤ k - TM.deg (f_support_le i.2)
          then
            GradedRing.proj 𝒜
              ((k - TM.deg (f_support_le i.2)) -
                degreeMonomial (p _ _ j.2) fun a ha ↦ T.deg (hp1 _ _ j.2 ha))
              (r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)
          else 0) • (i : M) := by
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi1⟩ _
        congr 1
        refine Finset.sum_congr rfl ?_
        rintro ⟨j, hj⟩ -
        rw [GradedRing.proj_apply, DirectSum.coe_decompose_mul_of_right_mem 𝒜]
        pick_goal 2
        · apply evalMonomial_mem 𝒜 (p _ _ hj) (fun _ h ↦
            T.deg (hp1 _ _ hj h))
          rintro a ha
          apply T.mem_deg (hp1 _ _ hj ha)
        rfl
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k,
        (∑ j ∈ (r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) ≤
            k - TM.deg (f_support_le i.2),
          GradedRing.proj 𝒜
              ((k - TM.deg (f_support_le i.2)) -
                degreeMonomial (p _ _ j.2) fun a ha ↦ T.deg (hp1 _ _ j.2 ha))
              (r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_filter]
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k,
        ∑ j ∈ (r (f i)).support.attach.filter
          fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun _ h ↦ T.deg (hp1 _ _ j.2 h)) ≤
            k - TM.deg (f_support_le i.2),
          (GradedRing.proj 𝒜
              ((k - TM.deg (f_support_le i.2)) -
                degreeMonomial (p _ _ j.2) fun _ h ↦ T.deg (hp1 _ _ j.2 h))
              (r (f i) j : A) * (evalMonomial (p _ _ j.2) : A)) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [Finset.sum_smul]
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k,
        ∑ j ∈ (r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun _ h ↦ T.deg (hp1 _ _ j.2 h)) ≤
            k - TM.deg (f_support_le i.2),
          (GradedRing.proj 𝒜
              ((k - TM.deg (f_support_le i.2)) -
                degreeMonomial (p _ _ j.2) fun _ h ↦ T.deg (hp1 _ _ j.2 h))
              (r (f i) j : A)) • (evalMonomial (p _ _ j.2) : A) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by rw [mul_smul]
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k,
        ∑ j ∈ (r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) ≤
            k - TM.deg (f_support_le i.2),
          (if degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) =
              k - TM.deg (f_support_le i.2)
            then (r (f i) j : A)
            else 0) • (evalMonomial (p _ _ j.2) : A) • (i : M) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j hj ↦ by
          congr 1
          split_ifs with ineq1
          · rw [ineq1, Nat.sub_self, GradedRing.proj_apply, DirectSum.decompose_of_mem_same]
            exact SetLike.coe_mem _
          · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne (hx := SetLike.coe_mem _)]
            intro rid
            rw [eq_comm, Nat.sub_eq_zero_iff_le] at rid
            rw [Finset.mem_filter] at hj
            exact ineq1 <| le_antisymm hj.2 rid
    _ = ∑ i ∈ f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k,
        ∑ j ∈ (r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) =
            k - TM.deg (f_support_le i.2),
          (r (f i) j : A) • (evalMonomial (p _ _ j.2) : A) • (i : M) := by
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, hi1⟩ _
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        rintro ⟨h, hj1⟩ -
        simp only [ite_smul, zero_smul, ite_eq_left_iff, not_le]
        intro rid
        rw [if_neg (Ne.symm (ne_of_lt rid))]
    _ = ∑ i ∈ (f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k).attach,
        ∑ j ∈ (r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) =
            k - TM.deg (f_support_le i.1.2),
          (r (f i) j : A) • (evalMonomial (p _ _ j.2) : A) • (i : M) :=
        Finset.sum_attach _ _ |>.symm
    _ = ∑ i ∈ (f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k).attach,
        ∑ j ∈ ((r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) =
            k - TM.deg (f_support_le i.1.2)).attach,
          (r (f i) j : A) • (evalMonomial (p _ _ j.1.2) : A) • (i : M) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_attach _ _ |>.symm
  replace eq0 :
    (⟨x, hx⟩ : ℳ k) =
    ∑ i ∈ (f.support.attach.filter fun i : f.support ↦ TM.deg (f_support_le i.2) ≤ k).attach,
        ∑ j ∈ ((r (f i)).support.attach.filter fun j : (r (f i)).support ↦
            degreeMonomial (p _ _ j.2) (fun a ha ↦ T.deg (hp1 _ _ j.2 ha)) =
            k - TM.deg (f_support_le i.1.2)).attach,
          r (f i) j • (⟨(evalMonomial (p _ _ j.1.2) : A) • (i : M), by
            convert (inferInstance : SetLike.GradedSMul 𝒜 ℳ).smul_mem
              (evalMonomial_mem 𝒜 (p _ _ j.1.2) (fun a ha ↦ T.deg (hp1 _ _ j.1.2 ha))
                (fun a ha ↦ T.mem_deg (hp1 _ _ j.1.2 ha)))
              (TM.mem_deg (f_support_le i.1.2))
            have mem := j.2
            simp only [Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_attach,
              true_and] at mem
            rw [mem, vadd_eq_add, Nat.sub_add_cancel]
            simpa [-Finset.coe_mem] using i.2⟩ : ℳ k) := by
    ext
    refine eq0.trans ?_
    rw [AddSubgroup.val_finset_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨j, hj1⟩ -
    rw [AddSubgroup.val_finset_sum]
    rfl

  rw [eq0]
  refine Submodule.sum_mem _ ?_
  rintro ⟨⟨i, hi1⟩, hi2⟩ -
  simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hi2
  refine Submodule.sum_mem _ ?_
  rintro ⟨⟨j, hj1⟩, hj2⟩ -
  simp only [Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_attach, true_and] at hj2
  refine Submodule.smul_mem _ _ <| Submodule.subset_span
    ⟨i, f_support_le hi1, p _ _ hj1, hp1 _ _ hj1, ?_, rfl⟩

  rw [hj2]
  exact Nat.sub_le _ _

end finite_module_over_degree_zero_subring

open finite_module_over_degree_zero_subring in
instance finite_module_over_degree_zero_subring (k : ℕ) : Module.Finite (𝒜 0) (ℳ k) :=
  ⟨Set.Finite.toFinset
    (generatingSet_is_finite
      (GradedRing.HomogeneousGeneratingSetOf.Irrelevant 𝒜)
      (HomogeneousGeneratingSetOf.Top A ℳ) k),
    by simpa only [Set.Finite.coe_toFinset] using
      (kth_degree_eq_span
        (GradedRing.HomogeneousGeneratingSetOf.Irrelevant 𝒜)
        (HomogeneousGeneratingSetOf.Top A ℳ) k).symm⟩

end GradedModule
