/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.DirectSum.Internal
public import Tengoku.Seed.Algebra.MonoidAlgebra.Basic
public import Tengoku.Seed.Algebra.MonoidAlgebra.Support
public import Tengoku.Seed.LinearAlgebra.Finsupp.SumProd
public import Tengoku.Seed.RingTheory.GradedAlgebra.Basic

/-!
# Internal grading of an `AddMonoidAlgebra`

In this file, we show that an `AddMonoidAlgebra` has an internal direct sum structure.

## Main results

* `AddMonoidAlgebra.gradeBy R f i`: the `i`th grade of an `R[M]` given by the
  degree function `f`.
* `AddMonoidAlgebra.grade R i`: the `i`th grade of an `R[M]` when the degree
  function is the identity.
* `AddMonoidAlgebra.gradeBy.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.gradeBy`.
* `AddMonoidAlgebra.grade.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.grade`.
* `AddMonoidAlgebra.gradeBy.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.gradeBy` defines an internal graded structure.
* `AddMonoidAlgebra.grade.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.grade` defines an internal graded structure when the degree function
  is the identity.
-/

@[expose] public section


noncomputable section

namespace AddMonoidAlgebra

variable {M : Type*} {ι : Type*} {R : Type*}

section

variable (R) [CommSemiring R]

/-- The submodule corresponding to each grade given by the degree function `f`. -/
abbrev gradeBy (f : M → ι) (i : ι) : Submodule R R[M] where
  carrier := { a | ∀ m, m ∈ a.coeff.support → f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

/-- The submodule corresponding to each grade. -/
abbrev grade (m : M) : Submodule R R[M] :=
  gradeBy R id m

/--
@isnad1 id=eq.0h2v.s5.c87aa7e05b58 from=seed src=0 shape=06d97264 vocab=98f22dad
-/
theorem gradeBy_id : gradeBy R (id : M → M) = grade R := rfl

/--
@isnad1 id=iff.0h6v.s7.9488bd16751b from=seed src=0 shape=ef8f3082 vocab=b6a30fe4
-/
theorem mem_gradeBy_iff (f : M → ι) (i : ι) (a : R[M]) :
    a ∈ gradeBy R f i ↔ (a.coeff.support : Set M) ⊆ f ⁻¹' {i} := by rfl

/--
@isnad1 id=iff.0h4v.s7.b640733656f0 from=seed src=0 shape=fc25c396 vocab=ec388cd9
-/
theorem mem_grade_iff (m : M) (a : R[M]) : a ∈ grade R m ↔ a.coeff.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  rfl

/--
@isnad1 id=iff.0h4v.s8.46ca295fad81 from=seed src=0 shape=cf008d39 vocab=bc145465
-/
theorem mem_grade_iff' (m : M) (a : R[M]) :
    a ∈ grade R m ↔ a ∈ LinearMap.range (lsingle (R := R) m) := by
  rw [mem_grade_iff, Finsupp.support_subset_singleton']; simp [← coeff_inj, eq_comm]

/--
@isnad1 id=eq.0h3v.s6.5fc5ace91e30 from=seed src=0 shape=c3511a57 vocab=764a44a9
-/
theorem grade_eq_lsingle_range (m : M) : grade R m = LinearMap.range (lsingle m) :=
  Submodule.ext (mem_grade_iff' R m)

/--
@isnad1 id=mem.0h6v.s7.798c3d32b753 from=seed src=0 shape=a4d0129e vocab=f8779e2b
-/
theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    single m r ∈ gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

/--
@isnad1 id=mem.0h4v.s7.b8eb10c29b78 from=seed src=0 shape=fdabd11c vocab=85ce342f
-/
theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) :
    single i r ∈ grade R i :=
  single_mem_gradeBy _ _ _

end

open DirectSum

/--
@isnad1 id=gradedmo.0h4v.s7.f5a23ad574ab from=seed src=0 shape=272ced76 vocab=56265560
-/
instance gradeBy.gradedMonoid [AddMonoid M] [AddMonoid ι] [CommSemiring R] (f : M →+ ι) :
    SetLike.GradedMonoid (gradeBy R f : ι → Submodule R R[M]) where
  one_mem m h := by
    rw [one_def] at h
    obtain rfl : m = 0 := Finset.mem_singleton.1 <| Finsupp.support_single_subset h
    apply map_zero
  mul_mem i j a b ha hb c hc := by
    classical
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : ∃ y ∈ a.coeff.support, ∃ z ∈ b.coeff.support, y + z = c :=
      Finset.mem_add.1 <| support_coeff_mul_subset a b hc
    rw [map_add, ha ma hma, hb mb hmb]

/--
@isnad1 id=gradedmo.0h2v.s6.a54fc265a8e9 from=seed src=0 shape=27f9d2d0 vocab=4c2add6e
-/
instance grade.gradedMonoid [AddMonoid M] [CommSemiring R] :
    SetLike.GradedMonoid (grade R : M → Submodule R R[M]) := by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition; the canonical grade decomposition, used to provide
`DirectSum.decompose`. -/
def decomposeAux : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i :=
  lift R _ M {
    toFun m := .of (fun i ↦ gradeBy R f i) (f m.toAdd) ⟨single m.toAdd 1, single_mem_gradeBy _ _ _⟩
    map_one' := of_eq_of_gradedMonoid_eq (by congr 2 <;> simp)
    map_mul' i j := by
      simpa [toAdd_mul, of_mul_of, GradedMonoid.GMul.mul, single_mul_single, mul_one] using
        DirectSum.of_eq_of_gradedMonoid_eq <| Sigma.subtype_ext (f.map_add _ _) rfl
  }

/--
@isnad1 id=eq.0h6v.s12.d59e98765f8a from=seed src=0 shape=27182705 vocab=de9ccdb1
-/
theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (single m r) =
      .of (fun i ↦ gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

/--
@isnad1 id=eq.0h6v.s12.1796b09872e2 from=seed src=0 shape=30fd981f vocab=c46790c6
-/
theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.coeff.support := by
      simpa only [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff, coeff_add, coeff_single, Finsupp.support_add_eq this, Finset.coe_union,
      Set.union_subset_iff] at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih', ← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy R f) :=
  .ofAlgHom _ (decomposeAux f) (by ext; simp [decomposeAux_single]) <| by simp [decomposeAux_coe]

/--
@isnad1 id=eq.0h4v.s12.fd7568115e28 from=seed src=0 shape=29a540bc vocab=b13fdb50
-/
@[simp]
theorem decomposeAux_eq_decompose :
    ⇑(decomposeAux f : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) :=
  rfl

/--
@isnad1 id=eq.0h6v.s12.ddee9aafb802 from=seed src=0 shape=3822eed0 vocab=c398bc93
-/
theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (single m r : R[M]) =
      .of (fun i ↦ gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ :=
  decomposeAux_single _ _ _

instance grade.gradedAlgebra : GradedAlgebra (grade R : ι → Submodule _ _) :=
  inferInstanceAs <| GradedAlgebra (gradeBy R (AddMonoidHom.id ι))

/--
@isnad1 id=eq.0h4v.s12.bf2bf97da377 from=seed src=0 shape=4764e8e7 vocab=f0370205
-/
theorem grade.decompose_single (i : ι) (r : R) :
    DirectSum.decompose (grade R : ι → Submodule _ _) (single i r) =
      .of (fun i ↦ grade R i) i ⟨single i r, single_mem_grade _ _⟩ :=
  decomposeAux_single _ _ _

/-- `AddMonoidAlgebra.gradeBy` describe an internally graded algebra.
@isnad1 id=isintern.0h4v.s7.2f3c22dc2680 from=seed src=0 shape=8919f991 vocab=fe0276eb
-/
theorem gradeBy.isInternal : DirectSum.IsInternal (gradeBy R f) :=
  DirectSum.Decomposition.isInternal _

/-- `AddMonoidAlgebra.grade` describe an internally graded algebra.
@isnad1 id=isintern.0h2v.s6.2b6d40bbbe28 from=seed src=0 shape=736ff39c vocab=b584775a
-/
theorem grade.isInternal : DirectSum.IsInternal (grade R : ι → Submodule R _) :=
  DirectSum.Decomposition.isInternal _

end AddMonoidAlgebra
