/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The quotient of a graded ring by a homogeneous ideal

For a graded ring `A = ⨁ᵢ 𝒜ᵢ` and a homogeneous ideal `J`, the quotient `A ⧸ J` is graded by the
images `grade 𝒜 J i = 𝒜ᵢ ↦ A ⧸ J` (`HomogeneousQuotient.gradedRing`).  Mathlib has no such
instance.  We also record that the decomposition of `A ⧸ J` is the reduction of that of `A`
(`coe_decompose_mk`) and that the irrelevant ideal of `A ⧸ J` is the image of that of `A`
(`irrelevant_le_map`), which is the hypothesis of `Proj.map` for `A ↠ A ⧸ J`.

The structure is a `def` (not an instance) because it depends on the homogeneity proof.
-/

set_option autoImplicit false

noncomputable section

open DirectSum

namespace SchemeNormalCone.AlgebraicGeometry.HomogeneousQuotient

variable {ι A : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing A]
  (𝒜 : ι → AddSubgroup A) [GradedRing 𝒜] (J : Ideal A)

/-- The degree-`i` part of `A ⧸ J`: the image of `𝒜 i`.-/
def grade (i : ι) : AddSubgroup (A ⧸ J) :=
  (𝒜 i).map (Ideal.Quotient.mk J).toAddMonoidHom

omit [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜] in
/--
@isnad1 id=mem.1h6v.s8.05824a8593ce from=translated src=- shape=4cdb94fa vocab=df352948
-/
theorem mk_mem_grade {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    Ideal.Quotient.mk J a ∈ grade 𝒜 J i :=
  ⟨a, ha, rfl⟩

/--
@isnad1 id=gradedmo.0h4v.s7.2b2aee578864 from=translated src=- shape=4f4f2fbb vocab=875f1735
-/
instance gradedMonoid : SetLike.GradedMonoid (grade 𝒜 J) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mk J)⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul (Ideal.Quotient.mk J) a b⟩

/-- Componentwise reduction `𝒜 i → grade i`.-/
def reduce (i : ι) : 𝒜 i →+ grade 𝒜 J i where
  toFun a := ⟨Ideal.Quotient.mk J a, mk_mem_grade 𝒜 J a.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- The decomposition of `A` followed by componentwise reduction.-/
def decompose₀ : A →+ ⨁ i, grade 𝒜 J i :=
  (DirectSum.map (reduce 𝒜 J)).comp (decomposeAddEquiv 𝒜).toAddMonoidHom

/--
@isnad1 id=eq.2h5v.s13.2add42cd3f61 from=translated src=- shape=05d441a2 vocab=61afa354
-/
theorem decompose₀_eq_zero (hJ : J.IsHomogeneous 𝒜) {a : A} (ha : a ∈ J) :
    decompose₀ 𝒜 J a = 0 := by
  ext i
  change ((reduce 𝒜 J i) (decompose 𝒜 a i) : A ⧸ J) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJ i ha)

/--
@isnad1 id=eq.0h5v.s13.6bcf2e658ce8 from=translated src=- shape=300aa2a6 vocab=c7da3aee
-/
theorem coe_decompose₀ (a : A) :
    DirectSum.coeAddMonoidHom (grade 𝒜 J) (decompose₀ 𝒜 J a) = Ideal.Quotient.mk J a := by
  have key : (DirectSum.coeAddMonoidHom (grade 𝒜 J)).comp (DirectSum.map (reduce 𝒜 J)) =
      (Ideal.Quotient.mk J).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
    refine DirectSum.addHom_ext fun i x ↦ ?_
    simp [reduce]
  have h := DFunLike.congr_fun key (decompose 𝒜 a)
  simp only [AddMonoidHom.comp_apply] at h
  rw [decompose₀, AddMonoidHom.comp_apply]
  change _ = Ideal.Quotient.mk J a
  refine h.trans ?_
  change Ideal.Quotient.mk J ((decompose 𝒜).symm (decompose 𝒜 a)) = _
  rw [Equiv.symm_apply_apply]

variable (hJ : J.IsHomogeneous 𝒜)
include hJ

/-- The decomposition of `A ⧸ J`.-/
def decomposeQ : A ⧸ J →+ ⨁ i, grade 𝒜 J i :=
  QuotientAddGroup.lift J.toAddSubgroup (decompose₀ 𝒜 J) (fun _ ha ↦ decompose₀_eq_zero 𝒜 J hJ ha)

/--
@isnad1 id=eq.1h5v.s13.bdf8400483a6 from=translated src=- shape=37f08a2b vocab=f78e7ebe
-/
theorem decomposeQ_mk (a : A) : decomposeQ 𝒜 J hJ (Ideal.Quotient.mk J a) = decompose₀ 𝒜 J a := rfl

/-- **The quotient of a graded ring by a homogeneous ideal is graded.**-/
@[implicit_reducible]
def decomposition : Decomposition (grade 𝒜 J) :=
  Decomposition.ofAddHom _ (decomposeQ 𝒜 J hJ)
    (by
      ext x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
      rw [decomposeQ_mk]
      exact coe_decompose₀ 𝒜 J a)
    (by
      refine DirectSum.addHom_ext fun i x ↦ ?_
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
      change decompose₀ 𝒜 J a = _
      rw [decompose₀, AddMonoidHom.comp_apply]
      change DirectSum.map (reduce 𝒜 J) (decompose 𝒜 a) = _
      rw [decompose_of_mem 𝒜 ha, DirectSum.map_of]
      rfl)

/-- The graded ring structure on `A ⧸ J`.-/
@[implicit_reducible]
def gradedRing : GradedRing (grade 𝒜 J) where
  toGradedMonoid := gradedMonoid 𝒜 J
  toDecomposition := decomposition 𝒜 J hJ

/--
@isnad1 id=eq.1h6v.s12.71d2e799877b from=translated src=- shape=cde6a533 vocab=9866198b
-/
theorem coe_decompose_mk (a : A) (i : ι) :
    letI := gradedRing 𝒜 J hJ
    ((decompose (grade 𝒜 J) (Ideal.Quotient.mk J a) i : grade 𝒜 J i) : A ⧸ J) =
      Ideal.Quotient.mk J (decompose 𝒜 a i) := rfl

omit hJ in
/--
@isnad1 id=le.1h3v.s9.53e7209b61f7 from=translated src=- shape=c8c06dc6 vocab=ac70e628
-/
theorem irrelevant_le_map (𝒜' : ℕ → AddSubgroup A) [GradedRing 𝒜']
    (J' : Ideal A) (hJ' : J'.IsHomogeneous 𝒜') :
    letI := gradedRing 𝒜' J' hJ'
    (HomogeneousIdeal.irrelevant (grade 𝒜' J')).toIdeal ≤
      (HomogeneousIdeal.irrelevant 𝒜').toIdeal.map (Ideal.Quotient.mk J') := by
  letI := gradedRing 𝒜' J' hJ'
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h0 : Ideal.Quotient.mk J' (decompose 𝒜' a 0) = 0 := by
    rw [← coe_decompose_mk 𝒜' J' hJ' a 0]
    exact hx
  have hmem : a - decompose 𝒜' a 0 ∈ (HomogeneousIdeal.irrelevant 𝒜').toIdeal := by
    change GradedRing.proj 𝒜' 0 (a - decompose 𝒜' a 0) = 0
    rw [map_sub, GradedRing.proj_apply, GradedRing.proj_apply,
      decompose_of_mem_same 𝒜' (SetLike.coe_mem _), sub_self]
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk J') hmem
  rwa [map_sub, h0, sub_zero] at this

end SchemeNormalCone.AlgebraicGeometry.HomogeneousQuotient
