import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.CategoryTheory.MonoidalCategory open _root_.AlgebraicGeometry

open scoped CategoryTheory.MonObj

noncomputable section

namespace P2mThetaFinB

variable {k : Type u} [Field k] {X : Scheme.{u}} {t : X ⟶ Spec (CommRingCat.of k)}

abbrev Pt (t : X ⟶ Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

def pt (z : Pt t) : X := z.left (IsLocalRing.closedPoint k)

/--
@isnad1 id=eq.0h4v.s7.a4cd1dc7c3fb from=translated src=- shape=06075c1f vocab=b46c3785
-/
lemma left_comp (z : Pt t) : (z.left : Spec (CommRingCat.of k) ⟶ X) ≫ t = 𝟙 _ := Over.w z

/--
@isnad1 id=injectiv.0h3v.s5.a43cb70ae232 from=translated src=- shape=ec110de3 vocab=c2546d36
-/
lemma pt_injective [LocallyOfFiniteType t] [IsAlgClosed k] : Function.Injective (pt (t := t)) :=
  fun z z' h => Over.OverMorphism.ext
    (ext_of_apply_closedPoint_eq (X := X) (f := z.left) (g := z'.left) t (left_comp z)
      (left_comp z') h)

/--
@isnad1 id=ex.1h4v.s7.3e7af353661c from=translated src=- shape=e9f5b207 vocab=757669f8
-/
lemma exists_pt_eq [LocallyOfFiniteType t] [IsAlgClosed k] {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ z : Pt t, pt z = y :=
  ⟨Over.homMk (pointOfClosedPoint (X := X) t y hy) (by simp), pointOfClosedPoint_apply t y hy _⟩

section Grp

variable [GrpObj (Over.mk t)]

def lmul (z : Pt t) : Over.mk t ⟶ Over.mk t :=
  (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z) * 𝟙 (Over.mk t)

/--
@isnad1 id=eq.0h5v.s8.4f046684ca1d from=translated src=- shape=c9da0708 vocab=bd5fd8c4
-/
lemma comp_lmul (x z : Pt t) : x ≫ lmul z = z * x := by
  have h1 : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ z = z := by
    rw [show CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ from
      Subsingleton.elim _ _]
    exact Category.id_comp z
  rw [lmul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.comp_toUnit, h1]

/--
@isnad1 id=eq.0h5v.s9.6289295bd63e from=translated src=- shape=5810468a vocab=98aa6000
-/
lemma pt_mul (z x : Pt t) : pt (z * x) = (lmul z).left (pt x) := by
  rw [← comp_lmul]
  rfl

def invLeft (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] : X ⟶ X :=
  (ι[Over.mk t]).left

/--
@isnad1 id=eq.0h4v.s8.93ad16670fdf from=translated src=- shape=e37cc64e vocab=0f9266ad
-/
lemma pt_inv (x : Pt t) : pt x⁻¹ = invLeft t (pt x) := by
  rw [Hom.inv_def]
  rfl

def Cplus (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] (Z : Set X) : Set X :=
  ⋂ z ∈ {z : Pt t | pt z ∈ Z}, ((lmul z).left : X ⟶ X) ⁻¹' Z

/--
@isnad1 id=isclosed.1h4v.s6.c23eb1206c9a from=translated src=- shape=57521186 vocab=909b4b5a
-/
lemma isClosed_Cplus {Z : Set X} (hZ : IsClosed Z) : IsClosed (Cplus t Z) :=
  isClosed_biInter fun z _ => hZ.preimage (lmul z).left.continuous

/--
@isnad1 id=iff.0h5v.s8.d639904efa39 from=translated src=- shape=3ad1937e vocab=8022ed94
-/
lemma mem_Cplus_iff {Z : Set X} (x : Pt t) :
    pt x ∈ Cplus t Z ↔ ∀ z : Pt t, pt z ∈ Z → pt (z * x) ∈ Z := by
  simp only [Cplus, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_preimage, pt_mul]

def C (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] (Z : Set X) : Set X :=
  Cplus t Z ∩ (invLeft t) ⁻¹' Cplus t Z

/--
@isnad1 id=isclosed.1h4v.s6.19cee1c8d2c1 from=translated src=- shape=57521186 vocab=a85be77a
-/
lemma isClosed_C {Z : Set X} (hZ : IsClosed Z) : IsClosed (C t Z) :=
  (isClosed_Cplus hZ).inter ((isClosed_Cplus hZ).preimage (invLeft t).continuous)

/--
@isnad1 id=iff.0h5v.s8.61a2d6728335 from=translated src=- shape=158bd971 vocab=f828c4ff
-/
lemma mem_stab_iff {Z : Set X} (x : Pt t) :
    (∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z) ↔ pt x ∈ C t Z := by
  rw [C, Set.mem_inter_iff, Set.mem_preimage, ← pt_inv, mem_Cplus_iff, mem_Cplus_iff]
  constructor
  · intro h
    refine ⟨fun z hz => (h z).1 hz, fun z hz => ?_⟩
    have := (h (z * x⁻¹)).2
    rw [inv_mul_cancel_right] at this
    exact this hz
  · rintro ⟨h₁, h₂⟩ z
    refine ⟨h₁ z, fun hz => ?_⟩
    have := h₂ (z * x) hz
    rwa [mul_inv_cancel_right] at this

end Grp

variable (t) in

/--
@isnad1 id=finite.3h5v.s7.5053ba31450b from=translated src=- shape=c581e07f vocab=af5d72cb
-/
lemma finite_of_isClosed_of_subset_affineOpen [IsProper t] {C : Set X} (hC : IsClosed C)
    {U : X.Opens} (hU : IsAffineOpen U) (hCU : C ⊆ U) : C.Finite := by

  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩
  have hrange : Set.range I.subschemeι = C := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨C, hC⟩

  have htop : I.subschemeι ⁻¹ᵁ U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact hCU (hrange ▸ Set.mem_range_self y)
  have hAff : IsAffine I.subscheme := by
    have h1 : IsAffineOpen (I.subschemeι ⁻¹ᵁ U) := hU.preimage I.subschemeι
    rw [htop] at h1
    haveI : IsAffine (⊤ : I.subscheme.Opens) := h1
    exact IsAffine.of_isIso I.subscheme.topIso.inv

  have hfin : IsFinite (I.subschemeι ≫ t) := by
    rw [IsFinite.iff_isProper_and_isAffineHom]
    exact ⟨inferInstance, isAffineHom_of_isAffine _⟩

  have huniv : (Set.univ : Set I.subscheme).Finite := by
    have := (I.subschemeι ≫ t).finite_preimage_singleton (IsLocalRing.closedPoint k)
    refine this.subset fun y _ => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subsingleton.elim _ _
  rw [← hrange, ← Set.image_univ]
  exact huniv.image _

/--
@isnad1 id=finite.4h5v.s9.73183720555c from=translated src=- shape=b6117810 vocab=b0579c79
-/
theorem main [IsAlgClosed k] [IsProper t] [GrpObj (Over.mk t)] (Z : Set X) (hZ : IsClosed Z) (U : X.Opens)
    (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ U) (he : pt (1 : Pt t) ∉ Z) :
    Set.Finite {x : Pt t | ∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z} := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t

  have hS : {x : Pt t | ∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z} = pt ⁻¹' C t Z := by
    ext x
    exact mem_stab_iff x
  rw [hS]

  have hCZ : C t Z ⊆ U := by
    intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := by
      by_contra hyZ
      exact hyU (hZU hyZ)
    have hcl : IsClosed (C t Z ∩ Z) := (isClosed_C hZ).inter hZ
    have hne : (C t Z ∩ Z ∩ closedPoints X).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := JacobsonSpace.closure_inter_closedPoints_eq_closure hcl.isLocallyClosed
      rw [hemp, closure_empty, hcl.closure_eq] at this
      exact (this ▸ (Set.mem_empty_iff_false y)).mp ⟨hy, hyZ⟩
    obtain ⟨y₀, ⟨hy₀C, hy₀Z⟩, hy₀cl⟩ := hne
    obtain ⟨z₀, rfl⟩ := exists_pt_eq (t := t) (mem_closedPoints_iff.mp hy₀cl)
    have hst := (mem_stab_iff z₀).2 hy₀C 1
    rw [one_mul] at hst
    exact he (hst.2 hy₀Z)
  have hCfin : (C t Z).Finite := finite_of_isClosed_of_subset_affineOpen t (isClosed_C hZ) hU hCZ
  exact hCfin.preimage pt_injective.injOn

end P2mThetaFinB

end

/--
@isnad1 id=finite.4h5v.s11.c8a8847c86ea from=translated src=- shape=4413eed9 vocab=a805571f
-/
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [GrpObj (Over.mk t)]
    (Z : Set X) (hZ : IsClosed Z) (U : X.Opens) (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ (U : Set X))
    (he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t).left (IsLocalRing.closedPoint k) ∉ Z) :
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
      ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        z.left (IsLocalRing.closedPoint k) ∈ Z ↔ (z * x).left (IsLocalRing.closedPoint k) ∈ Z} :=
  P2mThetaFinB.main Z hZ U hU hZU he
