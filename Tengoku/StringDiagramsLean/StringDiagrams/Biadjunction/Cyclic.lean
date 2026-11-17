import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Basic
import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Conjugate
import Tengoku.Seed.CategoryTheory.EqToHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mates and cyclic 2-morphisms

Properties of the right and left mates of a 2-morphism between 1-morphisms with chosen
biadjunctions, and closure properties of cyclic 2-morphisms (`Biadjunction.IsCyclic`).

## Main results

* Functoriality: `rightMate_id`, `leftMate_id`, and `rightMate_comp`, `leftMate_comp`
  (mates reverse the order of vertical composition); `doubleMate_id`, `doubleMate_comp`.
* Whiskering (for composite biadjunctions `Biadjunction.comp`): `rightMate_whiskerRight`,
  `leftMate_whiskerRight`, `rightMate_whiskerLeft`, `leftMate_whiskerLeft`.
* Mates of mates (`Biadjunction.symm`): `rightMate_symm_leftMate`, `leftMate_symm_rightMate`
  (the mates of `α` with respect to the exchanged biadjunctions, taken in the opposite
  rotational direction, return `α`) and `rightMate_symm`, `leftMate_symm`.
* Cyclic 2-morphisms: `isCyclic_id`, `IsCyclic.comp`, `IsCyclic.whiskerRight`,
  `IsCyclic.whiskerLeft`, `IsCyclic.hcomp`, `IsCyclic.inv`, `IsCyclic.rightMate`,
  `IsCyclic.leftMate`; the associators and unitors are cyclic for the composite
  biadjunctions (`isCyclic_associator_hom`, `isCyclic_leftUnitor_hom`, ...), and
  `isCyclic_eqToHom` for biadjunctions identified along equalities of 1-morphisms.
* Units and counits: the unit of `f ⊣ g` is cyclic with respect to `Biadjunction.id` and
  `P.comp P.symm`, and both of its mates are the counit of `g ⊣ f`
  (`rightMate_left_unit`, `leftMate_left_unit`, `isCyclic_left_unit`); similarly for the
  unit of `g ⊣ f` and for the two counits.
* `rightMate_eq_comp`, `leftMate_eq_comp`: changing the biadjunctions conjugates the mates
  by the mates of identities.
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

namespace Biadjunction

variable {a b c d : B}

section Vertical

variable {f f' f'' : a ⟶ b} {g g' g'' : b ⟶ a}

/--
@isnad1 id=eq.0h6v.s9.18d1e6d0faca from=translated src=- shape=629e2e02 vocab=002f507f
-/
@[simp]
theorem rightMate_id (P : f ⊣⊢ g) : rightMate P P (𝟙 f) = 𝟙 g :=
  conjugateEquiv_id _

/--
@isnad1 id=eq.0h6v.s9.d132df74c10f from=translated src=- shape=629e2e02 vocab=bc3dc66a
-/
@[simp]
theorem leftMate_id (P : f ⊣⊢ g) : leftMate P P (𝟙 f) = 𝟙 g :=
  conjugateEquiv_symm_id _

/--
@isnad1 id=eq.0h14v.s10.aa42a5257a23 from=translated src=- shape=c0db0afd vocab=b8359180
-/
theorem rightMate_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (P'' : f'' ⊣⊢ g'') (α : f ⟶ f')
    (β : f' ⟶ f'') :
    rightMate P P'' (α ≫ β) = rightMate P' P'' β ≫ rightMate P P' α :=
  (conjugateEquiv_comp _ _ _ _ _).symm

/--
@isnad1 id=eq.0h14v.s10.2a5afd16f0fa from=translated src=- shape=c0db0afd vocab=1c7fbdf8
-/
theorem leftMate_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (P'' : f'' ⊣⊢ g'') (α : f ⟶ f')
    (β : f' ⟶ f'') :
    leftMate P P'' (α ≫ β) = leftMate P' P'' β ≫ leftMate P P' α :=
  (conjugateEquiv_symm_comp _ _ _ _ _).symm

/--
@isnad1 id=eq.0h6v.s7.b91cd4dd35e0 from=translated src=- shape=eeefd19d vocab=4a75cc23
-/
@[simp]
theorem doubleMate_id (P : f ⊣⊢ g) : doubleMate P P (𝟙 f) = 𝟙 f := by
  rw [doubleMate, rightMate_id, Equiv.symm_apply_eq, leftMate_id]

/--
@isnad1 id=eq.0h14v.s8.520a569d36c6 from=translated src=- shape=7783ee9c vocab=e77b700b
-/
theorem doubleMate_comp (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (P'' : f'' ⊣⊢ g'') (α : f ⟶ f')
    (β : f' ⟶ f'') :
    doubleMate P P'' (α ≫ β) = doubleMate P P' α ≫ doubleMate P' P'' β := by
  rw [doubleMate, Equiv.symm_apply_eq, leftMate_comp P P' P'', doubleMate, doubleMate,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, rightMate_comp]

/-- Changing the biadjunctions on the source and target conjugates the right mate by the right
mates of identities.
@isnad1 id=eq.0h12v.s10.ff802248109a from=translated src=- shape=9802a679 vocab=4febe41b
-/
theorem rightMate_eq_comp (P Q : f ⊣⊢ g) (P' Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P P' α = rightMate Q' P' (𝟙 f') ≫ rightMate Q Q' α ≫ rightMate P Q (𝟙 f) := by
  rw [← rightMate_comp, ← rightMate_comp, Category.id_comp, Category.comp_id]

/-- Changing the biadjunctions on the source and target conjugates the left mate by the left
mates of identities.
@isnad1 id=eq.0h12v.s10.85dffae3ebe1 from=translated src=- shape=9802a679 vocab=2ac07fa9
-/
theorem leftMate_eq_comp (P Q : f ⊣⊢ g) (P' Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P P' α = leftMate Q' P' (𝟙 f') ≫ leftMate Q Q' α ≫ leftMate P Q (𝟙 f) := by
  rw [← leftMate_comp, ← leftMate_comp, Category.id_comp, Category.comp_id]

end Vertical

section Change

variable {f f' : a ⟶ b} {g g' h h' : b ⟶ a}

/-- `rightMate_eq_comp` for biadjunctions with different chosen biadjoints.
@isnad1 id=eq.0h14v.s10.486c33ab7fb5 from=translated src=- shape=d22f7e50 vocab=4febe41b
-/
theorem rightMate_eq_comp' (P : f ⊣⊢ g) (Q : f ⊣⊢ h) (P' : f' ⊣⊢ g') (Q' : f' ⊣⊢ h')
    (α : f ⟶ f') :
    rightMate P P' α = rightMate Q' P' (𝟙 f') ≫ rightMate Q Q' α ≫ rightMate P Q (𝟙 f) := by
  simp only [rightMate]
  rw [conjugateEquiv_comp, conjugateEquiv_comp, Category.id_comp, Category.comp_id]

/-- `leftMate_eq_comp` for biadjunctions with different chosen biadjoints.
@isnad1 id=eq.0h14v.s10.9bbb25e0fe32 from=translated src=- shape=d22f7e50 vocab=2ac07fa9
-/
theorem leftMate_eq_comp' (P : f ⊣⊢ g) (Q : f ⊣⊢ h) (P' : f' ⊣⊢ g') (Q' : f' ⊣⊢ h')
    (α : f ⟶ f') :
    leftMate P P' α = leftMate Q' P' (𝟙 f') ≫ leftMate Q Q' α ≫ leftMate P Q (𝟙 f) := by
  simp only [leftMate]
  rw [conjugateEquiv_symm_comp, conjugateEquiv_symm_comp, Category.id_comp, Category.comp_id]

end Change

section Symm

variable {f f' : a ⟶ b} {g g' : b ⟶ a}

/-- The right mate with respect to the exchanged biadjunctions is the inverse of the left
mate.
@isnad1 id=eq.0h9v.s7.5efbd6d6ce20 from=translated src=- shape=467f1cfc vocab=16d736d6
-/
theorem rightMate_symm (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') :
    rightMate P'.symm P.symm = (leftMate P P').symm := rfl

/-- The left mate with respect to the exchanged biadjunctions is the inverse of the right
mate.
@isnad1 id=eq.0h9v.s7.2834f843503c from=translated src=- shape=467f1cfc vocab=16d736d6
-/
theorem leftMate_symm (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') :
    leftMate P'.symm P.symm = (rightMate P P').symm := rfl

/--
@isnad1 id=eq.0h10v.s9.7b162253e977 from=translated src=- shape=a4d19996 vocab=08b91420
-/
@[simp]
theorem rightMate_symm_leftMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P'.symm P.symm (leftMate P P' α) = α :=
  Equiv.apply_symm_apply (conjugateEquiv P.right P'.right) α

/--
@isnad1 id=eq.0h10v.s9.c2bc92f7c621 from=translated src=- shape=a4d19996 vocab=08b91420
-/
@[simp]
theorem leftMate_symm_rightMate (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P'.symm P.symm (rightMate P P' α) = α :=
  Equiv.symm_apply_apply _ _

/--
@isnad1 id=eq.0h10v.s10.0ba335eb6a3d from=translated src=- shape=fe57d44a vocab=1414b41a
-/
@[simp]
theorem leftMate_symm_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (β : g' ⟶ g) :
    leftMate P P' ((leftMate P P').symm β) = β :=
  Equiv.apply_symm_apply _ _

/-- The double mate is the right mate taken twice, the second time with respect to the
exchanged biadjunctions.
@isnad1 id=eq.0h10v.s9.67f26d5860dc from=translated src=- shape=2200dced vocab=1b109495
-/
theorem doubleMate_eq (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    doubleMate P P' α = rightMate P'.symm P.symm (rightMate P P' α) := rfl

end Symm

/-! ## Cyclic 2-morphisms -/

section Cyclic

variable {f f' f'' : a ⟶ b} {g g' g'' : b ⟶ a}

/--
@isnad1 id=iscyclic.0h6v.s6.5e4721745eb2 from=translated src=- shape=dded72d7 vocab=106c2a80
-/
theorem isCyclic_id (P : f ⊣⊢ g) : IsCyclic P P (𝟙 f) := by
  rw [IsCyclic, rightMate_id, leftMate_id]

/--
@isnad1 id=eq.1h10v.s9.6dd73743ee6b from=translated src=- shape=8c40aefb vocab=a5073529
-/
theorem IsCyclic.eq {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} (h : IsCyclic P P' α) :
    rightMate P P' α = leftMate P P' α := h

/--
@isnad1 id=eq.1h10v.s7.69f1d97a1754 from=translated src=- shape=4270a472 vocab=dc8c9bbb
-/
theorem IsCyclic.doubleMate_eq {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (h : IsCyclic P P' α) : doubleMate P P' α = α :=
  (isCyclic_iff_doubleMate_eq P P' α).1 h

/--
@isnad1 id=iscyclic.2h14v.s7.325a7859f185 from=translated src=- shape=dbf137ef vocab=fd6e22f1
-/
theorem IsCyclic.comp {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {P'' : f'' ⊣⊢ g''} {α : f ⟶ f'}
    {β : f' ⟶ f''} (hα : IsCyclic P P' α) (hβ : IsCyclic P' P'' β) :
    IsCyclic P P'' (α ≫ β) := by
  rw [IsCyclic, rightMate_comp P P' P'', leftMate_comp P P' P'', hα.eq, hβ.eq]

/--
@isnad1 id=iscyclic.1h10v.s7.70bbacdc1236 from=translated src=- shape=ff3b6a93 vocab=22f655c0
-/
theorem IsCyclic.inv {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} [IsIso α]
    (h : IsCyclic P P' α) : IsCyclic P' P (CategoryTheory.inv α) := by
  have hr : rightMate P' P (CategoryTheory.inv α) ≫ rightMate P P' α = 𝟙 _ := by
    rw [← rightMate_comp, IsIso.hom_inv_id, rightMate_id]
  have hl : leftMate P' P (CategoryTheory.inv α) ≫ leftMate P P' α = 𝟙 _ := by
    rw [← leftMate_comp, IsIso.hom_inv_id, leftMate_id]
  have : IsIso (rightMate P P' α) :=
    ⟨rightMate P' P (CategoryTheory.inv α),
      by rw [← rightMate_comp, IsIso.inv_hom_id, rightMate_id], hr⟩
  rw [← h.eq] at hl
  rw [IsCyclic, IsIso.eq_inv_of_inv_hom_id hr, IsIso.eq_inv_of_inv_hom_id hl]

/--
@isnad1 id=iscyclic.1h10v.s7.25e7c5216732 from=translated src=- shape=e9b7cd66 vocab=e7d7c942
-/
theorem IsCyclic.iso_inv {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {e : f ≅ f'}
    (h : IsCyclic P P' e.hom) : IsCyclic P' P e.inv := by
  have := h.inv
  rwa [IsIso.Iso.inv_hom] at this

/-- The right mate of a cyclic 2-morphism is cyclic, for the exchanged biadjunctions.
@isnad1 id=iscyclic.1h10v.s9.5a740c7ef8f7 from=translated src=- shape=49c2f943 vocab=b97dd27c
-/
theorem IsCyclic.rightMate {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (h : IsCyclic P P' α) : IsCyclic P'.symm P.symm (rightMate P P' α) := by
  rw [IsCyclic, leftMate_symm_rightMate]
  conv_lhs => rw [h.eq]
  exact rightMate_symm_leftMate P P' α

/-- The left mate of a cyclic 2-morphism is cyclic, for the exchanged biadjunctions.
@isnad1 id=iscyclic.1h10v.s9.50660670b337 from=translated src=- shape=49c2f943 vocab=cc16bd5e
-/
theorem IsCyclic.leftMate {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (h : IsCyclic P P' α) : IsCyclic P'.symm P.symm (leftMate P P' α) := by
  rw [← h.eq]; exact h.rightMate

/--
@isnad1 id=iff.0h10v.s9.dd23d398427a from=translated src=- shape=b32fe528 vocab=b97dd27c
-/
theorem isCyclic_rightMate_iff (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    IsCyclic P'.symm P.symm (rightMate P P' α) ↔ IsCyclic P P' α := by
  refine ⟨fun h => ?_, IsCyclic.rightMate⟩
  have := h.leftMate
  rwa [leftMate_symm_rightMate] at this

/-- Cyclicity of `β : g' ⟶ g` for the exchanged biadjunctions: the inverses of the two mates
agree.
@isnad1 id=iff.0h10v.s10.d5da6d2b99a3 from=translated src=- shape=a214eae7 vocab=24130896
-/
theorem isCyclic_symm_iff (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (β : g' ⟶ g) :
    IsCyclic P'.symm P.symm β ↔ (rightMate P P').symm β = (leftMate P P').symm β := by
  rw [IsCyclic, rightMate_symm, leftMate_symm, eq_comm]

end Cyclic

/-! ## Whiskering -/

section Whisker

variable {f f' : a ⟶ b} {g g' : b ⟶ a}

/--
@isnad1 id=eq.0h14v.s10.418967ce9348 from=translated src=- shape=0fe6e9ec vocab=9f05a6c6
-/
theorem rightMate_whiskerRight (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : b ⟶ c} {k : c ⟶ b}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    rightMate (P.comp R) (P'.comp R) (α ▷ h) = k ◁ rightMate P P' α :=
  conjugateEquiv_whiskerRight _ _ _ _

/--
@isnad1 id=eq.0h14v.s10.1ac14ccd39fe from=translated src=- shape=0fe6e9ec vocab=6a4dcfc9
-/
theorem leftMate_whiskerRight (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : b ⟶ c} {k : c ⟶ b}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    leftMate (P.comp R) (P'.comp R) (α ▷ h) = k ◁ leftMate P P' α :=
  conjugateEquiv_symm_whiskerRight _ _ _ _

/--
@isnad1 id=eq.0h14v.s10.c8f90617c999 from=translated src=- shape=cd36819a vocab=9f05a6c6
-/
theorem rightMate_whiskerLeft (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : c ⟶ a} {k : a ⟶ c}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    rightMate (R.comp P) (R.comp P') (h ◁ α) = rightMate P P' α ▷ k :=
  conjugateEquiv_whiskerLeft _ _ _ _

/--
@isnad1 id=eq.0h14v.s10.4d33c6e59b18 from=translated src=- shape=cd36819a vocab=6a4dcfc9
-/
theorem leftMate_whiskerLeft (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') {h : c ⟶ a} {k : a ⟶ c}
    (R : h ⊣⊢ k) (α : f ⟶ f') :
    leftMate (R.comp P) (R.comp P') (h ◁ α) = leftMate P P' α ▷ k :=
  conjugateEquiv_symm_whiskerLeft _ _ _ _

/--
@isnad1 id=iscyclic.1h14v.s7.b775a2c14057 from=translated src=- shape=5dde2e2b vocab=583058df
-/
theorem IsCyclic.whiskerRight {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) {h : b ⟶ c} {k : c ⟶ b} (R : h ⊣⊢ k) :
    IsCyclic (P.comp R) (P'.comp R) (α ▷ h) := by
  rw [IsCyclic, rightMate_whiskerRight, leftMate_whiskerRight, hα.eq]

/--
@isnad1 id=iscyclic.1h14v.s7.da0017b69649 from=translated src=- shape=e0abefb3 vocab=ec00273b
-/
theorem IsCyclic.whiskerLeft {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'}
    (hα : IsCyclic P P' α) {h : c ⟶ a} {k : a ⟶ c} (R : h ⊣⊢ k) :
    IsCyclic (R.comp P) (R.comp P') (h ◁ α) := by
  rw [IsCyclic, rightMate_whiskerLeft, leftMate_whiskerLeft, hα.eq]

/-- Horizontal composites of cyclic 2-morphisms are cyclic for the composite biadjunctions.
@isnad1 id=iscyclic.2h18v.s8.4b0a391630f0 from=translated src=- shape=deddf070 vocab=f679b6c0
-/
theorem IsCyclic.hcomp {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} {h h' : b ⟶ c}
    {k k' : c ⟶ b} {R : h ⊣⊢ k} {R' : h' ⊣⊢ k'} {β : h ⟶ h'} (hα : IsCyclic P P' α)
    (hβ : IsCyclic R R' β) :
    IsCyclic (P.comp R) (P'.comp R') (α ▷ h ≫ f' ◁ β) :=
  (hα.whiskerRight R).comp (hβ.whiskerLeft P')

end Whisker

/-! ## Units and counits -/

section UnitCounit

variable {f : a ⟶ b} {g : b ⟶ a}

/-- The right mate of the unit of `f ⊣ g` (a 2-morphism `𝟙 a ⟶ f ≫ g`, with the biadjunctions
`Biadjunction.id a` and `P.comp P.symm : f ≫ g ⊣⊢ f ≫ g`) is the counit of `g ⊣ f`.
@isnad1 id=eq.0h6v.s9.3dd6937630a9 from=translated src=- shape=1bb8b888 vocab=2c1e0a13
-/
theorem rightMate_left_unit (P : f ⊣⊢ g) :
    rightMate (id a) (P.comp P.symm) P.left.unit = P.right.counit := by
  apply conjugateEquiv_eq_of_unit
  simp only [id_left, comp_left, symm_left, Adjunction.id, Adjunction.comp_unit,
    Adjunction.compUnit]
  symm
  calc
    _ = P.left.unit ⊗≫ f ◁ leftZigzag P.right.unit P.right.counit ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [P.right.left_triangle]; bicategory

/-- The left mate of the unit of `f ⊣ g` is the counit of `g ⊣ f`.
@isnad1 id=eq.0h6v.s9.fdc16428df64 from=translated src=- shape=1bb8b888 vocab=4b200128
-/
theorem leftMate_left_unit (P : f ⊣⊢ g) :
    leftMate (id a) (P.comp P.symm) P.left.unit = P.right.counit := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [id_right, comp_right, symm_right, Adjunction.id, Adjunction.comp_unit,
    Adjunction.compUnit]
  calc
    _ = P.left.unit ⊗≫ rightZigzag P.right.unit P.right.counit ▷ g ⊗≫ 𝟙 _ := by
      bicategory
    _ = _ := by
      rw [P.right.right_triangle]; bicategory

/-- The unit of `f ⊣ g` is cyclic for the biadjunctions `Biadjunction.id a` and
`P.comp P.symm`.
@isnad1 id=iscyclic.0h6v.s6.4ffbec2cc563 from=translated src=- shape=85012a76 vocab=8ddce868
-/
theorem isCyclic_left_unit (P : f ⊣⊢ g) : IsCyclic (id a) (P.comp P.symm) P.left.unit := by
  rw [IsCyclic, rightMate_left_unit, leftMate_left_unit]

/-- The right mate of the unit of `g ⊣ f` is the counit of `f ⊣ g`.
@isnad1 id=eq.0h6v.s9.bdfcf05e261f from=translated src=- shape=5ba85f96 vocab=2c1e0a13
-/
theorem rightMate_right_unit (P : f ⊣⊢ g) :
    rightMate (id b) (P.symm.comp P) P.right.unit = P.left.counit :=
  rightMate_left_unit P.symm

/-- The left mate of the unit of `g ⊣ f` is the counit of `f ⊣ g`.
@isnad1 id=eq.0h6v.s9.e3441f777d36 from=translated src=- shape=5ba85f96 vocab=4b200128
-/
theorem leftMate_right_unit (P : f ⊣⊢ g) :
    leftMate (id b) (P.symm.comp P) P.right.unit = P.left.counit :=
  leftMate_left_unit P.symm

/-- The unit of `g ⊣ f` is cyclic for the biadjunctions `Biadjunction.id b` and
`P.symm.comp P`.
@isnad1 id=iscyclic.0h6v.s6.24f5cc4d95f8 from=translated src=- shape=dc443531 vocab=f072cead
-/
theorem isCyclic_right_unit (P : f ⊣⊢ g) : IsCyclic (id b) (P.symm.comp P) P.right.unit :=
  isCyclic_left_unit P.symm

/-- The right mate of the counit of `f ⊣ g` (a 2-morphism `g ≫ f ⟶ 𝟙 b`, with the
biadjunctions `P.symm.comp P : g ≫ f ⊣⊢ g ≫ f` and `Biadjunction.id b`) is the unit of
`g ⊣ f`.
@isnad1 id=eq.0h6v.s9.963b35f65eb0 from=translated src=- shape=12e48d93 vocab=2c1e0a13
-/
theorem rightMate_left_counit (P : f ⊣⊢ g) :
    rightMate (P.symm.comp P) (id b) P.left.counit = P.right.unit := by
  rw [← leftMate_right_unit P]
  exact rightMate_symm_leftMate (id b) (P.symm.comp P) P.right.unit

/-- The left mate of the counit of `f ⊣ g` is the unit of `g ⊣ f`.
@isnad1 id=eq.0h6v.s9.82a2d1deec7d from=translated src=- shape=12e48d93 vocab=4b200128
-/
theorem leftMate_left_counit (P : f ⊣⊢ g) :
    leftMate (P.symm.comp P) (id b) P.left.counit = P.right.unit := by
  rw [← rightMate_right_unit P]
  exact leftMate_symm_rightMate (id b) (P.symm.comp P) P.right.unit

/-- The counit of `f ⊣ g` is cyclic for the biadjunctions `P.symm.comp P` and
`Biadjunction.id b`.
@isnad1 id=iscyclic.0h6v.s6.08d8f2065e3b from=translated src=- shape=c44e3f92 vocab=c3d69f33
-/
theorem isCyclic_left_counit (P : f ⊣⊢ g) : IsCyclic (P.symm.comp P) (id b) P.left.counit := by
  rw [IsCyclic, rightMate_left_counit, leftMate_left_counit]

/-- The right mate of the counit of `g ⊣ f` is the unit of `f ⊣ g`.
@isnad1 id=eq.0h6v.s9.e5a061ec8ff4 from=translated src=- shape=13d8360a vocab=2c1e0a13
-/
theorem rightMate_right_counit (P : f ⊣⊢ g) :
    rightMate (P.comp P.symm) (id a) P.right.counit = P.left.unit :=
  rightMate_left_counit P.symm

/-- The left mate of the counit of `g ⊣ f` is the unit of `f ⊣ g`.
@isnad1 id=eq.0h6v.s9.a271e1268c9a from=translated src=- shape=13d8360a vocab=4b200128
-/
theorem leftMate_right_counit (P : f ⊣⊢ g) :
    leftMate (P.comp P.symm) (id a) P.right.counit = P.left.unit :=
  leftMate_left_counit P.symm

/-- The counit of `g ⊣ f` is cyclic for the biadjunctions `P.comp P.symm` and
`Biadjunction.id a`.
@isnad1 id=iscyclic.0h6v.s6.d06561ce9f72 from=translated src=- shape=26bf323d vocab=5c8b6890
-/
theorem isCyclic_right_counit (P : f ⊣⊢ g) :
    IsCyclic (P.comp P.symm) (id a) P.right.counit :=
  isCyclic_left_counit P.symm

end UnitCounit

/-! ## Coherence 2-morphisms -/

section Coherence

variable {e : B} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b} {f₃ : c ⟶ e} {g₃ : e ⟶ c}

/--
@isnad1 id=eq.0h14v.s10.2ec4e57cf7cc from=translated src=- shape=c8ee9aba vocab=84b47d06
-/
theorem rightMate_associator_hom (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    rightMate ((P.comp Q).comp R) (P.comp (Q.comp R)) (α_ f₁ f₂ f₃).hom =
      (α_ g₃ g₂ g₁).hom := by
  apply conjugateEquiv_eq_of_unit
  simp only [comp_left, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/--
@isnad1 id=eq.0h14v.s10.397ee257f67e from=translated src=- shape=c8ee9aba vocab=b44cd58f
-/
theorem leftMate_associator_hom (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    leftMate ((P.comp Q).comp R) (P.comp (Q.comp R)) (α_ f₁ f₂ f₃).hom =
      (α_ g₃ g₂ g₁).hom := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [comp_right, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/-- The associator is cyclic for the composite biadjunctions.
@isnad1 id=iscyclic.0h14v.s8.79395c91ff5d from=translated src=- shape=802bbbdf vocab=69033371
-/
theorem isCyclic_associator_hom (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    IsCyclic ((P.comp Q).comp R) (P.comp (Q.comp R)) (α_ f₁ f₂ f₃).hom := by
  rw [IsCyclic, rightMate_associator_hom, leftMate_associator_hom]

/--
@isnad1 id=iscyclic.0h14v.s8.e0ce8e3434ed from=translated src=- shape=c07c4e57 vocab=b548f5f8
-/
theorem isCyclic_associator_inv (P : f₁ ⊣⊢ g₁) (Q : f₂ ⊣⊢ g₂) (R : f₃ ⊣⊢ g₃) :
    IsCyclic (P.comp (Q.comp R)) ((P.comp Q).comp R) (α_ f₁ f₂ f₃).inv :=
  (isCyclic_associator_hom P Q R).iso_inv

/--
@isnad1 id=eq.0h6v.s9.b5795339bfbe from=translated src=- shape=60471809 vocab=cb7f8149
-/
theorem rightMate_leftUnitor_hom (P : f₁ ⊣⊢ g₁) :
    rightMate ((id a).comp P) P (λ_ f₁).hom = (ρ_ g₁).inv := by
  apply conjugateEquiv_eq_of_unit
  simp only [comp_left, id_left, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/--
@isnad1 id=eq.0h6v.s9.dbdffbc8cf09 from=translated src=- shape=60471809 vocab=8064e982
-/
theorem leftMate_leftUnitor_hom (P : f₁ ⊣⊢ g₁) :
    leftMate ((id a).comp P) P (λ_ f₁).hom = (ρ_ g₁).inv := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [comp_right, id_right, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/-- The left unitor is cyclic for the biadjunctions `(id a).comp P` and `P`.
@isnad1 id=iscyclic.0h6v.s7.d89475c69c2a from=translated src=- shape=2a9fc1b6 vocab=6c0ec20d
-/
theorem isCyclic_leftUnitor_hom (P : f₁ ⊣⊢ g₁) : IsCyclic ((id a).comp P) P (λ_ f₁).hom := by
  rw [IsCyclic, rightMate_leftUnitor_hom, leftMate_leftUnitor_hom]

/--
@isnad1 id=iscyclic.0h6v.s7.d790348aa972 from=translated src=- shape=7aff998a vocab=a7afc456
-/
theorem isCyclic_leftUnitor_inv (P : f₁ ⊣⊢ g₁) : IsCyclic P ((id a).comp P) (λ_ f₁).inv :=
  (isCyclic_leftUnitor_hom P).iso_inv

/--
@isnad1 id=eq.0h6v.s9.48a73b7728ca from=translated src=- shape=4209c986 vocab=cb7f8149
-/
theorem rightMate_rightUnitor_hom (P : f₁ ⊣⊢ g₁) :
    rightMate (P.comp (id b)) P (ρ_ f₁).hom = (λ_ g₁).inv := by
  apply conjugateEquiv_eq_of_unit
  simp only [comp_left, id_left, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/--
@isnad1 id=eq.0h6v.s9.ccadc6cc3357 from=translated src=- shape=4209c986 vocab=8064e982
-/
theorem leftMate_rightUnitor_hom (P : f₁ ⊣⊢ g₁) :
    leftMate (P.comp (id b)) P (ρ_ f₁).hom = (λ_ g₁).inv := by
  rw [leftMate, Equiv.symm_apply_eq]
  symm
  apply conjugateEquiv_eq_of_unit
  simp only [comp_right, id_right, Adjunction.id, Adjunction.comp_unit, Adjunction.compUnit]
  bicategory

/-- The right unitor is cyclic for the biadjunctions `P.comp (id b)` and `P`.
@isnad1 id=iscyclic.0h6v.s7.4ce08a802a05 from=translated src=- shape=5ad40bc1 vocab=a4557ae0
-/
theorem isCyclic_rightUnitor_hom (P : f₁ ⊣⊢ g₁) : IsCyclic (P.comp (id b)) P (ρ_ f₁).hom := by
  rw [IsCyclic, rightMate_rightUnitor_hom, leftMate_rightUnitor_hom]

/--
@isnad1 id=iscyclic.0h6v.s7.1aad3124c930 from=translated src=- shape=b25da1bd vocab=b4404ee2
-/
theorem isCyclic_rightUnitor_inv (P : f₁ ⊣⊢ g₁) : IsCyclic P (P.comp (id b)) (ρ_ f₁).inv :=
  (isCyclic_rightUnitor_hom P).iso_inv

/-- `eqToHom` is cyclic for biadjunctions which agree along the equalities of 1-morphisms.
@isnad1 id=iscyclic.3h9v.s7.6d52a79ebaf0 from=translated src=- shape=a92130a1 vocab=6c25a6b0
-/
theorem isCyclic_eqToHom {f f' : a ⟶ b} {g g' : b ⟶ a} {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'}
    (hf : f = f') (hg : g = g') (hP : HEq P P') : IsCyclic P P' (eqToHom hf) := by
  subst hf hg
  cases eq_of_heq hP
  exact isCyclic_id P

end Coherence

end Biadjunction

end StringDiagrams
