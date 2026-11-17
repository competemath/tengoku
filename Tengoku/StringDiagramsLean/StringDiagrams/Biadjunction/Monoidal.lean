import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Trace
import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Linear
import Tengoku.Seed.CategoryTheory.Bicategory.SingleObj
import Tengoku.Seed.CategoryTheory.Monoidal.Rigid.Basic
import Tengoku.Seed.CategoryTheory.Monoidal.Linear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Biadjunctions in monoidal categories

A monoidal category `C` is a bicategory with one object, `MonoidalSingleObj C` (Mathlib), whose
1-morphisms are the objects of `C` (composition is `⊗`) and whose 2-morphisms are the
morphisms of `C`; whiskering, associators and unitors are those of `C`, definitionally. Under
this identification an exact pairing `ExactPairing X Y` (coevaluation `𝟙_ C ⟶ X ⊗ Y`,
evaluation `Y ⊗ X ⟶ 𝟙_ C`) is the same as a bicategorical adjunction `X ⊣ Y`
(`MonoidalDuality.adjunction`, `MonoidalDuality.exactPairing`), and a biduality (exact pairings
`X Y` and `Y X`) is a biadjunction (`MonoidalDuality.biadjunction`).

This file states the monoidal versions of the definitions and main results of
`StringDiagrams.Biadjunction`, obtained by transfer:

* `MonoidalDuality.rightMate Y Y' f`, `MonoidalDuality.leftMate Y Y' f : Y' ⟶ Y` for
  `f : X ⟶ X'`; they agree with Mathlib's `rightAdjointMate` and `leftAdjointMate` for the
  chosen right and left duals (`rightMate_eq_rightAdjointMate`,
  `leftMate_eq_leftAdjointMate`);
* `MonoidalDuality.IsCyclic Y Y' f`, closed under composition (`IsCyclic.comp`), and, in a
  preadditive (resp. linear) monoidal category, under sums (resp. scalar multiples);
* traces `MonoidalDuality.rightTrace Y f = η_ X Y ≫ f ▷ Y ≫ ε_ Y X` and
  `MonoidalDuality.leftTrace Y f = η_ Y X ≫ Y ◁ f ≫ ε_ X Y` in `End (𝟙_ C)`, with the
  cyclicity `rightTrace Y (f ≫ g) = rightTrace Y' (g ≫ f)` when `f` or `g` is cyclic, the
  relation of traces with mates, and additivity/linearity.
-/

namespace StringDiagrams

open CategoryTheory MonoidalCategory Bicategory

universe w v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- `leftZigzag` with its coherence isomorphism made explicit.
@isnad1 id=eq.0h7v.s8.d2f39950bb37 from=translated src=- shape=cd3740d2 vocab=d6225821
-/
theorem leftZigzag_eq {B : Type*} [Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    leftZigzag η ε = η ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε := by
  bicategory

/-- `rightZigzag` with its coherence isomorphism made explicit.
@isnad1 id=eq.0h7v.s8.2d325ace771d from=translated src=- shape=da1561ff vocab=a9852c2b
-/
theorem rightZigzag_eq {B : Type*} [Bicategory B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    rightZigzag η ε = g ◁ η ≫ (α_ g f g).inv ≫ ε ▷ g := by
  bicategory

namespace MonoidalDuality

/-- The one-object bicategory `MonoidalSingleObj C`, with its universe fixed.-/
abbrev SingleObj (C : Type u) [Category.{v} C] [MonoidalCategory C] : Type :=
  MonoidalSingleObj C

/-- The unique object of the bicategory `MonoidalSingleObj C`.-/
local notation "⋆" => (MonoidalSingleObj.star C : SingleObj C)

/-- An exact pairing of `X` and `Y` as an adjunction `X ⊣ Y` in the one-object bicategory
`MonoidalSingleObj C`.-/
def adjunction (X Y : C) [ExactPairing X Y] :
    @Bicategory.Adjunction (SingleObj C) _ ⋆ ⋆ X Y where
  unit := η_ X Y
  counit := ε_ X Y
  left_triangle := by
    rw [leftZigzag_eq]
    exact ExactPairing.evaluation_coevaluation X Y
  right_triangle := by
    rw [rightZigzag_eq]
    exact ExactPairing.coevaluation_evaluation X Y

/--
@isnad1 id=eq.0h3v.s7.551026a8e44b from=translated src=- shape=b16b8933 vocab=e3bce5d4
-/
@[simp]
theorem adjunction_unit (X Y : C) [ExactPairing X Y] : (adjunction X Y).unit = η_ X Y := rfl

/--
@isnad1 id=eq.0h3v.s7.9dc953ad4c3c from=translated src=- shape=0eb31c80 vocab=2b65b729
-/
@[simp]
theorem adjunction_counit (X Y : C) [ExactPairing X Y] : (adjunction X Y).counit = ε_ X Y :=
  rfl

/-- An adjunction `X ⊣ Y` in `MonoidalSingleObj C` as an exact pairing of `X` and `Y`.-/
@[instance_reducible]
def exactPairing {X Y : C} (adj : @Bicategory.Adjunction (SingleObj C) _ ⋆ ⋆ X Y) :
    ExactPairing X Y where
  coevaluation' := adj.unit
  evaluation' := adj.counit
  coevaluation_evaluation' := by
    have h := adj.right_triangle
    rw [rightZigzag_eq] at h
    exact h
  evaluation_coevaluation' := by
    have h := adj.left_triangle
    rw [leftZigzag_eq] at h
    exact h

/-- A biduality (exact pairings of `X` with `Y` and of `Y` with `X`) as a biadjunction in
`MonoidalSingleObj C`.-/
def biadjunction (X Y : C) [ExactPairing X Y] [ExactPairing Y X] :
    @Biadjunction (SingleObj C) _ ⋆ ⋆ X Y where
  left := adjunction X Y
  right := adjunction Y X

/--
@isnad1 id=eq.0h3v.s6.1d8b3beab8e3 from=translated src=- shape=7b6e5bf5 vocab=7c614906
-/
theorem biadjunction_symm (X Y : C) [ExactPairing X Y] [ExactPairing Y X] :
    (biadjunction X Y).symm = biadjunction Y X := rfl

/-! ## Mates -/

section Mates

variable {X X' X'' : C} (Y Y' Y'' : C)

/-- The right mate `Y' ⟶ Y` of `f : X ⟶ X'`, for exact pairings `X Y` and `X' Y'`.-/
def rightMate [ExactPairing X Y] [ExactPairing X' Y'] (f : X ⟶ X') : Y' ⟶ Y :=
  Bicategory.conjugateEquiv (adjunction X' Y') (adjunction X Y) f

/-- The left mate `Y' ⟶ Y` of `f : X ⟶ X'`, for exact pairings `Y X` and `Y' X'`.-/
def leftMate [ExactPairing Y X] [ExactPairing Y' X'] (f : X ⟶ X') : Y' ⟶ Y :=
  (Bicategory.conjugateEquiv (adjunction Y X) (adjunction Y' X')).symm f

/--
@isnad1 id=eq.0h6v.s8.dd9883ddf635 from=translated src=- shape=abc9d067 vocab=a1d459b1
-/
theorem rightMate_eq [ExactPairing X Y] [ExactPairing X' Y'] (f : X ⟶ X') :
    rightMate Y Y' f = (ρ_ Y').inv ≫ Y' ◁ η_ X Y ≫ Y' ◁ f ▷ Y ≫ (α_ Y' X' Y).inv ≫
      ε_ X' Y' ▷ Y ≫ (λ_ Y).hom := by
  have h := Bicategory.conjugateEquiv_apply' (adjunction X' Y') (adjunction X Y) f
  exact h

/--
@isnad1 id=eq.0h6v.s8.3bd1cd28d245 from=translated src=- shape=6b2d56b0 vocab=6f89a003
-/
theorem leftMate_eq [ExactPairing Y X] [ExactPairing Y' X'] (f : X ⟶ X') :
    leftMate Y Y' f = (λ_ Y').inv ≫ η_ Y X ▷ Y' ≫ (α_ Y X Y').hom ≫ Y ◁ f ▷ Y' ≫
      Y ◁ ε_ Y' X' ≫ (ρ_ Y).hom := by
  have h := Bicategory.conjugateEquiv_symm_apply' (adjunction Y X) (adjunction Y' X') f
  exact h

/-- For the chosen right duals, the right mate is Mathlib's `rightAdjointMate`.
@isnad1 id=eq.0h4v.s6.4d70220ac1cf from=translated src=- shape=745e4102 vocab=8270bbbb
-/
theorem rightMate_eq_rightAdjointMate [HasRightDual X] [HasRightDual X'] (f : X ⟶ X') :
    rightMate (Xᘁ) (X'ᘁ) f = rightAdjointMate f := by
  rw [rightMate_eq, rightAdjointMate]

/-- For the chosen left duals, the left mate is Mathlib's `leftAdjointMate`.
@isnad1 id=eq.0h4v.s6.2f228b74c23b from=translated src=- shape=745e4102 vocab=741b7d9b
-/
theorem leftMate_eq_leftAdjointMate [HasLeftDual X] [HasLeftDual X'] (f : X ⟶ X') :
    leftMate (ᘁX) (ᘁX') f = leftAdjointMate f := by
  rw [leftMate_eq, leftAdjointMate]
  monoidal

/--
@isnad1 id=eq.0h6v.s10.beba00609be6 from=translated src=- shape=83980520 vocab=e555bdac
-/
theorem rightMate_biadjunction [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] (f : X ⟶ X') :
    Biadjunction.rightMate (biadjunction X Y) (biadjunction X' Y') f = rightMate Y Y' f := rfl

/--
@isnad1 id=eq.0h6v.s10.606d31206286 from=translated src=- shape=83980520 vocab=4faf989d
-/
theorem leftMate_biadjunction [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] (f : X ⟶ X') :
    Biadjunction.leftMate (biadjunction X Y) (biadjunction X' Y') f = leftMate Y Y' f := rfl

/--
@isnad1 id=eq.0h3v.s5.e0a46919fc4d from=translated src=- shape=7b4d895d vocab=8f272f73
-/
@[simp]
theorem rightMate_id [ExactPairing X Y] : rightMate Y Y (𝟙 X) = 𝟙 Y :=
  Bicategory.conjugateEquiv_id _

/--
@isnad1 id=eq.0h3v.s5.483cd5b72eca from=translated src=- shape=541ad4ef vocab=a2c20f99
-/
@[simp]
theorem leftMate_id [ExactPairing Y X] : leftMate Y Y (𝟙 X) = 𝟙 Y :=
  Bicategory.conjugateEquiv_symm_id _

/--
@isnad1 id=eq.0h9v.s6.9de144afb963 from=translated src=- shape=74341dd3 vocab=94e6bd08
-/
theorem rightMate_comp [ExactPairing X Y] [ExactPairing X' Y'] [ExactPairing X'' Y'']
    (f : X ⟶ X') (g : X' ⟶ X'') :
    rightMate Y Y'' (f ≫ g) = rightMate Y' Y'' g ≫ rightMate Y Y' f :=
  (Bicategory.conjugateEquiv_comp _ _ _ _ _).symm

/--
@isnad1 id=eq.0h9v.s6.b48c03605ec4 from=translated src=- shape=a2f410ff vocab=c583865b
-/
theorem leftMate_comp [ExactPairing Y X] [ExactPairing Y' X'] [ExactPairing Y'' X'']
    (f : X ⟶ X') (g : X' ⟶ X'') :
    leftMate Y Y'' (f ≫ g) = leftMate Y' Y'' g ≫ leftMate Y Y' f :=
  (Bicategory.conjugateEquiv_symm_comp _ _ _ _ _).symm

/-- A morphism `f : X ⟶ X'` between objects with bidualities is cyclic if its right and left
mates agree.-/
def IsCyclic [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y'] [ExactPairing Y' X']
    (f : X ⟶ X') : Prop :=
  rightMate Y Y' f = leftMate Y Y' f

/--
@isnad1 id=iff.0h6v.s6.ba6d370b5d9a from=translated src=- shape=947edc3e vocab=c0dbcdce
-/
theorem isCyclic_iff [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] (f : X ⟶ X') :
    IsCyclic Y Y' f ↔ (biadjunction X Y).IsCyclic (biadjunction X' Y') f := Iff.rfl

/--
@isnad1 id=iscyclic.0h3v.s5.f945f84b87bb from=translated src=- shape=cd09ca4a vocab=85cda2a8
-/
theorem isCyclic_id [ExactPairing X Y] [ExactPairing Y X] : IsCyclic Y Y (𝟙 X) :=
  (isCyclic_iff Y Y (𝟙 X)).2 (Biadjunction.isCyclic_id (biadjunction X Y))

variable {Y Y' Y''} in
/--
@isnad1 id=iscyclic.2h9v.s7.7340196f1318 from=translated src=- shape=1fda4f89 vocab=5cbe729c
-/
theorem IsCyclic.comp [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] [ExactPairing X'' Y''] [ExactPairing Y'' X''] {f : X ⟶ X'}
    {g : X' ⟶ X''} (hf : IsCyclic Y Y' f) (hg : IsCyclic Y' Y'' g) :
    IsCyclic Y Y'' (f ≫ g) :=
  (isCyclic_iff Y Y'' (f ≫ g)).2
    (Biadjunction.IsCyclic.comp ((isCyclic_iff Y Y' f).1 hf) ((isCyclic_iff Y' Y'' g).1 hg))

/-- The mates of a morphism with respect to the exchanged bidualities, in the opposite
rotational direction, recover the morphism.
@isnad1 id=eq.0h6v.s6.5b6dc8c106f9 from=translated src=- shape=1be1bed6 vocab=a45f8acd
-/
theorem rightMate_leftMate [ExactPairing Y X] [ExactPairing Y' X'] (f : X ⟶ X') :
    rightMate X' X (leftMate Y Y' f) = f :=
  Equiv.apply_symm_apply _ f

/--
@isnad1 id=eq.0h6v.s6.d3cd2c7f9d3c from=translated src=- shape=c631da40 vocab=a45f8acd
-/
theorem leftMate_rightMate [ExactPairing X Y] [ExactPairing X' Y'] (f : X ⟶ X') :
    leftMate X' X (rightMate Y Y' f) = f :=
  Equiv.symm_apply_apply _ f

variable {Y Y'} in
/-- The right mate of a cyclic morphism is cyclic, for the exchanged bidualities.
@isnad1 id=iscyclic.1h6v.s6.ef904577905c from=translated src=- shape=992b878f vocab=88ad9b63
-/
theorem IsCyclic.rightMate [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y']
    [ExactPairing Y' X'] {f : X ⟶ X'} (hf : IsCyclic Y Y' f) :
    IsCyclic X' X (MonoidalDuality.rightMate Y Y' f) :=
  Biadjunction.IsCyclic.rightMate (P := biadjunction X Y) (P' := biadjunction X' Y') hf

end Mates

/-! ## Traces -/

section Traces

variable {X X' : C} (Y Y' : C)

/-- The right trace `η_ X Y ≫ f ▷ Y ≫ ε_ Y X` of `f : X ⟶ X`.-/
def rightTrace [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Y ≫ f ▷ Y ≫ ε_ Y X

/-- The left trace `η_ Y X ≫ Y ◁ f ≫ ε_ X Y` of `f : X ⟶ X`.-/
def leftTrace [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ Y X ≫ Y ◁ f ≫ ε_ X Y

/--
@isnad1 id=eq.0h4v.s7.d25eb8c935c8 from=translated src=- shape=a8f66ef6 vocab=09cbce5f
-/
theorem rightTrace_biadjunction [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) :
    (biadjunction X Y).rightTrace f = rightTrace Y f := rfl

/--
@isnad1 id=eq.0h4v.s7.d407571c0517 from=translated src=- shape=a8f66ef6 vocab=ed856fde
-/
theorem leftTrace_biadjunction [ExactPairing X Y] [ExactPairing Y X] (f : X ⟶ X) :
    (biadjunction X Y).leftTrace f = leftTrace Y f := rfl

/--
@isnad1 id=eq.0h3v.s6.6ec57a793dbe from=translated src=- shape=fe2b83bb vocab=99ac32c6
-/
theorem rightTrace_id [ExactPairing X Y] [ExactPairing Y X] :
    rightTrace Y (𝟙 X) = η_ X Y ≫ ε_ Y X := by
  simp [rightTrace]

/--
@isnad1 id=eq.0h3v.s6.157d5a38d2f8 from=translated src=- shape=6564fe88 vocab=72317e23
-/
theorem leftTrace_id [ExactPairing X Y] [ExactPairing Y X] :
    leftTrace Y (𝟙 X) = η_ Y X ≫ ε_ X Y := by
  simp [leftTrace]

variable {Y Y'}

variable [ExactPairing X Y] [ExactPairing Y X] [ExactPairing X' Y'] [ExactPairing Y' X']

/--
@isnad1 id=eq.1h7v.s7.6f5278152913 from=translated src=- shape=34993b41 vocab=c1b05aa0
-/
theorem rightTrace_comp_comm_of_isCyclic_left {f : X ⟶ X'} (hf : IsCyclic Y Y' f)
    (g : X' ⟶ X) : rightTrace Y (f ≫ g) = rightTrace Y' (g ≫ f) :=
  Biadjunction.rightTrace_comp_comm_of_isCyclic_left (P := biadjunction X Y)
    (P' := biadjunction X' Y') hf g

/--
@isnad1 id=eq.1h7v.s7.19463865edd1 from=translated src=- shape=c3f0b316 vocab=c1b05aa0
-/
theorem rightTrace_comp_comm_of_isCyclic_right (f : X ⟶ X') {g : X' ⟶ X}
    (hg : IsCyclic Y' Y g) : rightTrace Y (f ≫ g) = rightTrace Y' (g ≫ f) :=
  Biadjunction.rightTrace_comp_comm_of_isCyclic_right (P := biadjunction X Y)
    (P' := biadjunction X' Y') f hg

/--
@isnad1 id=eq.1h7v.s7.956a4e9c251c from=translated src=- shape=34993b41 vocab=feb0f131
-/
theorem leftTrace_comp_comm_of_isCyclic_left {f : X ⟶ X'} (hf : IsCyclic Y Y' f)
    (g : X' ⟶ X) : leftTrace Y (f ≫ g) = leftTrace Y' (g ≫ f) :=
  Biadjunction.leftTrace_comp_comm_of_isCyclic_left (P := biadjunction X Y)
    (P' := biadjunction X' Y') hf g

/--
@isnad1 id=eq.1h7v.s7.2e1ed0adc5d8 from=translated src=- shape=c3f0b316 vocab=feb0f131
-/
theorem leftTrace_comp_comm_of_isCyclic_right (f : X ⟶ X') {g : X' ⟶ X}
    (hg : IsCyclic Y' Y g) : leftTrace Y (f ≫ g) = leftTrace Y' (g ≫ f) :=
  Biadjunction.leftTrace_comp_comm_of_isCyclic_right (P := biadjunction X Y)
    (P' := biadjunction X' Y') f hg

/-- The right trace of `f` is the left trace of its right mate.
@isnad1 id=eq.0h4v.s6.d596f479c14c from=translated src=- shape=f60e7af1 vocab=2f01eb3c
-/
theorem rightTrace_eq_leftTrace_rightMate (f : X ⟶ X) :
    rightTrace Y f = leftTrace X (rightMate Y Y f) :=
  Biadjunction.rightTrace_eq_leftTrace_rightMate (biadjunction X Y) f

/-- The right trace of `f` is the left trace of its left mate.
@isnad1 id=eq.0h4v.s6.494e954831e1 from=translated src=- shape=f60e7af1 vocab=5c790d5c
-/
theorem rightTrace_eq_leftTrace_leftMate (f : X ⟶ X) :
    rightTrace Y f = leftTrace X (leftMate Y Y f) :=
  Biadjunction.rightTrace_eq_leftTrace_leftMate (biadjunction X Y) f

/-- The left trace of `f` is the right trace of its right mate.
@isnad1 id=eq.0h4v.s6.132751d16adc from=translated src=- shape=f60e7af1 vocab=2f01eb3c
-/
theorem leftTrace_eq_rightTrace_rightMate (f : X ⟶ X) :
    leftTrace Y f = rightTrace X (rightMate Y Y f) :=
  Biadjunction.leftTrace_eq_rightTrace_rightMate (biadjunction X Y) f

/-- The left trace of `f` is the right trace of its left mate.
@isnad1 id=eq.0h4v.s6.5c985999953d from=translated src=- shape=f60e7af1 vocab=5c790d5c
-/
theorem leftTrace_eq_rightTrace_leftMate (f : X ⟶ X) :
    leftTrace Y f = rightTrace X (leftMate Y Y f) :=
  Biadjunction.leftTrace_eq_rightTrace_leftMate (biadjunction X Y) f

end Traces

/-! ## Linear structure -/

section Linear

instance instPreadditiveHom [Preadditive C] (a b : MonoidalSingleObj C) :
    Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive C)

instance instLinearHom (R : Type*) [Semiring R] [Preadditive C] [Linear R C]
    (a b : MonoidalSingleObj C) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R C)

instance [Preadditive C] [MonoidalPreadditive C] :
    LocallyPreadditive (MonoidalSingleObj C) where
  whiskerLeft_add f _ _ η θ := MonoidalPreadditive.whiskerLeft_add (C := C) (X := f) η θ
  add_whiskerRight η θ h := MonoidalPreadditive.add_whiskerRight (C := C) (X := h) η θ

instance (R : Type*) [Semiring R] [Preadditive C] [Linear R C] [MonoidalPreadditive C]
    [MonoidalLinear R C] :
    LocallyLinear R (MonoidalSingleObj C) where
  whiskerLeft_smul f _ _ r η := MonoidalLinear.whiskerLeft_smul (C := C) f r η
  smul_whiskerRight r η h := MonoidalLinear.smul_whiskerRight (C := C) r η h

variable [Preadditive C] [MonoidalPreadditive C] {X X' : C} {Y Y' : C}

/--
@isnad1 id=eq.0h7v.s8.01fde6369c75 from=translated src=- shape=0910b825 vocab=829df5c3
-/
theorem rightMate_add [ExactPairing X Y] [ExactPairing X' Y'] (f g : X ⟶ X') :
    rightMate Y Y' (f + g) = rightMate Y Y' f + rightMate Y Y' g := by
  simp only [rightMate_eq, MonoidalPreadditive.whiskerLeft_add,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

/--
@isnad1 id=eq.0h7v.s8.0ecf44bbfe6b from=translated src=- shape=3165d1a1 vocab=840e7da6
-/
theorem leftMate_add [ExactPairing Y X] [ExactPairing Y' X'] (f g : X ⟶ X') :
    leftMate Y Y' (f + g) = leftMate Y Y' f + leftMate Y Y' g := by
  simp only [leftMate_eq, MonoidalPreadditive.whiskerLeft_add,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

variable [ExactPairing X Y] [ExactPairing Y X]

/--
@isnad1 id=iscyclic.2h7v.s7.7ec80fe6fdb0 from=translated src=- shape=f4e08ff7 vocab=ff19a4ba
-/
theorem IsCyclic.add [ExactPairing X' Y'] [ExactPairing Y' X'] {f g : X ⟶ X'}
    (hf : IsCyclic Y Y' f) (hg : IsCyclic Y Y' g) : IsCyclic Y Y' (f + g) := by
  rw [IsCyclic, rightMate_add, leftMate_add, hf, hg]

/--
@isnad1 id=eq.0h5v.s8.86f0dd9ca834 from=translated src=- shape=cd943081 vocab=7c72bf4a
-/
theorem rightTrace_add (f g : X ⟶ X) : rightTrace Y (f + g) = rightTrace Y f + rightTrace Y g :=
  Biadjunction.rightTrace_add (biadjunction X Y) f g

/--
@isnad1 id=eq.0h5v.s8.1996c237b2ab from=translated src=- shape=cd943081 vocab=4380a301
-/
theorem leftTrace_add (f g : X ⟶ X) : leftTrace Y (f + g) = leftTrace Y f + leftTrace Y g :=
  Biadjunction.leftTrace_add (biadjunction X Y) f g

variable {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]

/--
@isnad1 id=eq.0h6v.s9.018cf36ae0df from=translated src=- shape=3913f996 vocab=8de711f1
-/
theorem rightTrace_smul (r : R) (f : X ⟶ X) : rightTrace Y (r • f) = r • rightTrace Y f :=
  Biadjunction.rightTrace_smul (biadjunction X Y) r f

/--
@isnad1 id=eq.0h6v.s9.2ab4bd021c62 from=translated src=- shape=3913f996 vocab=0ea34146
-/
theorem leftTrace_smul (r : R) (f : X ⟶ X) : leftTrace Y (r • f) = r • leftTrace Y f :=
  Biadjunction.leftTrace_smul (biadjunction X Y) r f

/--
@isnad1 id=iscyclic.1h8v.s8.2824aafb22b8 from=translated src=- shape=509c23d7 vocab=4b434425
-/
theorem IsCyclic.smul [ExactPairing X' Y'] [ExactPairing Y' X'] {f : X ⟶ X'}
    (hf : IsCyclic Y Y' f) (r : R) : IsCyclic Y Y' (r • f) :=
  Biadjunction.IsCyclic.smul (P := biadjunction X Y) (P' := biadjunction X' Y') hf r

end Linear

end MonoidalDuality

end StringDiagrams
