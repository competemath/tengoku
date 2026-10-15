/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Tengoku.LeanPool.LeanPool.Kurosh.SchreierCover
public import Tengoku

/-!
# Index Formula

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

universe u

namespace GraphCoveringTheory

noncomputable instance actionCategoryFintype (M : Type u) (A : Type u)
    [Monoid M] [MulAction M A] [Fintype A] : Fintype (ActionCategory M A) :=
  Fintype.ofEquiv A (ActionCategory.objEquiv M A)

noncomputable instance coverHomFintype (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] [Fintype α] (a b : CoverVertex α A) :
    Fintype (a ⟶ b) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun e : α => FreeGroup.of e • a.back = b.back)) (by simp)

/-- A Schreier edge is determined by its source and its free generator. -/
def coverGeneratorTotalEquiv (α : Type u) (A : Type u)
    [MulAction (FreeGroup α) A] :
    Quiver.Total (CoverVertex α A) ≃ A × α where
  toFun e := ⟨e.left.back, e.hom.val⟩
  invFun e :=
    ⟨(e.1 : CoverVertex α A),
      ((FreeGroup.of e.2 • e.1 : A) : CoverVertex α A),
      ⟨e.2, rfl⟩⟩
  left_inv e := by
    rcases e with ⟨x, y, ⟨e, h⟩⟩
    cases x with | mk x
    cases y with | mk y
    cases h
    rfl
  right_inv e := by
    rcases e with ⟨a, e⟩
    rfl

/-- The geodesic spanning tree in the symmetrified generating quiver, rooted at `r`. -/
noncomputable def freeGroupoidTree (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G] (r : G) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)) :=
  @geodesicSubtree
    (Symmetrify (IsFreeGroupoid.Generators G))
    (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators G))
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)

/-- The chosen geodesic spanning tree is an arborescence rooted at `r`. -/
@[reducible] noncomputable def freeGroupoidTreeArborescence (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G] (r : G) :
    Arborescence (freeGroupoidTree G r) := by
  dsimp [freeGroupoidTree]
  exact @Quiver.geodesicArborescence
    (Symmetrify (IsFreeGroupoid.Generators G)) _
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)

/-- The generators outside the chosen geodesic spanning tree. -/
noncomputable abbrev freeGroupoidGeneratorSet (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    (r : G) :
    Set (Quiver.Total (IsFreeGroupoid.Generators G)) :=
  (wideSubquiverEquivSetTotal
    (wideSubquiverSymmetrify (freeGroupoidTree G r)))ᶜ

noncomputable instance freeGroupoidGeneratorSetFintype (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Fintype (freeGroupoidGeneratorSet G r) := by
  classical
  exact inferInstance

/-- The generating edges outside a given wide subquiver and its reverse. -/
noncomputable abbrev generatorComplement (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) :
    Set (Quiver.Total (IsFreeGroupoid.Generators G)) :=
  (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ

noncomputable instance generatorComplementFintype (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))) :
    Fintype (generatorComplement G T) := by
  classical
  exact inferInstance

/--
@isnad1 id=eq.0h2v.s7.b215dc579c34 from=translated src=- shape=8de3b20c vocab=e418ccc6
-/
lemma generatorComplement_card (G : Type u) [Groupoid G]
    [IsFreeGroupoid G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)]
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)))
    [Arborescence T] :
    Fintype.card (generatorComplement G T) =
      Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G) := by
  classical
  let G' := IsFreeGroupoid.Generators G
  let S : Set (Quiver.Total G') :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  have hS : Fintype.card S = Fintype.card G' - 1 := by
    simpa [S] using (FiniteGraphFreeGroup.symmetrified_tree_set_card T)
  have hcomp : Fintype.card (Sᶜ : Set (Quiver.Total G')) =
      Fintype.card (Quiver.Total G') - Fintype.card S := by
    exact @Fintype.card_subtype_compl _ _ (fun e : Quiver.Total G' => e ∈ S)
      inferInstance inferInstance
  have htreele : Fintype.card S ≤ Fintype.card (Quiver.Total G') :=
    Fintype.card_subtype_le _
  have htreele' : Fintype.card G' - 1 ≤ Fintype.card (Quiver.Total G') := by
    rw [← hS]
    exact htreele
  have hGpos : 1 ≤ Fintype.card G' := by
    exact Fintype.card_pos_iff.mpr ⟨show G' from root T⟩
  change Fintype.card (Sᶜ : Set (Quiver.Total G')) =
    Fintype.card (Quiver.Total G') + 1 - Fintype.card G'
  rw [hcomp, hS]
  omega

/--
@isnad1 id=eq.0h2v.s6.725b31708d92 from=translated src=- shape=17990804 vocab=2c7a190c
-/
lemma freeGroupoidGeneratorSet_card (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Fintype.card (freeGroupoidGeneratorSet G r) =
      Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G) := by
  let : Arborescence (freeGroupoidTree G r) := freeGroupoidTreeArborescence G r
  exact generatorComplement_card G (freeGroupoidTree G r)

/--
@isnad1 id=nonempty.0h2v.s6.9273d52e6a67 from=translated src=- shape=7f4f4d1c vocab=4e5eff77
-/
theorem freeGroupoid_end_free_basis (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Nonempty (FreeGroupBasis (Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G))) (End r)) := by
  classical
  let T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G)) :=
    @geodesicSubtree
      (Symmetrify (IsFreeGroupoid.Generators G))
      (Quiver.symmetrifyQuiver (IsFreeGroupoid.Generators G))
      (show Symmetrify (IsFreeGroupoid.Generators G) from r)
      (@IsFreeGroupoid.generators_connected G _ _ _ r)
  let : Arborescence T := @Quiver.geodesicArborescence
    (Symmetrify (IsFreeGroupoid.Generators G)) _
    (show Symmetrify (IsFreeGroupoid.Generators G) from r)
    (@IsFreeGroupoid.generators_connected G _ _ _ r)
  let X := generatorComplement G T
  have hroot : (show G from root T) = r := by
    rfl
  let B : FreeGroupBasis X (End r) := by
    rw [← hroot]
    simpa [X, generatorComplement] using (FiniteGraphFreeGroup.spanningTreeBasis T)
  have hcard := generatorComplement_card G T
  let eX : X ≃ Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G)) :=
    hcard ▸ Fintype.equivFin X
  exact ⟨B.reindex eX⟩

/--
@isnad1 id=nonempty.0h2v.s7.0d839ff43498 from=translated src=- shape=9bf6ac36 vocab=63c81cf2
-/
theorem freeGroupoid_end_free_rank (G : Type u) [Groupoid G]
    [IsFreeGroupoid G] [IsConnected G]
    [Fintype (IsFreeGroupoid.Generators G)]
    [∀ a b : IsFreeGroupoid.Generators G, Fintype (a ⟶ b)] (r : G) :
    Nonempty (End r ≃* FreeGroup (Fin
      (Fintype.card (Quiver.Total (IsFreeGroupoid.Generators G)) + 1 -
        Fintype.card (IsFreeGroupoid.Generators G)))) := by
  rcases freeGroupoid_end_free_basis G r with ⟨B⟩
  exact ⟨B.repr⟩

end GraphCoveringTheory
