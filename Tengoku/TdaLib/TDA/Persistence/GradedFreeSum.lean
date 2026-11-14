import Tengoku.TdaLib.TDA.Persistence.GradedFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Disjoint unions of graded free modules

A free module on a disjoint union of graded families has the coproduct
universal property. The maps and their laws are stated through generators,
which also makes them usable when defining homogeneous relations.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence.GradedFree

open CategoryTheory

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- Disjoint union, retaining each generator's grade.-/
def GradedGenerators.sum (W V : GradedGenerators.{v,w} P) : GradedGenerators.{v,w} P where
  Carrier := Sum W.Carrier V.Carrier
  grade := Sum.elim W.grade V.grade

variable (W V : GradedGenerators.{v,w} P)

/-- Include the first free family in the free module on the union.-/
noncomputable def sumInl : module (R := R) W ⟶ module (W.sum V) :=
  lift W (module (W.sum V)) (fun g => birth (W.sum V) (Sum.inl g))

/-- Include the second free family in the free module on the union.-/
noncomputable def sumInr : module (R := R) V ⟶ module (W.sum V) :=
  lift V (module (W.sum V)) (fun g => birth (W.sum V) (Sum.inr g))

/--
@isnad1 id=eq.0h5v.s9.1dd0398d3f95 from=translated src=- shape=a8399f03 vocab=247a8d1b
-/
@[simp] theorem sumInl_birth (g : W.Carrier) :
    (sumInl (R := R) W V).app (W.grade g) (birth W g) =
      birth (W.sum V) (Sum.inl g) :=
  lift_birth W (module (W.sum V)) _ g

/--
@isnad1 id=eq.0h5v.s9.0fa1d7b0b77a from=translated src=- shape=ec463ffd vocab=fd291b9e
-/
@[simp] theorem sumInr_birth (g : V.Carrier) :
    (sumInr (R := R) W V).app (V.grade g) (birth V g) =
      birth (W.sum V) (Sum.inr g) :=
  lift_birth V (module (W.sum V)) _ g

/-- At every available grade, the first inclusion retains its basis vector.
@isnad1 id=eq.1h6v.s9.f437ba8fb73c from=translated src=- shape=7d0f5040 vocab=99726924
-/
theorem sumInl_generator (g : W.Carrier) {a : P} (h : W.grade g ≤ a) :
    (sumInl (R := R) W V).app a (generator W g h) =
      generator (W.sum V) (Sum.inl g) h := by
  have hn := (sumInl (R := R) W V).naturality (homOfLE h)
  have hv := congrArg (fun q => q (birth (R := R) W g)) hn
  change (sumInl W V).app a (generator W g h) =
    (module (R := R) (W.sum V)).map (homOfLE h)
      ((sumInl W V).app (W.grade g) (birth W g)) at hv
  rw [sumInl_birth] at hv
  exact hv

/-- At every available grade, the second inclusion retains its basis vector.
@isnad1 id=eq.1h6v.s9.69a65d40efcf from=translated src=- shape=8a1229e3 vocab=07534d9a
-/
theorem sumInr_generator (g : V.Carrier) {a : P} (h : V.grade g ≤ a) :
    (sumInr (R := R) W V).app a (generator V g h) =
      generator (W.sum V) (Sum.inr g) h := by
  have hn := (sumInr (R := R) W V).naturality (homOfLE h)
  have hv := congrArg (fun q => q (birth (R := R) V g)) hn
  change (sumInr W V).app a (generator V g h) =
    (module (R := R) (W.sum V)).map (homOfLE h)
      ((sumInr W V).app (V.grade g) (birth V g)) at hv
  rw [sumInr_birth] at hv
  exact hv

/-- A pair of maps out of free families extends uniquely across their union.-/
noncomputable def sumDesc {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M) :
    module (R := R) (W.sum V) ⟶ M :=
  lift (W.sum V) M (fun z => match z with
    | .inl x => f.app (W.grade x) (birth W x)
    | .inr y => g.app (V.grade y) (birth V y))

/--
@isnad1 id=eq.0h8v.s10.b4224290dd79 from=translated src=- shape=c6768ad4 vocab=54982644
-/
@[simp] theorem sumDesc_birth_inl {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M)
    (x : W.Carrier) :
    (sumDesc W V f g).app (W.grade x) (birth (W.sum V) (Sum.inl x)) =
      f.app (W.grade x) (birth W x) :=
  lift_birth (W.sum V) M _ (Sum.inl x)

/--
@isnad1 id=eq.0h8v.s10.0bf74f5dd22a from=translated src=- shape=41fddbea vocab=24bc6788
-/
@[simp] theorem sumDesc_birth_inr {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M)
    (y : V.Carrier) :
    (sumDesc W V f g).app (V.grade y) (birth (W.sum V) (Sum.inr y)) =
      g.app (V.grade y) (birth V y) :=
  lift_birth (W.sum V) M _ (Sum.inr y)

/--
@isnad1 id=eq.0h7v.s7.51707fff80ea from=translated src=- shape=f54303cb vocab=b297afe7
-/
@[simp] theorem sumInl_sumDesc {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M) :
    sumInl W V ≫ sumDesc W V f g = f := by
  have hleft := lift_unique W M (fun x => f.app (W.grade x) (birth W x))
    (sumInl W V ≫ sumDesc W V f g) (by intro x; simp)
  exact hleft.trans
    (lift_unique W M (fun x => f.app (W.grade x) (birth W x)) f (fun _ => rfl)).symm

/--
@isnad1 id=eq.0h7v.s7.c633c9398375 from=translated src=- shape=73c0debc vocab=4912d815
-/
@[simp] theorem sumInr_sumDesc {M : PModule.{u,v,max u w} R P}
    (f : module (R := R) W ⟶ M) (g : module (R := R) V ⟶ M) :
    sumInr W V ≫ sumDesc W V f g = g := by
  have hright := lift_unique V M (fun y => g.app (V.grade y) (birth V y))
    (sumInr W V ≫ sumDesc W V f g) (by intro y; simp)
  exact hright.trans
    (lift_unique V M (fun y => g.app (V.grade y) (birth V y)) g (fun _ => rfl)).symm

/-- The inclusion maps jointly determine a map out of a union-free module.
@isnad1 id=eq.0h6v.s7.f93568fd5766 from=translated src=- shape=dcda8a9c vocab=67c1590f
-/
theorem sumDesc_unique {M : PModule.{u,v,max u w} R P}
    (h : module (R := R) (W.sum V) ⟶ M) :
    sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h) = h := by
  let s := fun z : (W.sum V).Carrier =>
    h.app ((W.sum V).grade z) (birth (W.sum V) z)
  have hdesc := lift_unique (W.sum V) M s
    (sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h)) (by
      intro z
      cases z with
      | inl x =>
        change (sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h)).app
          (W.grade x) (birth (W.sum V) (Sum.inl x)) =
            h.app (W.grade x) (birth (W.sum V) (Sum.inl x))
        rw [sumDesc_birth_inl]
        change h.app (W.grade x) ((sumInl W V).app (W.grade x) (birth W x)) = _
        rw [sumInl_birth]
      | inr y =>
        change (sumDesc W V (sumInl W V ≫ h) (sumInr W V ≫ h)).app
          (V.grade y) (birth (W.sum V) (Sum.inr y)) =
            h.app (V.grade y) (birth (W.sum V) (Sum.inr y))
        rw [sumDesc_birth_inr]
        change h.app (V.grade y) ((sumInr W V).app (V.grade y) (birth V y)) = _
        rw [sumInr_birth])
  exact hdesc.trans (lift_unique (W.sum V) M s h (fun _ => rfl)).symm

/-- Equality of maps out of the sum-free module reduces to both families.
@isnad1 id=eq.2h7v.s8.2410e255d3d3 from=translated src=- shape=5c76b46d vocab=76260314
-/
theorem sumHom_ext {M : PModule.{u,v,max u w} R P}
    {f g : module (R := R) (W.sum V) ⟶ M}
    (hW : sumInl W V ≫ f = sumInl W V ≫ g)
    (hV : sumInr W V ≫ f = sumInr W V ≫ g) : f = g := by
  calc
    f = sumDesc W V (sumInl W V ≫ f) (sumInr W V ≫ f) :=
      (sumDesc_unique W V f).symm
    _ = sumDesc W V (sumInl W V ≫ g) (sumInr W V ≫ g) := by rw [hW, hV]
    _ = g := sumDesc_unique W V g

/-- Hom maps from the union-free module are exactly pairs of Hom maps from
its two summands.-/
noncomputable def sumHomEquiv (M : PModule.{u,v,max u w} R P) :
    (module (R := R) (W.sum V) ⟶ M) ≃
      ((module (R := R) W ⟶ M) × (module (R := R) V ⟶ M)) where
  toFun h := (sumInl W V ≫ h, sumInr W V ≫ h)
  invFun p := sumDesc W V p.1 p.2
  left_inv := sumDesc_unique W V
  right_inv := by
    intro p
    cases p
    simp

/-- Interchanging the two graded families gives a canonical free-module isomorphism.-/
noncomputable def sumCommIso :
    module (R := R) (W.sum V) ≅ module (V.sum W) where
  hom := sumDesc W V (sumInr V W) (sumInl V W)
  inv := sumDesc V W (sumInr W V) (sumInl W V)
  hom_inv_id := by
    apply sumHom_ext W V <;>
      simp only [← Category.assoc, sumInl_sumDesc, sumInr_sumDesc, Category.comp_id]
  inv_hom_id := by
    apply sumHom_ext V W <;>
      simp only [← Category.assoc, sumInl_sumDesc, sumInr_sumDesc, Category.comp_id]

end TDA.Persistence.GradedFree
