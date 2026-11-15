import Tengoku.Seed.AlgebraicGeometry.ResidueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

def schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hcomm : h ≫ f = f)
    (s : S) :
    Limits.pullback f (S.fromSpecResidueField s)
      ⟶ Limits.pullback f (S.fromSpecResidueField s) :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ h) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, hcomm, Limits.pullback.condition])

/--
@isnad1 id=eq.1h5v.s7.69ef9a88ab3a from=translated src=- shape=5d702cce vocab=637790ab
-/
@[simp] theorem schemeFibreEndo_fst {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ h :=
  Limits.pullback.lift_fst _ _ _

/--
@isnad1 id=eq.1h5v.s7.906c1e491441 from=translated src=- shape=5a119b74 vocab=d1856fa1
-/
@[simp] theorem schemeFibreEndo_snd {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X)
    (hcomm : h ≫ f = f) (s : S) :
    schemeFibreEndo f h hcomm s ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ :=
  Limits.pullback.lift_snd _ _ _

end AlgebraicGeometry
