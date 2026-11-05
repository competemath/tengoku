module

public import Tengoku.Seed.CategoryTheory.Galois.IsFundamentalgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

open CategoryTheory

/--
@isnad1 id=eq.0h2v.s6.7ba12f9654cf from=translated src=- shape=a1304611 vocab=b423d539
-/
@[simp]
lemma CategoryTheory.Aut.one_hom {C : Type*} [Category C] (X : C) :
    (1 : Aut X).hom = (1 : End X) := rfl

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category C] (F : C ⥤ FintypeCat)

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)][IsNaturalSMul F G]

/--
@isnad1 id=eq.0h3v.s7.94c149b36284 from=translated src=- shape=bbf9b80c vocab=75a23c96
-/
lemma ker_toAut : (toAut F G).ker = ⨅ (X : C) (x : F.obj X), MulAction.stabilizer G x := by
  ext g : 1
  simp [MonoidHom.mem_ker, Subgroup.mem_iInf, Aut.ext_iff, NatTrans.ext'_iff, funext_iff,
    FintypeCat.hom_ext_iff]

variable  [GaloisCategory C] [FiberFunctor F]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ X, ContinuousSMul G (F.obj X)]

end CategoryTheory.PreGaloisCategory
