import Tengoku.Seed.CategoryTheory.Localization.Predicate
import Tengoku.DgLean.DG.Category.Homotopy.ConeCochain
import Tengoku.DgLean.DG.Category.Homotopy.HomotopyCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The homotopy category of dg modules over a dg category as a localization

Let `C` be a category with dg Hom groups. This file shows that the quotient functor
`DG.CatModule.HomotopyCategory.quotient C : CatModule C ⥤ HomotopyCategory C` is a localization
functor for the class `DG.CatModule.homotopyEquivalences C` of homotopy equivalences
(`DG.CatModule.HomotopyCategory.quotient_isLocalization`). It is a port of
`DG.Homotopy.Localization` (the case of a dg ring).

The key point is `DG.CatModule.DGHomotopy.map_eq_of_inverts_homotopyEquivalences`: homotopic
morphisms `f g : M ⟶ N` become equal under any functor inverting homotopy equivalences. As a
cylinder of `M` we use the biproduct `M ⊞ cone (𝟙 M)`: the projection to `M` is a homotopy
equivalence since `cone (𝟙 M)` is contractible, it has the two sections `biprod.inl` and
`biprod.lift (𝟙 M) (inr (𝟙 M))`, and a homotopy from `f` to `g` gives a morphism
`M ⊞ cone (𝟙 M) ⟶ N` restricting to `f` and `g` along them.
-/

open scoped DG

open CategoryTheory Limits

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]

variable (C) in
/-- The homotopy equivalences of dg modules over `C`, as a class of morphisms of
`CatModule C`.-/
def homotopyEquivalences : MorphismProperty (CatModule.{w} C) :=
  fun M N f => ∃ e : DGHomotopyEquiv M N, e.hom = f

/--
@isnad1 id=homotopy.0h4v.s6.f40bf5f887f3 from=translated src=- shape=b3a6b3f4 vocab=70589d0b
-/
theorem homotopyEquivalences_of_equiv {M N : CatModule.{w} C} (e : DGHomotopyEquiv M N) :
    homotopyEquivalences C e.hom :=
  ⟨e, rfl⟩

namespace DGHomotopy

variable [DGCategory C]

/-- The auxiliary dg module `M ⊞ cone (𝟙 M)`, playing the role of a cylinder of `M`.-/
noncomputable abbrev cyl (M : CatModule.{w} C) : CatModule.{w} C :=
  M ⊞ cone (𝟙 M)

/-- The section `biprod.lift (𝟙 M) (inr (𝟙 M))` of the projection `M ⊞ cone (𝟙 M) ⟶ M`.-/
noncomputable def cylInr (M : CatModule.{w} C) : M ⟶ cyl M :=
  biprod.lift (𝟙 M) (cone.inr (𝟙 M))

/--
@isnad1 id=eq.0h2v.s7.fb6fac77244e from=translated src=- shape=c8c25c8e vocab=ba08f57b
-/
@[reassoc (attr := simp)]
theorem cylInr_fst (M : CatModule.{w} C) : cylInr M ≫ biprod.fst = 𝟙 M :=
  biprod.lift_fst _ _

/-- The projection `M ⊞ cone (𝟙 M) ⟶ M` is a homotopy equivalence, with inverse
`biprod.inl`.-/
noncomputable def cylProjHomotopyEquiv (M : CatModule.{w} C) :
    DGHomotopyEquiv (cyl M) M where
  hom := biprod.fst
  inv := biprod.inl
  homotopyHomInvId := by
    have h : Homotopic (biprod.fst ≫ biprod.inl - 𝟙 (cyl M)) 0 := by
      have h₀ : biprod.fst ≫ biprod.inl - 𝟙 (cyl M) =
          -(biprod.snd ≫ 𝟙 (cone (𝟙 M)) ≫ biprod.inr) := by
        rw [← biprod.total, Category.id_comp]
        abel
      rw [h₀, ← neg_zero]
      refine Homotopic.neg ?_
      have h₁ := ((cone.isContractible_id M).comp_right (biprod.inr (X := M))).comp_left
        (biprod.snd (X := M))
      rwa [zero_comp, comp_zero] at h₁
    exact (Homotopic.iff_sub.mpr h).some
  homotopyInvHomId := DGHomotopy.ofEq biprod.inl_fst

variable {M N : CatModule.{w} C} {f g : M ⟶ N} (h : DGHomotopy f g)

/-- The morphism `cone (𝟙 M) ⟶ N` with restriction `g - f` to `N`, built from the
homotopy.-/
noncomputable def cylDescCone : cone (𝟙 M) ⟶ N :=
  cone.desc (𝟙 M) h.symm.hom (g - f) (by
    rw [Category.id_comp, Cochain.ofHom_sub, h.symm.ofHom_eq, add_sub_cancel_right])

/-- The morphism `M ⊞ cone (𝟙 M) ⟶ N` restricting to `f` along `biprod.inl` and to `g` along
`cylInr`.-/
noncomputable def cylDesc : cyl M ⟶ N :=
  biprod.desc f (cylDescCone h)

/--
@isnad1 id=eq.0h6v.s8.ca9ee0d5f6fd from=translated src=- shape=d20756d8 vocab=01a91ebe
-/
theorem inl_cylDesc : biprod.inl ≫ cylDesc h = f :=
  biprod.inl_desc _ _

/--
@isnad1 id=eq.0h6v.s7.21841938cd1d from=translated src=- shape=fa687635 vocab=52a360e1
-/
theorem cylInr_cylDesc : cylInr M ≫ cylDesc h = g := by
  rw [cylInr, cylDesc, biprod.lift_desc, Category.id_comp, cylDescCone, cone.inr_desc,
    add_sub_cancel]

include h in
/-- Homotopic morphisms of dg modules are identified by every functor inverting homotopy
equivalences.
@isnad1 id=eq.1h8v.s7.b5accd1d7117 from=translated src=- shape=98048b25 vocab=c6bd51d0
-/
theorem map_eq_of_inverts_homotopyEquivalences {E : Type*} [Category E]
    (F : CatModule.{w} C ⥤ E) (hF : (homotopyEquivalences C).IsInvertedBy F) :
    F.map f = F.map g := by
  have := hF _ (homotopyEquivalences_of_equiv (cylProjHomotopyEquiv M))
  have h₀ : F.map (biprod.inl : M ⟶ cyl M) = F.map (cylInr M) := by
    rw [← cancel_mono (F.map (cylProjHomotopyEquiv M).hom), ← F.map_comp, ← F.map_comp]
    exact congrArg F.map (biprod.inl_fst.trans (cylInr_fst M).symm)
  calc F.map f = F.map (biprod.inl ≫ cylDesc h) := by rw [inl_cylDesc]
    _ = F.map (cylInr M ≫ cylDesc h) := by rw [F.map_comp, F.map_comp, h₀]
    _ = F.map g := by rw [cylInr_cylDesc]

end DGHomotopy

namespace HomotopyCategory

variable (C)

/-- Homotopy equivalences become isomorphisms in the homotopy category.
@isnad1 id=isinvert.0h1v.s5.ecf367ea314f from=translated src=- shape=a059026b vocab=68f26701
-/
theorem quotient_inverts_homotopyEquivalences :
    (homotopyEquivalences.{w} C).IsInvertedBy (quotient C) := by
  rintro M N f ⟨e, rfl⟩
  exact (isoOfHomotopyEquiv e).isIso_hom

variable [DGCategory C]

/-- The homotopy category satisfies the universal property of the localization of the category
of dg modules at the homotopy equivalences.-/
def strictUniversalPropertyFixedTargetQuotient (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (quotient C)
      (homotopyEquivalences.{w} C) E where
  inverts := quotient_inverts_homotopyEquivalences C
  lift F hF := CategoryTheory.Quotient.lift _ F fun _ _ _ _ h =>
    h.some.map_eq_of_inverts_homotopyEquivalences F hF
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

end HomotopyCategory

end CatModule

end DG
