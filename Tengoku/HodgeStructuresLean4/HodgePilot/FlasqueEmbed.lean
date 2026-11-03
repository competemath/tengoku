import Tengoku.Seed.Topology.Sheaves.Flasque
import Tengoku.Seed.Topology.Sheaves.Stalks
import Tengoku.Seed.Topology.Sheaves.SheafOfFunctions
import Tengoku.Seed.CategoryTheory.Sites.LocallyInjective
import Tengoku.Seed.CategoryTheory.Preadditive.Injective.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Godement embedding: every abelian sheaf embeds in a flasque sheaf

For an abelian sheaf `F` on a topological space `X` we construct the concrete
Godement sheaf `godementSheaf F`: its sections over an open `U` are the
dependent families `∀ x : U, F.stalk x` of stalk elements, with restriction
given by restricting families.  This is the sections-level description of the
product over all points `x` of the skyscraper sheaves at `x` carrying the
stalks of `F` (a skyscraper at `x` contributes its value exactly over the
opens containing `x`); the categorical product itself is neither constructed
nor needed here.

Main results:

* `godementSheaf_isFlasque` — the Godement sheaf is flasque: a family of
  stalk elements on a smaller open extends by zero to any larger open;
* `toGodementSheaf` — the canonical morphism sending a section to its family
  of germs, a monomorphism (`mono_toGodementSheaf`) by germ separation on a
  sheaf (`TopCat.Presheaf.section_ext`);
* `godementEmbedFlasque` — **every abelian sheaf admits a monomorphism into
  a flasque sheaf**;
* `isFlasque_of_retract`, `isFlasque_of_injective_of_monoIntoFlasque` —
  flasqueness is stable under retracts, and an injective sheaf admitting a
  monomorphism into a flasque sheaf is flasque (the monomorphism splits);
* `isFlasque_of_injective` — **every injective abelian sheaf is flasque**,
  by splitting the Godement embedding;
* `isFlasque_sheafPullback`, `isFlasque_restrict` — the restriction of a
  flasque sheaf along an open embedding (in particular, to an open subspace)
  is flasque, since the naive pullback acts by composition with the
  image functor on opens.

## Claim discipline

Everything in this module is generic sheaf theory over an arbitrary
topological space.  Flasqueness is asserted only for the Godement sheaves
constructed here, for retracts of flasque sheaves, and for injective sheaves
via the splitting argument — each at exactly the proven scope.  No acyclicity
of any concrete sheaf is stated, no cohomology of anything is computed, and
no identification of sheaf cohomology with any other theory is stated or
implied.  Nothing here makes the Hodge conjecture statable.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v w

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.FlasqueEmbed

variable {X : TopCat.{u}}

/-! ## The concrete Godement presheaf -/

/-- The Godement presheaf of an abelian sheaf `F`: sections over `U` are the
dependent families `∀ x : U, F.stalk x` of stalk elements, restriction is
restriction of families.  This is the sections-level description of the
product of the skyscraper sheaves at the stalks of `F`; no categorical
product is constructed.-/
def godementPresheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (∀ x : U.unop, ToType (F.presheaf.stalk x.1))
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun g x => g (i.unop x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The underlying type-valued presheaf of the Godement presheaf is the
presheaf of dependent functions into the stalks.-/
def godementCompForgetIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.presheafToTypes X (fun x => ToType (F.presheaf.stalk x)) ≅
      godementPresheaf F ⋙ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The Godement presheaf is a sheaf: a compatible family of families of
stalk elements glues pointwise.  Proven by transport from Mathlib's sheaf of
(not necessarily continuous) dependent functions.
@isnad1 id=issheaf.0h2v.s3.b4bd31ab49e7 from=translated src=- shape=83a97904 vocab=c6d8ce8e
-/
theorem godementPresheaf_isSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (godementPresheaf F).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget AddCommGrpCat.{u})
    (godementPresheaf F)).mpr
    (TopCat.Presheaf.isSheaf_of_iso (godementCompForgetIso F)
      (TopCat.Presheaf.toTypes_isSheaf X _))

/-- The Godement sheaf of an abelian sheaf `F`: sections over `U` are the
families `∀ x : U, F.stalk x`.-/
def godementSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨godementPresheaf F, godementPresheaf_isSheaf F⟩

/-- The Godement sheaf is flasque: a family of stalk elements over a smaller
open extends by zero to a family over a larger open.
@isnad1 id=isflasqu.0h2v.s3.b94e1298c554 from=translated src=- shape=a1e5fe81 vocab=6cf2237d
-/
instance godementSheaf_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (godementSheaf F).IsFlasque where
  epi {U V} i := by
    refine (AddCommGrpCat.epi_iff_surjective _).mpr fun g => ?_
    classical
    refine ⟨fun x => if h : x.1 ∈ V.unop then g ⟨x.1, h⟩ else 0, ?_⟩
    funext x
    exact dite_eq_left x.2

/-! ## The canonical monomorphism into the Godement sheaf -/

/-- The canonical presheaf morphism from `F` to its Godement presheaf: a
section goes to its family of germs.-/
def toGodementPresheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.presheaf ⟶ godementPresheaf F where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s x => F.presheaf.germ U.unop x.1 x.2 s
      map_zero' := by
        funext x
        exact map_zero _
      map_add' := fun s t => by
        funext x
        exact map_add _ s t }
  naturality {U V} i := by
    ext s
    funext x
    exact F.presheaf.germ_res_apply' i x.1 x.2 s

/-- The canonical morphism from an abelian sheaf to its Godement sheaf.-/
def toGodementSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F ⟶ godementSheaf F :=
  ⟨toGodementPresheaf F⟩

/-- Componentwise injectivity of the canonical morphism into the Godement
sheaf: two sections of a sheaf with the same germ at every point of `U` are
equal.
@isnad1 id=injectiv.0h3v.s11.663d092b9502 from=translated src=- shape=1aeab8e2 vocab=d1595746
-/
theorem toGodementSheaf_app_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (U : (Opens X)ᵒᵖ) :
    Function.Injective ((toGodementSheaf F).hom.app U) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F U.unop
  intro x hx
  exact congrFun h ⟨x, hx⟩

/-- The canonical morphism into the Godement sheaf is a monomorphism.
@isnad1 id=mono.0h2v.s4.7dcbe3f381b6 from=translated src=- shape=41d93968 vocab=f76106a0
-/
instance mono_toGodementSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Mono (toGodementSheaf F) :=
  Sheaf.mono_of_injective _ (toGodementSheaf_app_injective F)

/-- **The Godement embedding.**  Every abelian sheaf on a topological space
admits a monomorphism into a flasque sheaf.
@isnad1 id=ex.0h2v.s6.713dc23b112d from=translated src=- shape=732d397a vocab=f74e9612
-/
theorem godementEmbedFlasque (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ∃ (G : TopCat.Sheaf AddCommGrpCat.{u} X) (m : F ⟶ G),
      Mono m ∧ G.IsFlasque :=
  ⟨godementSheaf F, toGodementSheaf F, inferInstance, inferInstance⟩

/-! ## Retract stability and flasqueness of injective sheaves -/

set_option backward.isDefEq.respectTransparency false in
/-- A retract of a flasque abelian sheaf is flasque.
@isnad1 id=isflasqu.1h5v.s6.6ea6ecd20a76 from=translated src=- shape=13a27fa2 vocab=adb3bfd7
-/
theorem isFlasque_of_retract {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ι : F ⟶ G) (r : G ⟶ F) (hri : ι ≫ r = 𝟙 F) [G.IsFlasque] :
    F.IsFlasque := by
  refine ⟨fun {U V} i => ?_⟩
  refine (AddCommGrpCat.epi_iff_surjective _).mpr fun s => ?_
  obtain ⟨t, ht⟩ :=
    (AddCommGrpCat.epi_iff_surjective (G.1.map i)).mp inferInstance
      (ι.hom.app V s)
  refine ⟨r.hom.app U t, ?_⟩
  have hnat : F.1.map i (r.hom.app U t) = r.hom.app V (G.1.map i t) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      r.hom.naturality]
  rw [hnat, ht]
  calc r.hom.app V (ι.hom.app V s)
      = (ι ≫ r).hom.app V s := (ConcreteCategory.comp_apply _ _ s).symm
    _ = (𝟙 F : F ⟶ F).hom.app V s := by rw [hri]
    _ = s := rfl

set_option backward.isDefEq.respectTransparency false in
/-- An injective abelian sheaf admitting a monomorphism into a flasque sheaf
is flasque: the monomorphism splits by injectivity, and flasqueness passes to
retracts.
@isnad1 id=isflasqu.0h4v.s6.f2bb91f05443 from=translated src=- shape=9a488ad0 vocab=dee7c225
-/
theorem isFlasque_of_injective_of_monoIntoFlasque
    {I G : TopCat.Sheaf AddCommGrpCat.{u} X} [Injective I] (m : I ⟶ G)
    [Mono m] [G.IsFlasque] : I.IsFlasque :=
  isFlasque_of_retract m (Injective.factorThru (𝟙 I) m)
    (Injective.comp_factorThru _ _)

/-- **Every injective abelian sheaf is flasque**: split the Godement
embedding by injectivity and transport flasqueness along the retract.
@isnad1 id=isflasqu.1h2v.s4.e2e3872a81ec from=translated src=- shape=e2016878 vocab=96861976
-/
theorem isFlasque_of_injective (I : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hI : Injective I) : I.IsFlasque :=
  haveI := hI
  isFlasque_of_injective_of_monoIntoFlasque (toGodementSheaf I)

/-! ## Restriction along an open embedding -/

/-- The restriction of a flasque sheaf along an open embedding is flasque:
the naive pullback `Topology.IsOpenEmbedding.sheafPullback` acts on the
underlying presheaf by composition with the image functor on opens, so every
restriction map of the pullback is a restriction map of the original
sheaf.
@isnad1 id=isflasqu.1h5v.s7.1bb2eb8c2d9e from=translated src=- shape=ad8c8166 vocab=fff0a12a
-/
theorem isFlasque_sheafPullback {C : Type v} [Category.{u} C]
    {Y : TopCat.{u}} {f : Y ⟶ X} (hf : Topology.IsOpenEmbedding f)
    (F : TopCat.Sheaf C X) [F.IsFlasque] :
    ((hf.sheafPullback C).obj F).IsFlasque where
  epi {_ _} i := inferInstanceAs (Epi (F.1.map (hf.functor.op.map i)))

/-- The restriction of a flasque sheaf to an open subspace is flasque.
@isnad1 id=isflasqu.0h4v.s7.e8b5110831b2 from=translated src=- shape=333a8cb3 vocab=72c0a7e6
-/
theorem isFlasque_restrict {C : Type v} [Category.{u} C] (W : Opens X)
    (F : TopCat.Sheaf C X) [F.IsFlasque] :
    ((W.isOpenEmbedding.sheafPullback C).obj F).IsFlasque :=
  isFlasque_sheafPullback W.isOpenEmbedding F

end HodgePilot.FlasqueEmbed
