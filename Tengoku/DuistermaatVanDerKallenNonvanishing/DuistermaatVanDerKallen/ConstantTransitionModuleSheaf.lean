import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.ConstantTransitionSheaf
import Tengoku.Seed.Algebra.Category.ModuleCat.Abelian
import Tengoku.Seed.Algebra.Category.ModuleCat.FilteredColimits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Linear constant-transition atlases yield sheaves of integral modules.
The underlying sheaf is the previously constructed sheaf of fiberwise sections. -/

open Set CategoryTheory TopologicalSpace Opposite
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

structure ConstantTransitionModuleAtlas (X : TopCat.{0}) (H : X → ModuleCat.{0} ℤ) where
  Index : Type
  domain : Index → Opens X
  model : Index → ModuleCat.{0} ℤ
  coord : ∀ i, ∀ x : domain i, H x.val ≃ₗ[ℤ] model i
  cover : ∀ x : X, ∃ i, x ∈ domain i
  transition : ∀ i j (x y : X) (hxi : x ∈ domain i) (hxj : x ∈ domain j)
    (hyi : y ∈ domain i) (hyj : y ∈ domain j) (v : model i),
    coord j ⟨x, hxj⟩ ((coord i ⟨x, hxi⟩).symm v) =
      coord j ⟨y, hyj⟩ ((coord i ⟨y, hyi⟩).symm v)

namespace ConstantTransitionModuleAtlas
variable {X : TopCat.{0}} {H : X → ModuleCat.{0} ℤ} (A : ConstantTransitionModuleAtlas X H)

def toAtlas : ConstantTransitionAtlas X (fun x => H x) where
  Index := A.Index
  domain := A.domain
  model i := A.model i
  coord i x := (A.coord i x).toEquiv
  cover := A.cover
  transition := A.transition

/-- Zero is locally constant in the linear coordinates.-/
theorem section_zero (U : Opens X) : A.toAtlas.sectionPredicate.pred (fun _ : U => 0) := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x.val
  refine ⟨U ⊓ A.domain i, ⟨x.property, hi⟩, Opens.infLELeft _ _, i, inf_le_right, (0 : A.model i), ?_⟩
  intro y
  exact (A.coord i ⟨y.val, y.property.2⟩).map_zero

/-- Local coordinate constancy is preserved by integer scalar multiplication.-/
theorem section_smul {U : Opens X} (r : ℤ) {f : ∀ x : U, H x.val}
    (hf : A.toAtlas.sectionPredicate.pred f) :
    A.toAtlas.sectionPredicate.pred (fun x => r • f x) := by
  apply A.toAtlas.prelocal.sheafify_inductionOn' (fun a => r • a) _ hf
  intro V g hg
  obtain ⟨i, hVi, v, he⟩ := hg
  change A.Index at i
  change V ≤ A.domain i at hVi
  change A.model i at v
  refine ⟨i, hVi, r • v, ?_⟩
  intro x
  change A.coord i ⟨x.val, hVi x.property⟩ (r • g x) = r • v
  have he' : A.coord i ⟨x.val, hVi x.property⟩ (g x) = v := he x
  exact (map_zsmul (A.coord i ⟨x.val, hVi x.property⟩) r (g x)).trans
    (congrArg (r • ·) he')

/-- Addition is local even when the two sections use different charts.-/
theorem section_add {U : Opens X} {f g : ∀ x : U, H x.val}
    (hf : A.toAtlas.sectionPredicate.pred f) (hg : A.toAtlas.sectionPredicate.pred g) :
    A.toAtlas.sectionPredicate.pred (fun x => f x + g x) := by
  apply A.toAtlas.prelocal.sheafify_inductionOn₂ A.toAtlas.prelocal A.toAtlas.prelocal
    (fun a b => a + b) _ hf hg
  intro V W a b ha hb p
  obtain ⟨i, hVi, v, he⟩ := ha
  change A.Index at i
  change V ≤ A.domain i at hVi
  change A.model i at v
  let jV := Opens.infLELeft V W
  let jW := Opens.infLERight V W
  have hWi : V ⊓ W ≤ A.domain i := inf_le_left.trans hVi
  have hb' := A.toAtlas.prelocal.res jW b hb
  refine ⟨V ⊓ W, jV, jW, p.property, i, hWi,
    v + A.coord i ⟨p.val, hWi p.property⟩ (b (jW p)), ?_⟩
  intro x
  change A.coord i ⟨x.val, hWi x.property⟩ (a (jV x) + b (jW x)) = _
  exact ((A.coord i ⟨x.val, hWi x.property⟩).map_add _ _).trans
    (congrArg₂ (· + ·) (he (jV x))
      (A.toAtlas.prelocal_coordinate_constant (fun z => b (jW z)) hb' i hWi x p))

/-- The module of locally constant coordinate sections over an open set.-/
def sections (U : Opens X) : Submodule ℤ (∀ x : U, H x.val) where
  carrier := {f | A.toAtlas.sectionPredicate.pred f}
  zero_mem' := A.section_zero U
  add_mem' := A.section_add
  smul_mem' := A.section_smul

def presheaf : TopCat.Presheaf (ModuleCat.{0} ℤ) X where
  obj U := ModuleCat.of ℤ (A.sections U.unop)
  map i := ModuleCat.ofHom
    { toFun := fun f => ⟨fun x => f.val (i.unop x), A.toAtlas.sectionPredicate.res i.unop f.val f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := by ext f x; rfl
  map_comp _ _ := by ext f x; rfl

/-- Forgetting the module operations gives exactly the sheaf of dependent
sections already constructed, so its verified gluing applies.-/
theorem presheaf_forget : A.presheaf ⋙ forget (ModuleCat.{0} ℤ) = A.toAtlas.sheaf.presheaf := rfl

/-- The sheaf of modules underlying the integral local system.-/
def sheaf : TopCat.Sheaf (ModuleCat.{0} ℤ) X := by
  refine ⟨A.presheaf, ?_⟩
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp' (forget (ModuleCat.{0} ℤ)) A.presheaf).mpr
  rw [A.presheaf_forget]
  exact A.toAtlas.sheaf.property

/-- Evaluation of a section is an integral linear map.-/
def sectionEval (U : Opens X) (x : U) : A.sections U →ₗ[ℤ] H x.val where
  toFun f := f.val x
  map_add' _ _ := rfl
  map_smul' r f := (int_smul_eq_zsmul (inferInstance : Module ℤ (H x.val)) r (f.val x)).symm

/-- On a connected chart, evaluation identifies its section module with
any one fiber.-/
def sectionLinearEquiv (i : A.Index) [PreconnectedSpace (A.domain i)] (x : A.domain i) :
    A.sections (A.domain i) ≃ₗ[ℤ] H x.val := by
  let : PreconnectedSpace (A.toAtlas.domain i) := inferInstanceAs (PreconnectedSpace (A.domain i))
  exact LinearEquiv.ofBijective (A.sectionEval _ x)
    ⟨A.toAtlas.section_eval_injective i x, A.toAtlas.section_eval_surjective i x⟩

/-- Compatible linear evaluations define the stalk evaluation cocone.-/
def evaluationCocone (x : X) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ A.presheaf) where
  pt := H x
  ι :=
    { app U := ModuleCat.ofHom (A.sectionEval U.unop.val ⟨x, U.unop.property⟩)
      naturality _ _ _ := by ext f; rfl }

/-- The actual module-valued stalk evaluates linearly in the fiber.-/
def stalkEval (x : X) : A.presheaf.stalk x ⟶ H x :=
  Limits.colimit.desc _ (A.evaluationCocone x)

theorem stalkEval_germ (U : Opens X) (x : X) (hx : x ∈ U) (s : A.sections U) :
    A.stalkEval x (A.presheaf.germ U x hx s) = s.val ⟨x, hx⟩ := by
  exact Limits.colimit.ι_desc_apply (A.evaluationCocone x) (op ⟨U, hx⟩) s

theorem stalkEval_surjective (x : X) : Function.Surjective (A.stalkEval x) := by
  intro v
  obtain ⟨i, hi⟩ := A.cover x
  let s : A.sections (A.domain i) :=
    ⟨A.toAtlas.constantSection i (A.coord i ⟨x, hi⟩ v), A.toAtlas.constantSection_local i _⟩
  refine ⟨A.presheaf.germ (A.domain i) x hi s, ?_⟩
  exact (A.stalkEval_germ _ x hi s).trans ((A.coord i ⟨x, hi⟩).symm_apply_apply v)

theorem stalkEval_injective (x : X) : Function.Injective (A.stalkEval x) := by
  intro a b hab
  obtain ⟨U, hxU, s, rfl⟩ := A.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, t, rfl⟩ := A.presheaf.exists_germ_eq b
  have he : s.val ⟨x, hxU⟩ = t.val ⟨x, hxV⟩ :=
    (A.stalkEval_germ U x hxU s).symm.trans (hab.trans (A.stalkEval_germ V x hxV t))
  have hst : A.toAtlas.sheaf.presheaf.germ U x hxU s =
      A.toAtlas.sheaf.presheaf.germ V x hxV t := by
    apply A.toAtlas.stalkToFiber_injective x
    exact (TopCat.stalkToFiber_germ A.toAtlas.sectionPredicate U x hxU s).trans
      (he.trans (TopCat.stalkToFiber_germ A.toAtlas.sectionPredicate V x hxV t).symm)
  obtain ⟨W, hxW, iU, iV, heW⟩ := A.toAtlas.sheaf.presheaf.germ_eq x hxU hxV s t hst
  exact A.presheaf.germ_ext W hxW iU iV heW

/-- The actual module stalk, including its operations, is the specified fiber.-/
def stalkLinearEquiv (x : X) : A.presheaf.stalk x ≃ₗ[ℤ] H x :=
  LinearEquiv.ofBijective (A.stalkEval x).hom
    ⟨A.stalkEval_injective x, A.stalkEval_surjective x⟩

/-- Every germ extends uniquely across a connected coordinate patch, also
as a statement about the actual module-valued stalk.-/
theorem germ_bijective (i : A.Index) [PreconnectedSpace (A.domain i)]
    (x : X) (hx : x ∈ A.domain i) :
    Function.Bijective (A.presheaf.germ (A.domain i) x hx) := by
  constructor
  · intro s t hst
    apply (A.sectionLinearEquiv i ⟨x, hx⟩).injective
    exact (A.stalkEval_germ _ x hx s).symm.trans
      ((congrArg (A.stalkEval x) hst).trans (A.stalkEval_germ _ x hx t))
  · intro a
    obtain ⟨s, hs⟩ := (A.sectionLinearEquiv i ⟨x, hx⟩).surjective (A.stalkEval x a)
    refine ⟨s, A.stalkEval_injective x ?_⟩
    exact (A.stalkEval_germ _ x hx s).trans hs

/-- The germ map on a connected coordinate patch is an integral linear
isomorphism onto the stalk.-/
def germLinearEquiv (i : A.Index) [PreconnectedSpace (A.domain i)]
    (x : X) (hx : x ∈ A.domain i) :
    A.sections (A.domain i) ≃ₗ[ℤ] A.presheaf.stalk x :=
  LinearEquiv.ofBijective (A.presheaf.germ (A.domain i) x hx).hom (A.germ_bijective i x hx)

/-- The étalé projection of the module-valued sheaf itself is a covering.-/
theorem isCoveringMap_module_etale (hconnected : ∀ i, PreconnectedSpace (A.domain i)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := A.presheaf)) := by
  apply TopCat.Presheaf.EtaleSpace.isCoveringMap_base
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  let : PreconnectedSpace (A.domain i) := hconnected i
  exact ⟨A.domain i, hi, fun y hy => A.germ_bijective i y hy⟩

/-- The germ of one section, viewed as a map into the étalé space.-/
def sectionEtaleMap (U : Opens X) (s : A.sections U) : U → A.presheaf.EtaleSpace :=
  fun x => ⟨x.val, A.presheaf.germ U x.val x.property s⟩

/-- A section over a connected atlas chart gives a continuous germ map.-/
theorem sectionEtaleMap_continuous (i : A.Index) [PreconnectedSpace (A.domain i)]
    (s : A.sections (A.domain i)) : Continuous (A.sectionEtaleMap _ s) := by
  rw [continuous_iff_continuousAt]
  intro x
  let e := TopCat.Presheaf.EtaleSpace.homeomorph (F := A.presheaf) (A.domain i)
    (A.germ_bijective i) x.val x.property
  have hc := ((continuous_subtype_val.comp e.symm.continuous).comp
    (continuous_id.prodMk (continuous_const (y :=
      WithTopology.toTopology ⊥ (A.presheaf.germ (A.domain i) x.val x.property s)))))
  have he : (fun y : A.domain i => (e.symm (y,
      WithTopology.toTopology ⊥ (A.presheaf.germ (A.domain i) x.val x.property s))).val) =
      A.sectionEtaleMap _ s := by
    funext y
    dsimp [e, TopCat.Presheaf.EtaleSpace.homeomorph, sectionEtaleMap]
    congr 2
    exact Function.leftInverse_surjInv (A.germ_bijective i x.val x.property) s
  dsimp only [Function.comp_def, id_eq] at hc
  rw [he] at hc
  exact hc.continuousAt
end ConstantTransitionModuleAtlas
end
end DuistermaatVanDerKallen
