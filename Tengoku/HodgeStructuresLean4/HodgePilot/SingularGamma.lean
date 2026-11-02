import Tengoku.HodgeStructuresLean4.HodgePilot.SingularFineness
import Tengoku.HodgeStructuresLean4.HodgePilot.SingularResolution
import Tengoku.Seed.Topology.Compactness.Paracompact
import Tengoku.Seed.Topology.ShrinkingLemma
import Tengoku.Seed.Topology.Sheaves.LocallySurjective
import Tengoku.Seed.SetTheory.Cardinal.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Partition sums and `Γ`-surjectivity for the sheafified cochain sheaves

For a topological space `X` this file builds, on the site `Opens X`, the
section-summation layer over the first-vertex partition endomorphisms of
`HodgePilot.SingularFineness`, and the `Γ`-surjectivity lemma they support:

1. **sheaf-level disjoint vanishing** (`partitionEndoSheaf_app_disjoint`):
   over any open disjoint from `A`, the component of the sheafified partition
   endomorphism `partitionEndoSheaf X A n` is the zero morphism — proved
   stalkwise through the `toSheafify`-unit bridges and separated by germ
   locality; consequently the image of any section is supported in
   `closure A` (`partitionEndoSheaf_app_supp`);
2. **extension by zero** (`extendByZero`, with existence/uniqueness and
   restriction receipts): a section on `U` that dies on `U ⊓ Zc` extends
   uniquely by zero across the two-element cover `{U, Zc ⊓ V}` of any
   ambient open `V ≤ U ⊔ Zc`;
3. **locally finite summation of sections** (`locFinSum`, with restriction,
   uniqueness, adequate-restriction and additivity receipts): a family of
   sections of an abelian sheaf over `W`, each supported in a set `Z i`,
   sums by gluing along a cover pack each of whose members meets only a
   prescribed finite set of the supports; the sum is organized as finite
   partial sums per cover member, glued by the sheaf condition — no
   infinite sum of endomorphisms or of sections is ever formed;
4. **the partition-sum identity** (`partitionSum_eq_id`, with the
   sectionwise finite identity `sum_partitionEndoSheaf_app_apply`): for a
   partition of the ambient space into subsets whose closures form the
   support datum of a cover pack over `W`, the locally finite sum of the
   partition-endomorphism images of a section of the sheafified cochain
   sheaf over `W` recovers the section — per cover member the identity is a
   finite sum, by the exactly-one-set-per-simplex property of the
   first-vertex predicate;
5. **Lemma W** (`gammaSurjective_of_shortExact_sheafifiedCochain`): on a
   paracompact Hausdorff space, for every short exact sequence of abelian
   sheaves whose kernel is a sheafified cochain sheaf, the induced map on
   global sections of the epimorphism side is surjective.  Local lifts of a
   global section come from local surjectivity of sheaf epimorphisms; a
   partition subordinate to the lift cover is produced by precise
   refinement, the shrinking lemma, and disjointification along a
   well-order (`exists_subordinate_partition`); the overlap differences of
   the lifts are pulled back to the kernel sheaf sectionwise
   (`existsUnique_section_preimage`); and the classical correction family
   `cᵢ = Σⱼ E_{Aⱼ}(bᵢ - bⱼ)` is assembled from the partition
   endomorphisms by the extension-by-zero and locally-finite-summation
   toolkit (`exists_correction`), the triple-overlap cocycle bookkeeping
   being discharged by sectionwise injectivity of the kernel inclusion.

The entitled claim of this file, in full: *for every topological space the
sheafified cochain sheaves carry the partition-sum calculus above (sheaf-level
disjoint vanishing, extension by zero, locally finite summation of sections,
and the partition-sum identity), and on a paracompact Hausdorff space every
short exact sequence of abelian sheaves whose kernel is a sheafified cochain
sheaf has surjective induced map on global sections.*

**What remains open here**: no `Γ`-acyclicity of any sheaf is claimed or
approached in this file — `Γ`-surjectivity of one short exact sequence at a
time is all that is proven, and the abstract class-of-kernels plumbing and
any acyclicity statement are outside this file.  No statement below is about
the cohomology of anything; no cohomology group of any kind is mentioned,
computed, or related to another.  The word "singular" below refers
exclusively to the genuine presheaf-level singular-cochain objects
(`singularPresheafComplex` and its stalks); the sheaf-level carriers are
sheafified cochain sheaves and are never called singular.  **Nothing here
identifies sheaf cohomology with singular cohomology in any degree, and
nothing here makes the Hodge conjecture statable.**  Everything is at
universe `0`, forced by the `ModuleCat.{0} ℚ` coefficients of the house
carrier.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology
  HodgePilot.SingularCohomology HodgePilot.ContractibleSingular HodgePilot.SingularResolution
  HodgePilot.SingularFineness

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.SingularGamma

/-! ## Restriction helpers -/

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along a composite of inclusions of opens collapses (the target
inclusion may be given by any morphism, inclusions of opens being unique).-/
lemma res_res' {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {O P Q : Opens X} (i : O ⟶ P) (j : P ⟶ Q) (k : O ⟶ Q) (s : F.1.obj (op Q)) :
    F.1.map i.op (F.1.map j.op s) = F.1.map k.op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Components of a sheaf morphism commute with restriction, elementwise.-/
lemma app_res {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (η : F ⟶ G)
    {O P : Opens X} (i : O ⟶ P) (s : F.1.obj (op P)) :
    η.hom.app (op O) (F.1.map i.op s) = G.1.map i.op (η.hom.app (op P) s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, η.hom.naturality]

/-- Restriction of the zero section is zero.-/
lemma res_zero' {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {O P : Opens X} (i : O ⟶ P) :
    F.1.map i.op (0 : F.1.obj (op P)) = 0 :=
  map_zero _

/-- Restriction of a sum of sections is the sum of the restrictions.-/
lemma res_add' {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {O P : Opens X} (i : O ⟶ P) (a b : F.1.obj (op P)) :
    F.1.map i.op (a + b) = F.1.map i.op a + F.1.map i.op b :=
  map_add _ _ _

/-- Restriction of a finite sum of sections is the sum of the restrictions.-/
lemma res_sum' {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {O P : Opens X} (i : O ⟶ P) {ι' : Type*} (T : Finset ι') (t : ι' → F.1.obj (op P)) :
    F.1.map i.op (∑ a ∈ T, t a) = ∑ a ∈ T, F.1.map i.op (t a) :=
  map_sum _ _ _

/-- A finite sum of morphisms of abelian groups applied to an element.-/
lemma hom_sum_apply {A B : AddCommGrpCat.{0}} {ι' : Type*} (T : Finset ι')
    (f : ι' → (A ⟶ B)) (x : A) :
    (∑ a ∈ T, f a) x = ∑ a ∈ T, f a x := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

/-! ## Stalk bridges through sheafification -/

set_option backward.isDefEq.respectTransparency false in
/-- Every element of the stalk of a sheafification is the image of a stalk
element of the underlying presheaf under the unit (the unit is an isomorphism
on stalks).-/
lemma exists_stalk_toSheafify_preimage {X : TopCat.{0}}
    (F : TopCat.Presheaf AddCommGrpCat.{0} X) (x : ↑X)
    (z : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj F).1) :
    ∃ w : F.stalk x,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) F) w = z := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat F
  exact (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (toSheafify (Opens.grothendieckTopology X) F))).2 z

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a sheafified morphism, computed through the unit: the
elementwise naturality square of `toSheafify` on stalks.-/
lemma stalk_presheafToSheaf_map_toSheafify {X : TopCat.{0}}
    {F G : TopCat.Presheaf AddCommGrpCat.{0} X} (φ : F ⟶ G) (x : ↑X) (w : F.stalk x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map φ).hom)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          (toSheafify (Opens.grothendieckTopology X) F) w)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          (toSheafify (Opens.grothendieckTopology X) G)
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map φ w) := by
  have hsq : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) F)
      ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map φ).hom)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map φ
      ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) G) := by
    show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) F)
      ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (sheafifyMap (Opens.grothendieckTopology X) φ) = _
    rw [← Functor.map_comp, ← Functor.map_comp, ← toSheafify_naturality]
  exact ((ConcreteCategory.comp_apply _ _ w).symm.trans
    (congrArg (fun ψ => (ConcreteCategory.hom ψ) w) hsq)).trans
    (ConcreteCategory.comp_apply _ _ w)

/-! ## Sheaf-level disjoint vanishing of the partition endomorphism -/

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of the presheaf-level partition endomorphism kills every
stalk element at a point of an `A`-disjoint open.-/
lemma stalkFunctor_map_partitionEndo_apply_eq_zero (X : TopCat.{0}) (A : Set ↑X) (n : ℕ)
    {U : Opens X} (hUA : Disjoint (U : Set ↑X) A) {x : ↑X} (hx : x ∈ U)
    (w : ((singularPresheafComplex X).X n).stalk x) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (partitionEndo X A n) w = 0 := by
  obtain ⟨V₁, hxV₁, tV, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq ((singularPresheafComplex X).X n) w
  have h1 : ((singularPresheafComplex X).X n).germ V₁ x hxV₁ tV
      = ((singularPresheafComplex X).X n).germ (V₁ ⊓ U) x ⟨hxV₁, hx⟩
        (((singularPresheafComplex X).X n).map (homOfLE inf_le_left).op tV) :=
    (TopCat.Presheaf.germ_res_apply ((singularPresheafComplex X).X n)
      (homOfLE (inf_le_left : V₁ ⊓ U ≤ V₁)) x ⟨hxV₁, hx⟩ tV).symm
  rw [h1, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have happ : (partitionEndo X A n).app (op (V₁ ⊓ U)) = 0 := by
    show partApp X A n (V₁ ⊓ U) = 0
    exact partApp_disjoint X A n (V₁ ⊓ U)
      (fun u => Set.disjoint_left.mp hUA u.2.2)
  rw [happ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **Sheaf-level disjoint vanishing**: over any open disjoint from `A`, the
component of the sheafified partition endomorphism is the zero morphism.-/
theorem partitionEndoSheaf_app_disjoint (X : TopCat.{0}) (A : Set ↑X) (n : ℕ)
    {U : Opens X} (hUA : Disjoint (U : Set ↑X) A) :
    (partitionEndoSheaf X A n).hom.app (op U) = 0 := by
  ext s
  show (partitionEndoSheaf X A n).hom.app (op U) s = 0
  refine TopCat.Presheaf.section_ext ((sheafifiedCochainComplex X).X n) U _ _
    (fun x hx => ?_)
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply]
  obtain ⟨w, hw⟩ := exists_stalk_toSheafify_preimage ((singularPresheafComplex X).X n) x
    (((sheafifiedCochainComplex X).X n).presheaf.germ U x hx s)
  rw [← hw]
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (partitionEndo X A n)).hom)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n)) w)
    = ((sheafifiedCochainComplex X).X n).presheaf.germ U x hx 0
  rw [stalk_presheafToSheaf_map_toSheafify,
    stalkFunctor_map_partitionEndo_apply_eq_zero X A n hUA hx w]
  simp only [map_zero]

/-! ## Extension by zero across a two-element cover -/

/-- The two-element cover datum: `true` indexes the first open, `false` the
second.-/
def pairOpens {X : TopCat.{0}} (U O : Opens X) : Bool → Opens X := fun b => cond b U O

/-- The morphisms of a two-element cover into a common ambient open.-/
def pairHoms {X : TopCat.{0}} {U O V : Opens X} (hUV : U ≤ V) (hOV : O ≤ V) :
    ∀ b, pairOpens U O b ⟶ V
  | true => homOfLE hUV
  | false => homOfLE hOV

/-- The sections of a two-element gluing datum: a given section on the first
open, zero on the second.-/
def pairSections {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) {U O : Opens X}
    (s : F.1.obj (op U)) : ∀ b, F.1.obj (op (pairOpens U O b))
  | true => s
  | false => 0

set_option backward.isDefEq.respectTransparency false in
/-- The two-element extension-by-zero datum is compatible when the given
section dies on the overlap with the carving open.-/
lemma pairSections_isCompatible {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U Zc V : Opens X} (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0) :
    TopCat.Presheaf.IsCompatible F.1 (pairOpens U (Zc ⊓ V)) (pairSections F s) := by
  intro b₁ b₂
  cases b₁ <;> cases b₂
  · -- false, false
    show F.1.map (Opens.infLELeft (Zc ⊓ V) (Zc ⊓ V)).op (0 : F.1.obj (op (Zc ⊓ V)))
      = F.1.map (Opens.infLERight (Zc ⊓ V) (Zc ⊓ V)).op (0 : F.1.obj (op (Zc ⊓ V)))
    rw [res_zero', res_zero']
  · -- false, true
    show F.1.map (Opens.infLELeft (Zc ⊓ V) U).op (0 : F.1.obj (op (Zc ⊓ V)))
      = F.1.map (Opens.infLERight (Zc ⊓ V) U).op s
    have hR : F.1.map (Opens.infLERight (Zc ⊓ V) U).op s = 0 := by
      rw [← res_res' F
        (homOfLE (le_inf inf_le_right ((inf_le_left : (Zc ⊓ V) ⊓ U ≤ Zc ⊓ V).trans
          inf_le_left) : (Zc ⊓ V) ⊓ U ≤ U ⊓ Zc))
        (homOfLE (inf_le_left : U ⊓ Zc ≤ U)) (Opens.infLERight (Zc ⊓ V) U) s, hs,
        res_zero']
    rw [res_zero', hR]
  · -- true, false
    show F.1.map (Opens.infLELeft U (Zc ⊓ V)).op s
      = F.1.map (Opens.infLERight U (Zc ⊓ V)).op (0 : F.1.obj (op (Zc ⊓ V)))
    have hL : F.1.map (Opens.infLELeft U (Zc ⊓ V)).op s = 0 := by
      rw [← res_res' F
        (homOfLE (le_inf inf_le_left ((inf_le_right : U ⊓ (Zc ⊓ V) ≤ Zc ⊓ V).trans
          inf_le_left) : U ⊓ (Zc ⊓ V) ≤ U ⊓ Zc))
        (homOfLE (inf_le_left : U ⊓ Zc ≤ U)) (Opens.infLELeft U (Zc ⊓ V)) s, hs,
        res_zero']
    rw [res_zero', hL]
  · -- true, true
    show F.1.map (Opens.infLELeft U U).op s = F.1.map (Opens.infLERight U U).op s
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Extension by zero, existence and uniqueness**: a section on `U` that
dies on `U ⊓ Zc` extends uniquely to any `V ≤ U ⊔ Zc` containing `U`, by a
section that restricts to zero on `Zc ⊓ V`.-/
theorem extendByZero_existsUnique {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V Zc : Opens X} (hUV : U ≤ V) (hcover : V ≤ U ⊔ Zc)
    (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0) :
    ∃! t : F.1.obj (op V),
      F.1.map (homOfLE hUV).op t = s
        ∧ F.1.map (homOfLE (inf_le_right : Zc ⊓ V ≤ V)).op t = 0 := by
  obtain ⟨t, ht, huniq⟩ := F.existsUnique_gluing' (pairOpens U (Zc ⊓ V)) V
    (pairHoms hUV (inf_le_right : Zc ⊓ V ≤ V))
    (fun v hv => by
      rcases Opens.mem_sup.mp (hcover hv) with h | h
      · exact Opens.mem_iSup.mpr ⟨true, h⟩
      · exact Opens.mem_iSup.mpr ⟨false, ⟨h, hv⟩⟩)
    (pairSections F s) (pairSections_isCompatible F s hs)
  refine ⟨t, ⟨ht true, ht false⟩, fun y hy => huniq y ?_⟩
  intro b
  cases b
  · exact hy.2
  · exact hy.1

/-- **Extension by zero** of a section that dies on `U ⊓ Zc`, to an ambient
`V ≤ U ⊔ Zc`.-/
def extendByZero {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V Zc : Opens X} (hUV : U ≤ V) (hcover : V ≤ U ⊔ Zc)
    (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0) :
    F.1.obj (op V) :=
  (extendByZero_existsUnique F hUV hcover s hs).exists.choose

/-- The extension by zero restricts to the given section.-/
lemma extendByZero_res {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V Zc : Opens X} (hUV : U ≤ V) (hcover : V ≤ U ⊔ Zc)
    (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0) :
    F.1.map (homOfLE hUV).op (extendByZero F hUV hcover s hs) = s :=
  (extendByZero_existsUnique F hUV hcover s hs).exists.choose_spec.1

/-- The extension by zero restricts to zero on the carving open.-/
lemma extendByZero_res_compl {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V Zc : Opens X} (hUV : U ≤ V) (hcover : V ≤ U ⊔ Zc)
    (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0) :
    F.1.map (homOfLE (inf_le_right : Zc ⊓ V ≤ V)).op
      (extendByZero F hUV hcover s hs) = 0 :=
  (extendByZero_existsUnique F hUV hcover s hs).exists.choose_spec.2

/-- Uniqueness receipt for the extension by zero.-/
lemma extendByZero_eq {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V Zc : Opens X} (hUV : U ≤ V) (hcover : V ≤ U ⊔ Zc)
    (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0)
    (t : F.1.obj (op V)) (h1 : F.1.map (homOfLE hUV).op t = s)
    (h2 : F.1.map (homOfLE (inf_le_right : Zc ⊓ V ≤ V)).op t = 0) :
    t = extendByZero F hUV hcover s hs :=
  (extendByZero_existsUnique F hUV hcover s hs).unique ⟨h1, h2⟩
    ⟨extendByZero_res F hUV hcover s hs, extendByZero_res_compl F hUV hcover s hs⟩

/-- The extension by zero restricts to zero on any open inside the carving
open.-/
lemma extendByZero_res_of_le {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V Zc : Opens X} (hUV : U ≤ V) (hcover : V ≤ U ⊔ Zc)
    (s : F.1.obj (op U))
    (hs : F.1.map (homOfLE (inf_le_left : U ⊓ Zc ≤ U)).op s = 0)
    {O : Opens X} (hOZ : O ≤ Zc) (hOV : O ≤ V) :
    F.1.map (homOfLE hOV).op (extendByZero F hUV hcover s hs) = 0 := by
  rw [← res_res' F (homOfLE (le_inf hOZ hOV)) (homOfLE (inf_le_right : Zc ⊓ V ≤ V))
      (homOfLE hOV) (extendByZero F hUV hcover s hs),
    extendByZero_res_compl F hUV hcover s hs, res_zero']

/-! ## Locally finite sums of sections by gluing -/

section LocFinSum

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
variable {ι κ : Type*} {W : Opens X}

set_option backward.isDefEq.respectTransparency false in
/-- Sums of restricted sections over two index sets agree whenever the
symmetric difference of the index sets is supported away from the open.-/
lemma sum_res_drop (t : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    {O : Opens X} (hOW : O ≤ W)
    (hsupp : ∀ i, Disjoint (O : Set ↑X) (Z i) → F.1.map (homOfLE hOW).op (t i) = 0)
    (T₁ T₂ : Finset ι)
    (h₁ : ∀ i ∈ T₁, i ∉ T₂ → Disjoint (O : Set ↑X) (Z i))
    (h₂ : ∀ i ∈ T₂, i ∉ T₁ → Disjoint (O : Set ↑X) (Z i)) :
    ∑ i ∈ T₁, F.1.map (homOfLE hOW).op (t i)
      = ∑ i ∈ T₂, F.1.map (homOfLE hOW).op (t i) := by
  rw [← Finset.sum_subset (Finset.inter_subset_left : T₁ ∩ T₂ ⊆ T₁)
      (fun i hi hni => hsupp i (h₁ i hi (fun hT2 => hni (Finset.mem_inter.mpr ⟨hi, hT2⟩)))),
    ← Finset.sum_subset (Finset.inter_subset_right : T₁ ∩ T₂ ⊆ T₂)
      (fun i hi hni => hsupp i (h₂ i hi (fun hT1 => hni (Finset.mem_inter.mpr ⟨hT1, hi⟩))))]

/-- Restricting a finite partial sum further down collapses the two
restriction steps.-/
lemma res_psum (t : ι → F.1.obj (op W)) {O O' : Opens X} (h1 : O' ≤ O) (hOW : O ≤ W)
    (hO'W : O' ≤ W) (T : Finset ι) :
    F.1.map (homOfLE h1).op (∑ i ∈ T, F.1.map (homOfLE hOW).op (t i))
      = ∑ i ∈ T, F.1.map (homOfLE hO'W).op (t i) := by
  rw [res_sum']
  exact Finset.sum_congr rfl (fun i _ => res_res' F _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- **Locally finite summation of sections, existence and uniqueness**: a
family of sections over `W`, each supported in a set `Z i` (in the sense that
it restricts to zero on any open of `W` disjoint from `Z i`), sums by gluing
along any cover of `W` each of whose members meets only the supports indexed
by a prescribed finite set.  The glued section is the unique section
restricting to the finite partial sums.-/
theorem locFinSum_existsUnique (t : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    (hsupp : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i) = 0)
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι) (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (Z i)) :
    ∃! s : F.1.obj (op W), ∀ j, F.1.map (homOfLE (hVW j)).op s
      = ∑ i ∈ S j, F.1.map (homOfLE (hVW j)).op (t i) := by
  refine F.existsUnique_gluing' V W (fun j => homOfLE (hVW j)) hcov
    (fun j => ∑ i ∈ S j, F.1.map (homOfLE (hVW j)).op (t i)) ?_
  intro j k
  have hJK : V j ⊓ V k ≤ W := inf_le_left.trans (hVW j)
  calc F.1.map (Opens.infLELeft (V j) (V k)).op
        (∑ i ∈ S j, F.1.map (homOfLE (hVW j)).op (t i))
      = ∑ i ∈ S j, F.1.map (homOfLE hJK).op (t i) := by
        rw [res_sum']
        exact Finset.sum_congr rfl (fun i _ => res_res' F _ _ _ _)
    _ = ∑ i ∈ S k, F.1.map (homOfLE hJK).op (t i) := by
        refine sum_res_drop F t Z hJK (fun i hd => hsupp i _ hJK hd) (S j) (S k)
          (fun i _ hik => (hS k i hik).mono_left ?_)
          (fun i _ hij => (hS j i hij).mono_left ?_)
        · exact Set.inter_subset_right
        · exact Set.inter_subset_left
    _ = F.1.map (Opens.infLERight (V j) (V k)).op
        (∑ i ∈ S k, F.1.map (homOfLE (hVW k)).op (t i)) := by
        rw [res_sum']
        exact (Finset.sum_congr rfl (fun i _ => res_res' F _ _ _ _)).symm

/-- **The locally finite sum** of a family of sections along a cover pack.-/
def locFinSum (t : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    (hsupp : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i) = 0)
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι) (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (Z i)) :
    F.1.obj (op W) :=
  (locFinSum_existsUnique F t Z hsupp V hVW hcov S hS).exists.choose

/-- The locally finite sum restricts on each cover member to the finite
partial sum.-/
lemma locFinSum_res (t : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    (hsupp : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i) = 0)
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι) (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (Z i))
    (j : κ) :
    F.1.map (homOfLE (hVW j)).op (locFinSum F t Z hsupp V hVW hcov S hS)
      = ∑ i ∈ S j, F.1.map (homOfLE (hVW j)).op (t i) :=
  (locFinSum_existsUnique F t Z hsupp V hVW hcov S hS).exists.choose_spec j

/-- Uniqueness receipt for the locally finite sum.-/
lemma locFinSum_unique (t : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    (hsupp : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i) = 0)
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι) (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (Z i))
    (s : F.1.obj (op W))
    (h : ∀ j, F.1.map (homOfLE (hVW j)).op s
      = ∑ i ∈ S j, F.1.map (homOfLE (hVW j)).op (t i)) :
    s = locFinSum F t Z hsupp V hVW hcov S hS :=
  (locFinSum_existsUnique F t Z hsupp V hVW hcov S hS).unique h
    (fun j => locFinSum_res F t Z hsupp V hVW hcov S hS j)

set_option backward.isDefEq.respectTransparency false in
/-- **Adequate-restriction receipt**: on any open of `W` that meets only the
supports indexed by a finite set `T`, the locally finite sum restricts to the
`T`-partial sum (not only on the members of the defining cover pack).-/
lemma locFinSum_res_adequate (t : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    (hsupp : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i) = 0)
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι) (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (Z i))
    {O : Opens X} (hOW : O ≤ W) (T : Finset ι)
    (hT : ∀ i, i ∉ T → Disjoint ((O : Opens X) : Set ↑X) (Z i)) :
    F.1.map (homOfLE hOW).op (locFinSum F t Z hsupp V hVW hcov S hS)
      = ∑ i ∈ T, F.1.map (homOfLE hOW).op (t i) := by
  refine F.eq_of_locally_eq' (fun j => O ⊓ V j) O (fun j => homOfLE inf_le_left)
    (fun x hxO => Opens.mem_iSup.mpr ?_) _ _ (fun j => ?_)
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcov (hOW hxO))
    exact ⟨j, ⟨hxO, hj⟩⟩
  · have hOVjW : O ⊓ V j ≤ W := inf_le_left.trans hOW
    calc F.1.map (homOfLE (inf_le_left : O ⊓ V j ≤ O)).op
          (F.1.map (homOfLE hOW).op (locFinSum F t Z hsupp V hVW hcov S hS))
        = F.1.map (homOfLE (inf_le_right : O ⊓ V j ≤ V j)).op
          (F.1.map (homOfLE (hVW j)).op (locFinSum F t Z hsupp V hVW hcov S hS)) := by
          rw [res_res' F (homOfLE inf_le_left) (homOfLE hOW) (homOfLE hOVjW) _,
            res_res' F (homOfLE inf_le_right) (homOfLE (hVW j)) (homOfLE hOVjW) _]
      _ = F.1.map (homOfLE (inf_le_right : O ⊓ V j ≤ V j)).op
          (∑ i ∈ S j, F.1.map (homOfLE (hVW j)).op (t i)) := by
          rw [locFinSum_res F t Z hsupp V hVW hcov S hS j]
      _ = ∑ i ∈ S j, F.1.map (homOfLE hOVjW).op (t i) :=
          res_psum F t inf_le_right (hVW j) hOVjW (S j)
      _ = ∑ i ∈ T, F.1.map (homOfLE hOVjW).op (t i) := by
          refine sum_res_drop F t Z hOVjW (fun i hd => hsupp i _ hOVjW hd) (S j) T
            (fun i _ hiT => (hT i hiT).mono_left ?_)
            (fun i _ hiS => (hS j i hiS).mono_left ?_)
          · exact Set.inter_subset_left
          · exact Set.inter_subset_right
      _ = F.1.map (homOfLE (inf_le_left : O ⊓ V j ≤ O)).op
          (∑ i ∈ T, F.1.map (homOfLE hOW).op (t i)) :=
          (res_psum F t inf_le_left hOW hOVjW T).symm

/-- Additivity receipt: the locally finite sum of a pointwise sum of two
families (with a common support datum) is the sum of the locally finite
sums.-/
lemma locFinSum_add (t t' : ι → F.1.obj (op W)) (Z : ι → Set ↑X)
    (hsupp : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i) = 0)
    (hsupp' : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t' i) = 0)
    (hsupp'' : ∀ i (O : Opens X) (hOW : O ≤ W), Disjoint (O : Set ↑X) (Z i) →
      F.1.map (homOfLE hOW).op (t i + t' i) = 0)
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι) (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (Z i)) :
    locFinSum F (fun i => t i + t' i) Z hsupp'' V hVW hcov S hS
      = locFinSum F t Z hsupp V hVW hcov S hS
        + locFinSum F t' Z hsupp' V hVW hcov S hS := by
  refine ((locFinSum_unique F (fun i => t i + t' i) Z hsupp'' V hVW hcov S hS _
    (fun j => ?_)).symm)
  rw [res_add', locFinSum_res F t Z hsupp V hVW hcov S hS j,
    locFinSum_res F t' Z hsupp' V hVW hcov S hS j, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (res_add' F _ _ _).symm)

end LocFinSum

/-! ## The partition-sum identity -/

section PartitionSum

variable {ι : Type} {κ : Type*}

set_option backward.isDefEq.respectTransparency false in
/-- Elementwise finite partition identity at the presheaf level: over an open
each of whose points lies in exactly one member (indexed by `S`) of a family
of subsets, the partition endomorphisms indexed by `S` sum to the identity on
sections.-/
lemma sum_partitionEndo_app_apply (X : TopCat.{0}) (A : ι → Set ↑X) (S : Finset ι) (n : ℕ)
    (V : Opens X) (hone : ∀ y ∈ (V : Set ↑X), ∃! i, i ∈ S ∧ y ∈ A i)
    (u : ((singularPresheafComplex X).X n).obj (op V)) :
    ∑ i ∈ S, (partitionEndo X (A i) n).app (op V) u = u := by
  have hkeep : ∑ i ∈ S, keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj V)) n
        (vertexPred X (A i) V n)
      = 𝟙 (((TopCat.toSSet.obj ((Opens.toTopCat X).obj V)).chainComplex Qcoef).X n) :=
    keep_finpartition _ n S (fun i => vertexPred X (A i) V n)
      (fun σ => hone (ambient (firstVertex σ)) (firstVertex σ).2)
  exact (Preadditive.sum_comp S
      (fun i => keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj V)) n
        (vertexPred X (A i) V n))
      (u : ((TopCat.toSSet.obj ((Opens.toTopCat X).obj V)).chainComplex Qcoef).X n
        ⟶ Qcoef)).symm.trans
    ((congrArg (fun m => m
      ≫ (u : ((TopCat.toSSet.obj ((Opens.toTopCat X).obj V)).chainComplex Qcoef).X n
        ⟶ Qcoef)) hkeep).trans
      (Category.id_comp _))

set_option backward.isDefEq.respectTransparency false in
/-- Finite partition identity on stalks: at a point of `V`, the stalk maps of
the partition endomorphisms indexed by `S` sum to the identity.-/
lemma sum_stalkFunctor_map_partitionEndo_apply (X : TopCat.{0}) (A : ι → Set ↑X)
    (S : Finset ι) (n : ℕ) {V : Opens X}
    (hone : ∀ y ∈ (V : Set ↑X), ∃! i, i ∈ S ∧ y ∈ A i)
    {x : ↑X} (hx : x ∈ V) (w : ((singularPresheafComplex X).X n).stalk x) :
    ∑ i ∈ S, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      (partitionEndo X (A i) n) w = w := by
  obtain ⟨V₁, hxV₁, tV, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq ((singularPresheafComplex X).X n) w
  have h1 : ((singularPresheafComplex X).X n).germ V₁ x hxV₁ tV
      = ((singularPresheafComplex X).X n).germ (V₁ ⊓ V) x ⟨hxV₁, hx⟩
        (((singularPresheafComplex X).X n).map (homOfLE inf_le_left).op tV) :=
    (TopCat.Presheaf.germ_res_apply ((singularPresheafComplex X).X n)
      (homOfLE (inf_le_left : V₁ ⊓ V ≤ V₁)) x ⟨hxV₁, hx⟩ tV).symm
  rw [h1,
    Finset.sum_congr rfl (fun i _ => TopCat.Presheaf.stalkFunctor_map_germ_apply
      (V₁ ⊓ V) x ⟨hxV₁, hx⟩ (partitionEndo X (A i) n) _)]
  have hms : ((singularPresheafComplex X).X n).germ (V₁ ⊓ V) x ⟨hxV₁, hx⟩
        (∑ i ∈ S, (partitionEndo X (A i) n).app (op (V₁ ⊓ V))
          (((singularPresheafComplex X).X n).map (homOfLE inf_le_left).op tV))
      = ∑ i ∈ S, ((singularPresheafComplex X).X n).germ (V₁ ⊓ V) x ⟨hxV₁, hx⟩
        ((partitionEndo X (A i) n).app (op (V₁ ⊓ V))
          (((singularPresheafComplex X).X n).map (homOfLE inf_le_left).op tV)) :=
    map_sum _ _ _
  rw [← hms,
    sum_partitionEndo_app_apply X A S n (V₁ ⊓ V) (fun y hy => hone y hy.2)]

set_option backward.isDefEq.respectTransparency false in
/-- **Sectionwise finite partition identity for the sheafified endomorphisms**:
over an open each of whose points lies in exactly one member (indexed by `S`)
of a family of subsets, the sheafified partition endomorphisms indexed by `S`
sum to the identity on sections of the sheafified cochain sheaf.-/
theorem sum_partitionEndoSheaf_app_apply (X : TopCat.{0}) (A : ι → Set ↑X)
    (S : Finset ι) (n : ℕ) {V : Opens X}
    (hone : ∀ y ∈ (V : Set ↑X), ∃! i, i ∈ S ∧ y ∈ A i)
    (s : ((sheafifiedCochainComplex X).X n).presheaf.obj (op V)) :
    ∑ i ∈ S, (partitionEndoSheaf X (A i) n).hom.app (op V) s = s := by
  refine TopCat.Presheaf.section_ext ((sheafifiedCochainComplex X).X n) V _ _
    (fun x hx => ?_)
  rw [map_sum]
  obtain ⟨w, hw⟩ := exists_stalk_toSheafify_preimage ((singularPresheafComplex X).X n) x
    (((sheafifiedCochainComplex X).X n).presheaf.germ V x hx s)
  have hterm : ∀ i, ((sheafifiedCochainComplex X).X n).presheaf.germ V x hx
        ((partitionEndoSheaf X (A i) n).hom.app (op V) s)
      = (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n))
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
            (partitionEndo X (A i) n) w) := by
    intro i
    rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, ← hw]
    exact stalk_presheafToSheaf_map_toSheafify (partitionEndo X (A i) n) x w
  have hms : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n))
        (∑ i ∈ S, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          (partitionEndo X (A i) n) w)
      = ∑ i ∈ S, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        (toSheafify (Opens.grothendieckTopology X) ((singularPresheafComplex X).X n))
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
          (partitionEndo X (A i) n) w) :=
    map_sum _ _ _
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← hms,
    sum_stalkFunctor_map_partitionEndo_apply X A S n hone hx w, hw]

set_option backward.isDefEq.respectTransparency false in
/-- The image of a section under the sheafified partition endomorphism is
supported in the closure of the partition set: it restricts to zero on any
open disjoint from that closure.-/
lemma partitionEndoSheaf_app_supp (X : TopCat.{0}) (A : Set ↑X) (n : ℕ)
    {W : Opens X} (s : ((sheafifiedCochainComplex X).X n).presheaf.obj (op W))
    (O : Opens X) (hOW : O ≤ W) (hd : Disjoint (O : Set ↑X) (closure A)) :
    ((sheafifiedCochainComplex X).X n).1.map (homOfLE hOW).op
      ((partitionEndoSheaf X A n).hom.app (op W) s) = 0 := by
  rw [← app_res (partitionEndoSheaf X A n) (homOfLE hOW) s,
    partitionEndoSheaf_app_disjoint X A n (hd.mono_right subset_closure)]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **The partition-sum identity**: for a partition of the ambient space into
subsets whose closures form the support datum of a cover pack over `W`, the
locally finite sum of the partition-endomorphism images of a section `s` of
the sheafified cochain sheaf over `W` recovers `s`.-/
theorem partitionSum_eq_id (X : TopCat.{0}) (A : ι → Set ↑X) (n : ℕ)
    (hA : ∀ y : ↑X, ∃! i, y ∈ A i)
    {W : Opens X} (s : ((sheafifiedCochainComplex X).X n).presheaf.obj (op W))
    (V : κ → Opens X) (hVW : ∀ j, V j ≤ W) (hcov : W ≤ ⨆ j, V j)
    (S : κ → Finset ι)
    (hS : ∀ j i, i ∉ S j → Disjoint ((V j : Opens X) : Set ↑X) (closure (A i))) :
    locFinSum ((sheafifiedCochainComplex X).X n)
      (fun i => (partitionEndoSheaf X (A i) n).hom.app (op W) s)
      (fun i => closure (A i))
      (fun i O hOW hd => partitionEndoSheaf_app_supp X (A i) n s O hOW hd)
      V hVW hcov S hS = s := by
  refine (locFinSum_unique ((sheafifiedCochainComplex X).X n)
    (fun i => (partitionEndoSheaf X (A i) n).hom.app (op W) s)
    (fun i => closure (A i))
    (fun i O hOW hd => partitionEndoSheaf_app_supp X (A i) n s O hOW hd)
    V hVW hcov S hS s (fun j => ?_)).symm
  have hone : ∀ y ∈ ((V j : Opens X) : Set ↑X), ∃! i, i ∈ S j ∧ y ∈ A i := by
    intro y hy
    obtain ⟨i₀, hi₀, huniq⟩ := hA y
    have hiS : i₀ ∈ S j := by
      by_contra hns
      exact Set.disjoint_left.mp (hS j i₀ hns) hy (subset_closure hi₀)
    exact ⟨i₀, ⟨hiS, hi₀⟩, fun k hk => huniq k hk.2⟩
  rw [Finset.sum_congr rfl (fun i _ =>
    (app_res (partitionEndoSheaf X (A i) n) (homOfLE (hVW j)) s).symm)]
  exact (sum_partitionEndoSheaf_app_apply X A (S j) n hone _).symm

/-- A cover pack over `W` extracted from a locally finite family of supports:
each point of `W` gets an open neighbourhood inside `W` meeting only a finite,
recorded set of the supports.-/
lemma exists_pack {X : TopCat.{0}} (Z : ι → Set ↑X) (hlf : LocallyFinite Z)
    (W : Opens X) :
    ∃ (V : ↥W → Opens X) (S : ↥W → Finset ι),
      (∀ y : ↥W, V y ≤ W) ∧ (W ≤ ⨆ y, V y) ∧
        ∀ y i, i ∉ S y → Disjoint ((V y : Opens X) : Set ↑X) (Z i) := by
  choose N hN hfin using fun y : ↥W => hlf (y : ↑X)
  refine ⟨fun y => ⟨interior (N y), isOpen_interior⟩ ⊓ W,
    fun y => (hfin y).toFinset, fun y => inf_le_right,
    fun x hx => Opens.mem_iSup.mpr
      ⟨⟨x, hx⟩, ⟨mem_interior_iff_mem_nhds.mpr (hN ⟨x, hx⟩), hx⟩⟩, ?_⟩
  intro y i hi
  rw [Set.Finite.mem_toFinset] at hi
  refine Set.disjoint_left.mpr (fun a ha hZa => hi ⟨a, hZa, ?_⟩)
  exact interior_subset ha.1

end PartitionSum

/-! ## Toolkit for the Γ-surjectivity lemma -/

section GammaTools

set_option backward.isDefEq.respectTransparency false in
/-- A composite of sheaf morphisms with vanishing composite kills every
section elementwise.-/
lemma comp_app_apply_eq_zero {X : TopCat.{0}} {F G H : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0) (U : Opens X) (s : F.1.obj (op U)) :
    g.hom.app (op U) (f.hom.app (op U) s) = 0 := by
  calc g.hom.app (op U) (f.hom.app (op U) s)
      = (f ≫ g).hom.app (op U) s :=
        (ConcreteCategory.comp_apply (f.hom.app (op U)) (g.hom.app (op U)) s).symm
    _ = (0 : F ⟶ H).hom.app (op U) s := by rw [hfg]
    _ = 0 := by simp

set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism of abelian sheaves is injective on sections over every
open.-/
lemma app_injective_of_mono {X : TopCat.{0}} {K B : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : K ⟶ B) [Mono f] (U : Opens X) :
    Function.Injective (f.hom.app (op U)) :=
  TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective f.hom U
    (fun x _ => by
      haveI : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map f.hom) :=
        TopCat.Presheaf.stalk_mono_of_mono f x
      exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp inferInstance)

set_option backward.isDefEq.respectTransparency false in
/-- An epimorphism of abelian sheaves admits local lifts of any global
section.-/
lemma exists_local_lift {X : TopCat.{0}} {B R : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : B ⟶ R) [Epi g] (r : R.1.obj (op ⊤)) (x : ↑X) :
    ∃ (V : Opens X) (_ : x ∈ V) (b : B.1.obj (op V)),
      g.hom.app (op V) b = R.1.map (homOfLE le_top).op r := by
  have hls : TopCat.Presheaf.IsLocallySurjective g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance
  obtain ⟨V, hVU, ⟨b, hb⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff g.hom).mp hls ⊤ r x trivial
  exact ⟨V, hxV, b, hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Sectionwise kernel extraction**: for a short exact sequence of abelian
sheaves and a section of the middle sheaf killed by the quotient map, there is
a unique section of the kernel sheaf mapping to it (the sections functor is
left exact; done here by germ-local preimages and gluing).-/
lemma existsUnique_section_preimage {X : TopCat.{0}}
    {K B R : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : K ⟶ B) (g : B ⟶ R) (hfg : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hfg).ShortExact)
    (U : Opens X) (t : B.1.obj (op U)) (ht : g.hom.app (op U) t = 0) :
    ∃! δ : K.1.obj (op U), f.hom.app (op U) δ = t := by
  haveI hmono : Mono f := hexact.mono_f
  have hinj : ∀ x, Function.Injective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map f.hom) := fun x => by
    haveI : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map f.hom) :=
      TopCat.Presheaf.stalk_mono_of_mono f x
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp inferInstance
  -- local preimages from stalkwise exactness
  have hloc : ∀ y : ↥U, ∃ (V : Opens X) (_ : (y : ↑X) ∈ V) (iVU : V ⟶ U)
      (s : K.1.obj (op V)), f.hom.app (op V) s = B.1.map iVU.op t := by
    intro y
    have hstalk := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (ShortComplex.mk f g hfg)).mp hexact.exact (y : ↑X)
    rw [ShortComplex.ab_exact_iff] at hstalk
    have hz : ((ShortComplex.mk f g hfg).map (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (y : ↑X))).g
        (B.presheaf.germ U y y.2 t) = 0 := by
      show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (y : ↑X)).map g.hom
        (B.presheaf.germ U y y.2 t) = 0
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht, map_zero]
    obtain ⟨z, hz'⟩ := hstalk _ hz
    have hz'' : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} (y : ↑X)).map f.hom z
        = B.presheaf.germ U y y.2 t := hz'
    obtain ⟨V₁, hyV₁, k₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq K.presheaf z
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hz''
    obtain ⟨W, hyW, iWV₁, iWU, heq⟩ :=
      TopCat.Presheaf.germ_eq B.presheaf (y : ↑X) hyV₁ y.2 _ _ hz''
    refine ⟨W, hyW, iWU, K.1.map iWV₁.op k₁, ?_⟩
    rw [app_res f iWV₁ k₁, heq]
  choose V mV iVU sf heq using hloc
  have V_cover : U ≤ iSup V := fun x hx =>
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, mV ⟨x, hx⟩⟩
  have compat : TopCat.Presheaf.IsCompatible K.1 V sf := by
    intro a b
    have hab : V a ⊓ V b ≤ U := le_trans inf_le_left (leOfHom (iVU a))
    have ha : f.hom.app (op (V a ⊓ V b))
        (K.1.map (Opens.infLELeft (V a) (V b)).op (sf a))
        = B.1.map (homOfLE hab).op t := by
      rw [app_res f (Opens.infLELeft (V a) (V b)) (sf a), heq a]
      exact res_res' B _ _ _ t
    have hb : f.hom.app (op (V a ⊓ V b))
        (K.1.map (Opens.infLERight (V a) (V b)).op (sf b))
        = B.1.map (homOfLE hab).op t := by
      rw [app_res f (Opens.infLERight (V a) (V b)) (sf b), heq b]
      exact res_res' B _ _ _ t
    exact app_injective_of_mono f (V a ⊓ V b) (ha.trans hb.symm)
  obtain ⟨δ, hδ, huniq⟩ := K.existsUnique_gluing' V U iVU V_cover sf compat
  have hfδ : f.hom.app (op U) δ = t := by
    refine B.eq_of_locally_eq' V U iVU V_cover _ _ (fun a => ?_)
    rw [← app_res f (iVU a) δ, hδ a, heq a]
  exact ⟨δ, hfδ, fun y hy =>
    app_injective_of_mono f U (hy.trans hfδ.symm)⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Subordinate partition of the space**: on a paracompact Hausdorff space,
any open cover admits a partition of the space into (arbitrary) subsets, one
per cover member, with each closure contained in the corresponding cover
member and the closures locally finite (precise refinement, shrinking lemma,
and disjointification along a well-order).-/
lemma exists_subordinate_partition {X : TopCat.{0}} [ParacompactSpace ↑X] [T2Space ↑X]
    {ι : Type} (u : ι → Opens X) (hu : (⊤ : Opens X) ≤ ⨆ i, u i) :
    ∃ A : ι → Set ↑X, (∀ y : ↑X, ∃! i, y ∈ A i) ∧
      (∀ i, closure (A i) ⊆ ((u i : Opens X) : Set ↑X)) ∧
      LocallyFinite (fun i => closure (A i)) := by
  have huniv : ⋃ i, ((u i : Opens X) : Set ↑X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hu (show y ∈ (⊤ : Opens X) from trivial))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨v, hvo, hvU, hvlf, hvu⟩ := precise_refinement
    (fun i => ((u i : Opens X) : Set ↑X)) (fun i => (u i).isOpen) huniv
  obtain ⟨w, hwU, hwo, hwc⟩ := exists_iUnion_eq_closure_subset hvo
    (fun x => hvlf.point_finite x) hvU
  refine ⟨fun i => w i \ ⋃ (j : ι) (_ : WellOrderingRel j i), w j, ?_, ?_, ?_⟩
  · intro y
    have hy : ∃ i, y ∈ w i := Set.iUnion_eq_univ_iff.mp hwU y
    obtain ⟨i₀, hi₀, hmin⟩ := (IsWellFounded.wf
      (r := (WellOrderingRel : ι → ι → Prop))).has_min {i | y ∈ w i} hy
    refine ⟨i₀, ⟨hi₀, fun hmem => ?_⟩, fun k hk => ?_⟩
    · obtain ⟨j, hji, hyj⟩ := Set.mem_iUnion₂.mp hmem
      exact hmin j hyj hji
    · rcases (@trichotomous ι WellOrderingRel _ k i₀) with h | h | h
      · exact absurd h (hmin k hk.1)
      · exact h
      · exact absurd (Set.mem_iUnion₂.mpr ⟨i₀, h, hi₀⟩) hk.2
  · intro i
    exact (closure_mono Set.sdiff_subset).trans ((hwc i).trans (hvu i))
  · exact hvlf.subset (fun i => (closure_mono Set.sdiff_subset).trans (hwc i))

set_option backward.isDefEq.respectTransparency false in
/-- **The classical correction family**: given a partition subordinate (in the
closure sense) to a family of opens, and a family `δ` of sections of the
sheafified cochain sheaf over the pairwise intersections satisfying the
restricted cocycle identity, there is a family `c i` of sections over the `V i`
whose overlap differences recover `δ` — each `c i` is the locally finite sum
over `j` of the extension by zero of the `A j`-partition image of `δ i j`.-/
lemma exists_correction (X : TopCat.{0}) (n : ℕ)
    (A : ↑X → Set ↑X) (V : ↑X → Opens X)
    (hA : ∀ y : ↑X, ∃! i, y ∈ A i)
    (hclA : ∀ j, closure (A j) ⊆ ((V j : Opens X) : Set ↑X))
    (hlf : LocallyFinite fun j => closure (A j))
    (δ : ∀ i j : ↑X, ((sheafifiedCochainComplex X).X n).1.obj (op (V i ⊓ V j)))
    (hcoc : ∀ (i j k : ↑X) (O : Opens X) (h1 : O ≤ V i ⊓ V k) (h2 : O ≤ V j ⊓ V k)
      (h3 : O ≤ V i ⊓ V j),
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE h1).op (δ i k)
        - ((sheafifiedCochainComplex X).X n).1.map (homOfLE h2).op (δ j k)
        = ((sheafifiedCochainComplex X).X n).1.map (homOfLE h3).op (δ i j)) :
    ∃ c : ∀ i : ↑X, ((sheafifiedCochainComplex X).X n).1.obj (op (V i)),
      ∀ i j : ↑X,
        ((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i)
          - ((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j)
          = δ i j := by
  classical
  have hZo : ∀ k : ↑X, IsOpen (closure (A k))ᶜ := fun k => isClosed_closure.isOpen_compl
  have hcov_ext : ∀ i j : ↑X,
      V i ≤ (V i ⊓ V j) ⊔ (⟨(closure (A j))ᶜ, hZo j⟩ : Opens X) := by
    intro i j y hy
    by_cases hyA : y ∈ closure (A j)
    · exact Opens.mem_sup.mpr (Or.inl ⟨hy, hclA j hyA⟩)
    · exact Opens.mem_sup.mpr (Or.inr hyA)
  have hs_ext : ∀ i j : ↑X, ((sheafifiedCochainComplex X).X n).1.map
      (homOfLE (inf_le_left :
        (V i ⊓ V j) ⊓ (⟨(closure (A j))ᶜ, hZo j⟩ : Opens X) ≤ V i ⊓ V j)).op
      ((partitionEndoSheaf X (A j) n).hom.app (op (V i ⊓ V j)) (δ i j)) = 0 := by
    intro i j
    exact partitionEndoSheaf_app_supp X (A j) n (δ i j) _ inf_le_left
      (Set.disjoint_left.mpr (fun a ha => ha.2))
  have hsupp : ∀ (i j : ↑X) (O : Opens X) (hOW : O ≤ V i),
      Disjoint (O : Set ↑X) (closure (A j)) →
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE hOW).op
        (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i j)
          ((partitionEndoSheaf X (A j) n).hom.app (op (V i ⊓ V j)) (δ i j))
          (hs_ext i j)) = 0 := by
    intro i j O hOW hd
    exact extendByZero_res_of_le _ _ _ _ _
      (fun a ha => Set.disjoint_left.mp hd ha) hOW
  choose P T hPle hPcov hPT using
    fun i : ↑X => exists_pack (fun k => closure (A k)) hlf (V i)
  refine ⟨fun i => locFinSum ((sheafifiedCochainComplex X).X n)
    (fun j => extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i j)
      ((partitionEndoSheaf X (A j) n).hom.app (op (V i ⊓ V j)) (δ i j)) (hs_ext i j))
    (fun j => closure (A j)) (hsupp i) (P i) (hPle i) (hPcov i) (T i) (hPT i),
    fun i j => ?_⟩
  obtain ⟨Q, TQ, hQle, hQcov, hQT⟩ := exists_pack (fun k => closure (A k)) hlf (V i ⊓ V j)
  refine ((sheafifiedCochainComplex X).X n).eq_of_locally_eq' Q (V i ⊓ V j)
    (fun y => homOfLE (hQle y)) hQcov _ _ (fun y => ?_)
  have hQVi : Q y ≤ V i := (hQle y).trans inf_le_left
  have hQVj : Q y ≤ V j := (hQle y).trans inf_le_right
  rw [map_sub,
    res_res' ((sheafifiedCochainComplex X).X n) (homOfLE (hQle y))
      (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) (homOfLE hQVi) _,
    res_res' ((sheafifiedCochainComplex X).X n) (homOfLE (hQle y))
      (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) (homOfLE hQVj) _,
    locFinSum_res_adequate ((sheafifiedCochainComplex X).X n) _ _ (hsupp i)
      (P i) (hPle i) (hPcov i) (T i) (hPT i) hQVi (TQ y) (fun k hk => hQT y k hk),
    locFinSum_res_adequate ((sheafifiedCochainComplex X).X n) _ _ (hsupp j)
      (P j) (hPle j) (hPcov j) (T j) (hPT j) hQVj (TQ y) (fun k hk => hQT y k hk),
    ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ TQ y,
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE hQVi).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V i ⊓ V k)) (δ i k))
            (hs_ext i k))
        - ((sheafifiedCochainComplex X).X n).1.map (homOfLE hQVj).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext j k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V j ⊓ V k)) (δ j k))
            (hs_ext j k))
      = (partitionEndoSheaf X (A k) n).hom.app (op (Q y))
        (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j)) := by
    intro k _
    have hU₁Vik : Q y ⊓ V k ≤ V i ⊓ V k := le_inf (inf_le_left.trans hQVi) inf_le_right
    have hU₁Vjk : Q y ⊓ V k ≤ V j ⊓ V k := le_inf (inf_le_left.trans hQVj) inf_le_right
    have hU₁Vij : Q y ⊓ V k ≤ V i ⊓ V j := inf_le_left.trans (hQle y)
    refine ((sheafifiedCochainComplex X).X n).eq_of_locally_eq₂
      (homOfLE (inf_le_left : Q y ⊓ V k ≤ Q y))
      (homOfLE (inf_le_left : Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y))
      (fun z hz => ?_) _ _ ?_ ?_
    · by_cases hzA : z ∈ closure (A k)
      · exact Opens.mem_sup.mpr (Or.inl ⟨hz, hclA k hzA⟩)
      · exact Opens.mem_sup.mpr (Or.inr ⟨hz, hzA⟩)
    · -- restriction to Q y ⊓ V k
      rw [map_sub,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVi) (homOfLE (inf_le_left.trans hQVi)) _,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVj) (homOfLE (inf_le_left.trans hQVj)) _,
        ← res_res' ((sheafifiedCochainComplex X).X n) (homOfLE hU₁Vik)
          (homOfLE (inf_le_left : V i ⊓ V k ≤ V i))
          (homOfLE (inf_le_left.trans hQVi)) _,
        ← res_res' ((sheafifiedCochainComplex X).X n) (homOfLE hU₁Vjk)
          (homOfLE (inf_le_left : V j ⊓ V k ≤ V j))
          (homOfLE (inf_le_left.trans hQVj)) _,
        extendByZero_res ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i k)
          ((partitionEndoSheaf X (A k) n).hom.app (op (V i ⊓ V k)) (δ i k))
          (hs_ext i k),
        extendByZero_res ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext j k)
          ((partitionEndoSheaf X (A k) n).hom.app (op (V j ⊓ V k)) (δ j k))
          (hs_ext j k),
        ← app_res (partitionEndoSheaf X (A k) n) (homOfLE hU₁Vik) (δ i k),
        ← app_res (partitionEndoSheaf X (A k) n) (homOfLE hU₁Vjk) (δ j k),
        ← map_sub, hcoc i j k (Q y ⊓ V k) hU₁Vik hU₁Vjk hU₁Vij,
        ← app_res (partitionEndoSheaf X (A k) n) (homOfLE (inf_le_left : Q y ⊓ V k ≤ Q y))
          (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j)),
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE (hQle y)) (homOfLE hU₁Vij) _]
    · -- restriction to Q y ⊓ (closure (A k))ᶜ
      have h0i : ((sheafifiedCochainComplex X).X n).1.map
          (homOfLE ((inf_le_left :
            Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y).trans hQVi)).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V i ⊓ V k)) (δ i k))
            (hs_ext i k)) = 0 :=
        extendByZero_res_of_le _ _ _ _ _ inf_le_right _
      have h0j : ((sheafifiedCochainComplex X).X n).1.map
          (homOfLE ((inf_le_left :
            Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y).trans hQVj)).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext j k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V j ⊓ V k)) (δ j k))
            (hs_ext j k)) = 0 :=
        extendByZero_res_of_le _ _ _ _ _ inf_le_right _
      have happ0 : ((sheafifiedCochainComplex X).X n).1.map
          (homOfLE (inf_le_left :
            Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y)).op
          ((partitionEndoSheaf X (A k) n).hom.app (op (Q y))
            (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j)))
          = 0 :=
        partitionEndoSheaf_app_supp X (A k) n _ _ inf_le_left
          (disjoint_compl_left.mono_left Set.inter_subset_right)
      rw [map_sub,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVi) (homOfLE (inf_le_left.trans hQVi)) _,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVj) (homOfLE (inf_le_left.trans hQVj)) _,
        h0i, h0j, happ0, sub_zero]
  rw [Finset.sum_congr rfl hterm]
  exact sum_partitionEndoSheaf_app_apply X A (TQ y) n
    (fun z hz => by
      obtain ⟨k₀, hk₀, huniq⟩ := hA z
      have hkT : k₀ ∈ TQ y := by
        by_contra hns
        exact Set.disjoint_left.mp (hQT y k₀ hns) hz (subset_closure hk₀)
      exact ⟨k₀, ⟨hkT, hk₀⟩, fun m hm => huniq m hm.2⟩)
    (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j))

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma W: `Γ`-surjectivity for short exact sequences of abelian sheaves
with sheafified-cochain kernel**, on a paracompact Hausdorff space.-/
theorem gammaSurjective_of_shortExact_sheafifiedCochain (X : TopCat.{0})
    [ParacompactSpace ↑X] [T2Space ↑X] (n : ℕ)
    {B R : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : (sheafifiedCochainComplex X).X n ⟶ B) (g : B ⟶ R) (hfg : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hfg).ShortExact) :
    Function.Surjective (g.hom.app (op (⊤ : Opens X))) := by
  intro r
  haveI hEpi : Epi g := hexact.epi_g
  haveI hMono : Mono f := hexact.mono_f
  -- Step A: local lifts of `r` and a subordinate partition
  choose V hxV b₀ hb₀ using fun x : ↑X => exists_local_lift g r x
  obtain ⟨A, hA, hclA, hlf⟩ := exists_subordinate_partition V
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩)
  -- Step B: the overlap differences of the lifts come from the kernel sheaf
  have hdiffzero : ∀ i j : ↑X, g.hom.app (op (V i ⊓ V j))
      (B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
        - B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j)) = 0 := by
    intro i j
    rw [map_sub, app_res g (homOfLE inf_le_left) (b₀ i),
      app_res g (homOfLE inf_le_right) (b₀ j), hb₀ i, hb₀ j,
      res_res' R (homOfLE inf_le_left) (homOfLE le_top) (homOfLE le_top) r,
      res_res' R (homOfLE inf_le_right) (homOfLE le_top) (homOfLE le_top) r,
      sub_self]
  choose δ hδ using fun i j : ↑X => (existsUnique_section_preimage f g hfg hexact
    (V i ⊓ V j) _ (hdiffzero i j)).exists
  -- Step B': the restricted cocycle identity, by injectivity of `f`
  have hcoc : ∀ (i j k : ↑X) (O : Opens X) (h1 : O ≤ V i ⊓ V k) (h2 : O ≤ V j ⊓ V k)
      (h3 : O ≤ V i ⊓ V j),
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE h1).op (δ i k)
        - ((sheafifiedCochainComplex X).X n).1.map (homOfLE h2).op (δ j k)
        = ((sheafifiedCochainComplex X).X n).1.map (homOfLE h3).op (δ i j) := by
    intro i j k O h1 h2 h3
    apply app_injective_of_mono f O
    have hOVi : O ≤ V i := h1.trans inf_le_left
    have hOVj : O ≤ V j := h2.trans inf_le_left
    have hOVk : O ≤ V k := h1.trans inf_le_right
    rw [map_sub, app_res f (homOfLE h1) (δ i k), app_res f (homOfLE h2) (δ j k),
      app_res f (homOfLE h3) (δ i j), hδ i k, hδ j k, hδ i j,
      map_sub, map_sub, map_sub,
      res_res' B (homOfLE h1) (homOfLE (inf_le_left : V i ⊓ V k ≤ V i))
        (homOfLE hOVi) (b₀ i),
      res_res' B (homOfLE h1) (homOfLE (inf_le_right : V i ⊓ V k ≤ V k))
        (homOfLE hOVk) (b₀ k),
      res_res' B (homOfLE h2) (homOfLE (inf_le_left : V j ⊓ V k ≤ V j))
        (homOfLE hOVj) (b₀ j),
      res_res' B (homOfLE h2) (homOfLE (inf_le_right : V j ⊓ V k ≤ V k))
        (homOfLE hOVk) (b₀ k),
      res_res' B (homOfLE h3) (homOfLE (inf_le_left : V i ⊓ V j ≤ V i))
        (homOfLE hOVi) (b₀ i),
      res_res' B (homOfLE h3) (homOfLE (inf_le_right : V i ⊓ V j ≤ V j))
        (homOfLE hOVj) (b₀ j)]
    abel
  -- Step C: the correction family
  obtain ⟨c, hc⟩ := exists_correction X n A V hA hclA hlf δ hcoc
  -- Step D: the corrected lifts agree on overlaps
  have hcompat : ∀ i j : ↑X,
      B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          (b₀ i - f.hom.app (op (V i)) (c i))
        = B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          (b₀ j - f.hom.app (op (V j)) (c j)) := by
    intro i j
    rw [map_sub, map_sub,
      ← app_res f (homOfLE inf_le_left) (c i),
      ← app_res f (homOfLE inf_le_right) (c j)]
    have hfc : f.hom.app (op (V i ⊓ V j))
          (((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i))
        - f.hom.app (op (V i ⊓ V j))
          (((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j))
        = B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
          - B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j) := by
      rw [← map_sub, hc i j, hδ i j]
    calc B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
          - f.hom.app (op (V i ⊓ V j))
            (((sheafifiedCochainComplex X).X n).1.map
              (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i))
        = (B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
            - B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j))
          - (f.hom.app (op (V i ⊓ V j))
              (((sheafifiedCochainComplex X).X n).1.map
                (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i))
            - f.hom.app (op (V i ⊓ V j))
              (((sheafifiedCochainComplex X).X n).1.map
                (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j)))
          + (B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j)
            - f.hom.app (op (V i ⊓ V j))
              (((sheafifiedCochainComplex X).X n).1.map
                (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j))) := by abel
      _ = B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j)
          - f.hom.app (op (V i ⊓ V j))
            (((sheafifiedCochainComplex X).X n).1.map
              (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j)) := by
          rw [hfc, sub_self, zero_add]
  -- Step E: glue the corrected lifts and conclude
  obtain ⟨b, hb, -⟩ := B.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩)
    (fun i => b₀ i - f.hom.app (op (V i)) (c i))
    (fun i j => hcompat i j)
  refine ⟨b, ?_⟩
  refine R.eq_of_locally_eq' V ⊤ (fun i => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩) _ _ (fun i => ?_)
  rw [← app_res g (homOfLE le_top) b, hb i, map_sub, hb₀ i,
    comp_app_apply_eq_zero f g hfg (V i) (c i), sub_zero]

end GammaTools

end HodgePilot.SingularGamma
