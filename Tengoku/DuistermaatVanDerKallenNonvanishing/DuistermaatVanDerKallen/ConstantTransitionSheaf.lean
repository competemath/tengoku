import Tengoku.Seed.Topology.Sheaves.LocalPredicate
import Tengoku.Seed.Topology.Sheaves.EtaleSpace
import Tengoku.Seed.Topology.LocallyConstant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A sheaf from dependent fibers with constant coordinate transitions.
The constructions identify the actual stalks; no gluing axiom is assumed. -/

open Set CategoryTheory TopologicalSpace Opposite Filter
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- An atlas on a family of sets with globally constant transitions on each
overlap. The convex good neighborhoods used below satisfy this condition.-/
structure ConstantTransitionAtlas (X : TopCat) (T : X → Type) where
  Index : Type
  domain : Index → Opens X
  model : Index → Type
  coord : ∀ i, ∀ x : domain i, T x.val ≃ model i
  cover : ∀ x : X, ∃ i, x ∈ domain i
  transition : ∀ i j (x y : X) (hxi : x ∈ domain i) (hxj : x ∈ domain j)
    (hyi : y ∈ domain i) (hyj : y ∈ domain j) (v : model i),
    coord j ⟨x, hxj⟩ ((coord i ⟨x, hxi⟩).symm v) =
      coord j ⟨y, hyj⟩ ((coord i ⟨y, hyi⟩).symm v)

namespace ConstantTransitionAtlas
variable {X : TopCat} {T : X → Type} (A : ConstantTransitionAtlas X T)

/-- A section constant in one coordinate chart.-/
def prelocal : TopCat.PrelocalPredicate T where
  pred {U} f := ∃ (i : A.Index) (h : U ≤ A.domain i) (v : A.model i),
    ∀ x : U, A.coord i ⟨x.val, h x.property⟩ (f x) = v
  res {U V} j f hf := by
    obtain ⟨i, h, v, he⟩ := hf
    exact ⟨i, j.le.trans h, v, fun x => he (j x)⟩

/-- Locally constant coordinate sections form an actual sheaf.-/
def sectionPredicate : TopCat.LocalPredicate T := A.prelocal.sheafify

def sheaf : TopCat.Sheaf (Type _) X := TopCat.subsheafToTypes A.sectionPredicate

/-- The constant-coordinate section with value `v`.-/
def constantSection (i : A.Index) (v : A.model i) (x : A.domain i) : T x.val :=
  (A.coord i x).symm v

theorem constantSection_prelocal (i : A.Index) (v : A.model i) :
    A.prelocal.pred (A.constantSection i v) :=
  ⟨i, le_rfl, v, fun x => (A.coord i x).apply_symm_apply v⟩

theorem constantSection_local (i : A.Index) (v : A.model i) :
    A.sectionPredicate.pred (A.constantSection i v) :=
  A.prelocal.sheafifyOf (A.constantSection_prelocal i v)

/-- Equal constant-coordinate values at one point determine the same section
throughout an overlap, by the constant transition identity.-/
theorem constantSection_eq (i j : A.Index) {x y : X}
    (hxi : x ∈ A.domain i) (hxj : x ∈ A.domain j)
    (hyi : y ∈ A.domain i) (hyj : y ∈ A.domain j)
    (v : A.model i) (w : A.model j)
    (he : A.constantSection i v ⟨x, hxi⟩ = A.constantSection j w ⟨x, hxj⟩) :
    A.constantSection i v ⟨y, hyi⟩ = A.constantSection j w ⟨y, hyj⟩ := by
  apply (A.coord j ⟨y, hyj⟩).injective
  change A.coord j ⟨y, hyj⟩ ((A.coord i ⟨y, hyi⟩).symm v) = _
  rw [← A.transition i j x y hxi hxj hyi hyj v]
  exact congrArg (A.coord j ⟨x, hxj⟩) he |>.trans (by simp [constantSection])

/-- Two sections constant in possibly different charts and equal at one
point agree on their whole overlap.-/
theorem prelocal_eq {U V : Opens X} (f : ∀ x : U, T x.val) (g : ∀ x : V, T x.val)
    (hf : A.prelocal.pred f) (hg : A.prelocal.pred g)
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V) (he : f ⟨x, hxU⟩ = g ⟨x, hxV⟩)
    {y : X} (hyU : y ∈ U) (hyV : y ∈ V) : f ⟨y, hyU⟩ = g ⟨y, hyV⟩ := by
  obtain ⟨i, hUi, v, hfv⟩ := hf
  obtain ⟨j, hVj, w, hgw⟩ := hg
  have hfi : ∀ z : U, f z = A.constantSection i v ⟨z.val, hUi z.property⟩ := by
    intro z
    apply (A.coord i ⟨z.val, hUi z.property⟩).injective
    simpa only [constantSection, Equiv.apply_symm_apply] using hfv z
  have hgj : ∀ z : V, g z = A.constantSection j w ⟨z.val, hVj z.property⟩ := by
    intro z
    apply (A.coord j ⟨z.val, hVj z.property⟩).injective
    simpa only [constantSection, Equiv.apply_symm_apply] using hgw z
  rw [hfi, hgj] at he ⊢
  exact A.constantSection_eq i j (hUi hxU) (hVj hxV) (hUi hyU) (hVj hyV) v w he

/-- Every element of an actual fiber is the value of an allowed local section.-/
theorem stalkToFiber_surjective (x : X) :
    Function.Surjective (TopCat.stalkToFiber A.sectionPredicate x) := by
  apply TopCat.stalkToFiber_surjective
  intro t
  obtain ⟨i, hi⟩ := A.cover x
  refine ⟨⟨A.domain i, hi⟩, A.constantSection i (A.coord i ⟨x, hi⟩ t),
    A.constantSection_local i _, ?_⟩
  exact (A.coord i ⟨x, hi⟩).symm_apply_apply t

/-- Equal values of allowed sections determine the same germ.-/
theorem stalkToFiber_injective (x : X) :
    Function.Injective (TopCat.stalkToFiber A.sectionPredicate x) := by
  apply TopCat.stalkToFiber_injective
  intro U V f hf g hg he
  obtain ⟨U', hxU', iU, hf'⟩ := hf ⟨x, U.property⟩
  obtain ⟨V', hxV', iV, hg'⟩ := hg ⟨x, V.property⟩
  let W : OpenNhds x := ⟨U' ⊓ V', hxU', hxV'⟩
  refine ⟨W, homOfLE (inf_le_left.trans iU.le), homOfLE (inf_le_right.trans iV.le), ?_⟩
  intro y
  exact A.prelocal_eq (fun z => f (iU z)) (fun z => g (iV z)) hf' hg' hxU' hxV' he
    y.property.1 y.property.2

/-- The actual stalk of the constructed sheaf is the specified fiber.-/
def stalkEquiv (x : X) : A.sheaf.presheaf.stalk x ≃ T x :=
  Equiv.ofBijective (TopCat.stalkToFiber A.sectionPredicate x)
    ⟨A.stalkToFiber_injective x, A.stalkToFiber_surjective x⟩

/-- A section constant in one chart has constant coordinates in every chart
containing its domain.-/
theorem prelocal_coordinate_constant {U : Opens X} (f : ∀ x : U, T x.val)
    (hf : A.prelocal.pred f) (i : A.Index) (hUi : U ≤ A.domain i) (x y : U) :
    A.coord i ⟨x.val, hUi x.property⟩ (f x) = A.coord i ⟨y.val, hUi y.property⟩ (f y) := by
  obtain ⟨j, hUj, v, hfv⟩ := hf
  have he : ∀ z : U, f z = (A.coord j ⟨z.val, hUj z.property⟩).symm v := by
    intro z
    apply (A.coord j ⟨z.val, hUj z.property⟩).injective
    simpa only [Equiv.apply_symm_apply] using hfv z
  rw [he x, he y]
  exact A.transition j i x.val y.val (hUj x.property) (hUi x.property)
    (hUj y.property) (hUi y.property) v

/-- Allowed sections have locally constant coordinates in each chart.-/
theorem coordinate_locallyConstant {U : Opens X} (f : ∀ x : U, T x.val)
    (hf : A.sectionPredicate.pred f) (i : A.Index) (hUi : U ≤ A.domain i) :
    IsLocallyConstant (fun x : U => A.coord i ⟨x.val, hUi x.property⟩ (f x)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨V, hxV, j, hV⟩ := hf x
  refine ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val, hxV, ?_⟩
  intro y hy
  exact A.prelocal_coordinate_constant (fun z => f (j z)) hV i (j.le.trans hUi)
    ⟨y.val, hy⟩ ⟨x.val, hxV⟩

/-- On a connected chart domain, an allowed section is determined by its
value at any one point.-/
theorem section_eval_injective (i : A.Index) [PreconnectedSpace (A.domain i)] (x : A.domain i) :
    Function.Injective (fun f : A.sheaf.presheaf.obj (op (A.domain i)) => f.val x) := by
  intro f g he
  apply Subtype.ext
  funext y
  apply (A.coord i y).injective
  have hf := A.coordinate_locallyConstant f.val f.property i le_rfl
  have hg := A.coordinate_locallyConstant g.val g.property i le_rfl
  exact (hf.apply_eq_of_preconnectedSpace y x).trans
    ((congrArg (A.coord i x) he).trans (hg.apply_eq_of_preconnectedSpace x y))

/-- Every element of a fiber extends over its entire chart domain.-/
theorem section_eval_surjective (i : A.Index) (x : A.domain i) :
    Function.Surjective (fun f : A.sheaf.presheaf.obj (op (A.domain i)) => f.val x) := by
  intro t
  exact ⟨⟨A.constantSection i (A.coord i x t), A.constantSection_local i _⟩,
    (A.coord i x).symm_apply_apply t⟩

/-- On a connected chart, every germ extends to one unique section.-/
theorem germ_bijective (i : A.Index) [PreconnectedSpace (A.domain i)] (x : X) (hx : x ∈ A.domain i) :
    Function.Bijective (A.sheaf.presheaf.germ (A.domain i) x hx) := by
  constructor
  · intro f g he
    apply A.section_eval_injective i ⟨x, hx⟩
    have hh := congrArg (TopCat.stalkToFiber A.sectionPredicate x) he
    exact (TopCat.stalkToFiber_germ A.sectionPredicate (A.domain i) x hx f).symm.trans
      (hh.trans (TopCat.stalkToFiber_germ A.sectionPredicate (A.domain i) x hx g))
  · intro t
    obtain ⟨f, hf⟩ := A.section_eval_surjective i ⟨x, hx⟩ (TopCat.stalkToFiber A.sectionPredicate x t)
    refine ⟨f, A.stalkToFiber_injective x ?_⟩
    exact (TopCat.stalkToFiber_germ A.sectionPredicate (A.domain i) x hx f).trans hf

/-- Connected domains with constant transitions give an actual covering
projection from the sheaf's étalé space, with the prescribed fibers as stalks.-/
theorem isCoveringMap_etale (hconnected : ∀ i, PreconnectedSpace (A.domain i)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := A.sheaf.presheaf)) := by
  apply TopCat.Presheaf.EtaleSpace.isCoveringMap_base
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  let : PreconnectedSpace (A.domain i) := hconnected i
  exact ⟨A.domain i, hi, fun y hy => A.germ_bijective i y hy⟩

end ConstantTransitionAtlas
end
end DuistermaatVanDerKallen
