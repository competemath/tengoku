import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.RepresentablePosetSpace
import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts
import Tengoku.Seed.CategoryTheory.Preadditive.Yoneda.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fullness of an incidence representable functor

A morphism of represented poset spaces is a linear map on `Hom(P,-)` that
preserves the images of all `Hom(P_t,-)`.  When precomposition along
`P ⟶ P_t` is injective, it therefore lifts uniquely to every projective
coordinate.  If the chosen root maps span all maps from `P` to the boundary
projectives, these coordinate lifts commute with every boundary morphism and
assemble into a module map on the representable of the boundary biproduct.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace MagnitudeConjecture.PosetSpace.RepresentableData

universe u v w z

variable {k T : Type u} {C : Type v} [Field k] [Fintype T] [PartialOrder T]
variable [Category.{u} C] [Preadditive C] [Linear k C]
  [HasFiniteBiproducts C]

/-- The usual finite-biproduct formula, with an index type in an arbitrary
universe.  Mathlib's existing statement currently fixes the index in
`Type 0`.-/
theorem biproduct_lift_eq_sum
    {J : Type w} [Fintype J] {F : J → C} [HasBiproduct F]
    {X : C} (g : ∀ j, X ⟶ F j) :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι F j := by
  classical
  apply biproduct.hom_ext
  intro j
  rw [biproduct.lift_π, Preadditive.sum_comp]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [biproduct.ι_π, hi]
  · simp

/-- Composition through a finite biproduct is the sum of the coordinate
composites, without a universe restriction on the index type.-/
theorem biproduct_lift_desc
    {J : Type w} [Fintype J] {F : J → C} [HasBiproduct F]
    {X Y : C} (g : ∀ j, X ⟶ F j) (h : ∀ j, F j ⟶ Y) :
    biproduct.lift g ≫ biproduct.desc h = ∑ j, g j ≫ h j := by
  rw [biproduct_lift_eq_sum g, Preadditive.sum_comp]
  simp

/-- Reindex a finite biproduct across index types in arbitrary universes.-/
noncomputable def biproductReindex
    {I : Type w} {J : Type z} [Finite I]
    (e : I ≃ J) (F : J → C)
    [HasBiproduct F] [HasBiproduct (fun i ↦ F (e i))] :
    (⨁ fun i ↦ F (e i)) ≅ ⨁ F where
  hom := biproduct.desc fun i ↦ biproduct.ι F (e i)
  inv := biproduct.lift fun i ↦ biproduct.π F (e i)
  hom_inv_id := by
    classical
    letI : Fintype I := Fintype.ofFinite I
    apply biproduct.hom_ext'
    intro i
    rw [Category.comp_id, ← Category.assoc, biproduct.ι_desc,
      biproduct_lift_eq_sum,
      Preadditive.comp_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi
      have he : e i ≠ e i' := fun heq ↦ hi (e.injective heq).symm
      simp only [← Category.assoc, biproduct.ι_π_ne F he, zero_comp]
    · simp
  inv_hom_id := by
    classical
    letI : Fintype I := Fintype.ofFinite I
    apply biproduct.hom_ext'
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    have hrow : biproduct.ι F (e i) ≫
        biproduct.lift (fun i ↦ biproduct.π F (e i)) =
        biproduct.ι (fun i ↦ F (e i)) i := by
      rw [biproduct_lift_eq_sum, Preadditive.comp_sum]
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hi
        have he : e i ≠ e i' := fun heq ↦ hi (e.injective heq).symm
        simp only [← Category.assoc, biproduct.ι_π_ne F he, zero_comp]
      · simp
    rw [Category.comp_id, ← Category.assoc, hrow, biproduct.ι_desc]

/-- The root projective followed by the projectives indexed by the poset.-/
abbrev boundaryFamily (D : RepresentableData k T C) : Option T → C
  | none => D.source
  | some t => D.projective t

/-- The root identity and the chosen maps `P ⟶ P_t`, uniformly indexed.-/
def boundaryUnit (D : RepresentableData k T C) (q : Option T) :
    D.source ⟶ D.boundaryFamily q := by
  cases q with
  | none => exact 𝟙 D.source
  | some t => exact D.unit t

/-- Precomposition with a root-to-boundary map.-/
def boundaryPrecomposition (D : RepresentableData k T C)
    (q : Option T) (X : C) :
    (D.boundaryFamily q ⟶ X) →ₗ[k] (D.source ⟶ X) where
  toFun h := D.boundaryUnit q ≫ h
  map_add' h h' := by simp
  map_smul' c h := by simp

@[simp]
theorem boundaryPrecomposition_apply
    (D : RepresentableData k T C) (q : Option T) (X : C)
    (h : D.boundaryFamily q ⟶ X) :
    D.boundaryPrecomposition q X h = D.boundaryUnit q ≫ h :=
  rfl

/-- The biproduct of the root and all non-root boundary projectives.-/
abbrev boundaryGenerator (D : RepresentableData k T C) : C :=
  ⨁ D.boundaryFamily

theorem boundaryPrecomposition_injective
    (D : RepresentableData k T C)
    (hinj : ∀ (t : T) (X : C),
      Function.Injective (D.precomposition t X))
    (q : Option T) (X : C) :
    Function.Injective (D.boundaryPrecomposition q X) := by
  cases q with
  | none =>
      intro h h' hEq
      rw [D.boundaryPrecomposition_apply,
        D.boundaryPrecomposition_apply] at hEq
      simpa [boundaryUnit] using hEq
  | some t =>
      change Function.Injective (D.precomposition t X)
      exact hinj t X

end MagnitudeConjecture.PosetSpace.RepresentableData
