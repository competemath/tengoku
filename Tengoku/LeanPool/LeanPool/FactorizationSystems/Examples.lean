/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/
module

public import Tengoku.LeanPool.LeanPool.FactorizationSystems.Basic
public import Tengoku

/-!
# LeanPool.FactorizationSystems.Examples
-/

@[expose] public section

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

/-
We construct an example of factorization system: (Mono,Epi) on Set
-/

/- Every iso is an epi -/
/--
@isnad1 id=epimorph.0h5v.s5.d1609fa51bb5 from=translated src=- shape=51dae6c3 vocab=ffeded5e
-/
lemma isIsoIsEpi : {X Y : C} → (f : X ⟶ Y) →
      MorphismProperty.isomorphisms _ f → MorphismProperty.epimorphisms _ f := by
  intro X Y f hf
  simp at hf
  exact {left_cancellation := by exact (IsIso.epi_of_iso f).left_cancellation}

/- Iso ⊆ Epi -/
/--
@isnad1 id=contains.0h1v.s3.fe7db596e258 from=translated src=- shape=84bfdc15 vocab=5faa1802
-/
lemma epimorphismsContainsIsos : containsIsos (MorphismProperty.epimorphisms C) := by
    intro X Y isof
    exact isIsoIsEpi isof.hom (Iso.isIso_hom isof)

/- Epimorphisms are closed under composition -/
/--
@isnad1 id=isclosed.0h1v.s3.9d442b73a463 from=translated src=- shape=84bfdc15 vocab=d8016d78
-/
lemma epimorphismsClosedUnderComp : is_closed_comp (MorphismProperty.epimorphisms C) where
    precomp := by exact epi_comp
    postcomp := by
        simp_all

/- Every iso is a mono -/
/--
@isnad1 id=monomorp.0h5v.s5.3901a8245a5a from=translated src=- shape=51dae6c3 vocab=56aa4b7c
-/
lemma isIsoIsMono : {X Y : C} → (f : X ⟶ Y) →
        MorphismProperty.isomorphisms _ f → MorphismProperty.monomorphisms _ f := by
    intro X Y f hf
    simp at hf
    exact {right_cancellation := by exact (IsIso.mono_of_iso f).right_cancellation}

/- Mono ⊆ Iso -/
/--
@isnad1 id=contains.0h1v.s3.add0988dba70 from=translated src=- shape=84bfdc15 vocab=b30a0062
-/
lemma monomorphismsContainsIsos : containsIsos (MorphismProperty.monomorphisms C) := by
    intro X Y isof
    exact isIsoIsMono isof.hom (Iso.isIso_hom isof)

/- Monomorphisms are closed under composition -/
/--
@isnad1 id=isclosed.0h1v.s3.8cee7baf1593 from=translated src=- shape=84bfdc15 vocab=ee0dff37
-/
lemma monomorphismsClosedUnderComp : is_closed_comp (MorphismProperty.monomorphisms C) where
    precomp := by exact mono_comp
    postcomp := by
        simp_all

/- The image of a function of sets -/
/-- Imported FactorizationSystems declaration. -/
def imageSet {X Y : Type u} (f : X ⟶ Y) : Type u := {y : Y // ∃ x : X , f x = y}

/- Left map of the image factorization of a map -/
/-- Imported FactorizationSystems declaration. -/
def leftMapSet {X Y : Type u} (f : X ⟶ Y) : X ⟶ imageSet f :=
  TypeCat.ofHom fun x => ⟨f x, ⟨x, rfl⟩⟩

/- Right map of the image factorization of a map -/
/-- Imported FactorizationSystems declaration. -/
def rightMapSet {X Y : Type u} (f : X ⟶ Y) : imageSet f ⟶ Y :=
  TypeCat.ofHom fun y => y.1

/- The image factorization of a map -/
/--
@isnad1 id=eq.0h3v.s5.fed6571d42b7 from=translated src=- shape=8e27d465 vocab=2dff3c0e
-/
lemma factorization_set {X Y : Type u} (f : X ⟶ Y) :
    leftMapSet f ≫ rightMapSet f = f := by
  ext x
  rfl

/- The left map of the image factorization of a map is epi -/
/--
@isnad1 id=epimorph.0h3v.s4.e6e40a52c374 from=translated src=- shape=37fe7772 vocab=2340508d
-/
lemma left_map_in_left_class_set {X Y : Type u} (f : X ⟶ Y) :
    MorphismProperty.epimorphisms _ (leftMapSet f) := by
  apply (epi_iff_surjective (leftMapSet f)).mpr
  rintro ⟨fx, ⟨x, hx⟩⟩
  use x
  apply Subtype.ext
  exact hx

/- The right map of the image factorization of a map is mono -/
/--
@isnad1 id=monomorp.0h3v.s4.e4341fb33ee7 from=translated src=- shape=904b8b8c vocab=efd6788b
-/
lemma right_map_in_right_class_set {X Y : Type u} (f : X ⟶ Y) :
    MorphismProperty.monomorphisms _ (rightMapSet f) := by
  apply (mono_iff_injective (rightMapSet f)).mpr
  intro x y h
  apply Subtype.ext
  exact h

/- Given another (Epi,Mono) factorization of a map, there
is a unique way solve the corresponding lifting problem -/
/--
@isnad1 id=existsun.1h9v.s7.04d92dbfcb6e from=translated src=- shape=e47331b4 vocab=9f104a24
-/
lemma factorization_iso_set_hom' {X Y : Type u} (f : X ⟶ Y) (im : Type u)
    (left : X ⟶ im) (_ : MorphismProperty.epimorphisms _ left) (right : im ⟶ Y)
    (q : MorphismProperty.monomorphisms _ right) (fact : left ≫ right = f) (y : imageSet f) :
    ∃! y' : im, right y' = (rightMapSet f) y := by
  let ⟨fx, P⟩ := y
  have injectiveRight : Function.Injective right := by
    exact (mono_iff_injective right).mp q
  obtain ⟨x, hx⟩ := P
  have hfact : right (left x) = f x := by
    simpa using congrArg (fun h : X ⟶ Y => h x) fact
  refine ⟨left x, hfact.trans hx, ?_⟩
  intro y' hy
  apply injectiveRight
  exact hy.trans (hfact.trans hx).symm

/- A (unique) way of solving the lifting problem, i.e. a diagonal filler -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def factorizationIsoSetHom : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) → imageSet f ⟶ im := by
  intro X Y f im left p right q fact
  exact TypeCat.ofHom fun y => (factorization_iso_set_hom' f im left p right q fact y).choose

/- The commutiativity of the right triangle with the diagonal filler -/
/--
@isnad1 id=eq.1h8v.s6.02fb6fa560f3 from=translated src=- shape=b8e80150 vocab=7a1241f6
-/
lemma factorization_iso_set_hom_comm_right : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    factorizationIsoSetHom f im left p right q fact ≫ right = rightMapSet f := by
  intro X Y f im left p right q fact
  ext y
  exact (Exists.choose_spec (factorization_iso_set_hom' f im left p right q fact y)).left

/- The commutiativity of the left triangle with the diagonal filler -/
/--
@isnad1 id=eq.1h8v.s6.d77213ca4398 from=translated src=- shape=1471001b vocab=2a1e98b8
-/
lemma factorization_iso_set_hom_comm_left : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    leftMapSet f ≫ factorizationIsoSetHom f im left p right q fact = left := by
  intro X Y f im left p right q fact
  apply q.right_cancellation
  rw [Category.assoc, factorization_iso_set_hom_comm_right f im left p right q fact,
    factorization_set f, fact]

/- The inverse of the solution to the lifting problem -/
/-- Imported FactorizationSystems declaration. -/
def factorizationIsoSetInv : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) → (left : X ⟶ im) →
    (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) → im ⟶ imageSet f := by
  intro X Y f im left p right fact
  exact TypeCat.ofHom fun y =>
  have existence : ∃ x : X, f x = right y := by
    have surjectiveLeft : Function.Surjective left := by
      exact (epi_iff_surjective left).mp p
    obtain ⟨x, hx⟩ := surjectiveLeft y
    use x
    have hfact : right (left x) = f x := by
      simpa using congrArg (fun h : X ⟶ Y => h x) fact
    exact hfact.symm.trans (congrArg right hx)
  ⟨right y, existence⟩

/- The commutiativity of the right triangle with the inverse to the diagonal filler -/
/--
@isnad1 id=eq.1h7v.s6.896580e7069c from=translated src=- shape=efcd6c07 vocab=8ff2d58c
-/
lemma factorization_iso_set_inv_comm_right : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) →
    factorizationIsoSetInv f im left p right fact ≫ rightMapSet f = right := by
  intro X Y f im left p right fact
  ext y
  rfl

/- The commutiativity of the left triangle with the inverse to the diagonal filler -/
/--
@isnad1 id=eq.1h7v.s6.d4e78330beb2 from=translated src=- shape=54236fa8 vocab=9117e6bc
-/
lemma factorization_iso_set_inv_comm_left : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (fact : left ≫ right = f) →
    left ≫ factorizationIsoSetInv f im left p right fact = leftMapSet f := by
  intro X Y f im left p right fact
  ext x
  apply Subtype.ext
  exact congrArg (fun h : X ⟶ Y => h x) fact

/- The factorization isomorphism -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def factorizationIsoSet : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) → (left : X ⟶ im) →
    (MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (MorphismProperty.monomorphisms _ right) → (left ≫ right = f) →
    Σ' i : imageSet f ≅ im,
      leftMapSet  f ≫ i.hom = left ∧ i.hom ≫ right = rightMapSet f := by
  intro X Y f im left p right q fact
  exact {
    fst := by exact {
      hom := factorizationIsoSetHom f im left p right q fact
      inv := factorizationIsoSetInv f im left p right fact
      hom_inv_id := by
        ext y
        apply Subtype.ext
        exact (Exists.choose_spec (factorization_iso_set_hom' f im left p right q fact y)).left
      inv_hom_id := by
        ext y
        apply (mono_iff_injective right).mp q
        exact (Exists.choose_spec
          (factorization_iso_set_hom' f im left p right q fact
            (factorizationIsoSetInv f im left p right fact y))).left
    }
    snd := by exact {
      left := factorization_iso_set_hom_comm_left f im left p right q fact
      right := factorization_iso_set_hom_comm_right f im left p right q fact
    }
  }

/- The uniqueness of the factorization isomorphism -/
/--
@isnad1 id=eq.3h9v.s8.117a6db946f2 from=translated src=- shape=12c5559a vocab=63b8be24
-/
lemma factorization_iso_is_unique_set : {X Y : Type u} → (f : X ⟶ Y) → (im : Type u) →
    (left : X ⟶ im) → (p : MorphismProperty.epimorphisms _ left) → (right : im ⟶ Y) →
    (q : MorphismProperty.monomorphisms _ right) → (fact : left ≫ right = f) →
    (i : imageSet f ≅ im) → (leftMapSet f ≫ i.hom = left) →
    (_ : i.hom ≫ right = rightMapSet f) →
    i = (factorizationIsoSet f im left p right q fact).fst := by
  intro X Y f im left p right q fact i comm_left _
  apply Iso.ext
  apply (left_map_in_left_class_set f).left_cancellation
  exact comm_left.trans
    (factorization_iso_set_hom_comm_left f im left p right q fact).symm

/- The (Epi,Mono) factorization system on Set -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def EpiMonoSet : FactorizationSystem
    (MorphismProperty.epimorphisms (Type u)) (MorphismProperty.monomorphisms (Type u)) := {
  contains_isos_left_class := epimorphismsContainsIsos
  contains_isos_right_class := monomorphismsContainsIsos
  is_closed_comp_left_class := epimorphismsClosedUnderComp
  is_closed_comp_right_class := monomorphismsClosedUnderComp
  image := imageSet
  leftMap := leftMapSet
  rightMap := rightMapSet
  factorization := factorization_set
  left_map_in_left_class := left_map_in_left_class_set
  right_map_in_right_class := right_map_in_right_class_set
  factorizationIso := factorizationIsoSet
  factorization_iso_is_unique := factorization_iso_is_unique_set }

end CategoryTheory
