import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationDirected.HomBiproductFinrank
import Tengoku.Seed.CategoryTheory.Limits.Shapes.CombinedProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reindexing multiplicity biproducts

These isomorphisms split one label's copies from a finite multiplicity
biproduct.  The final form is the associativity/reindexing step required by
the directed effective-lifting induction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe uI uJ uK uC vC

variable {I : Type uI} [DecidableEq I]

private def eraseForward
    (S : Finset I) {i : I} (n n' : I → ℕ)
    (hcount : ∀ a, a ∈ S.erase i → n' a = n a)
    (p : MultiplicityIndex S n) :
    MultiplicityIndex (S.erase i) n' ⊕ Fin (n i) := by
  by_cases hpi : p.1.1 = i
  · exact Sum.inr (Fin.cast (congrArg n hpi) p.2)
  · exact Sum.inl
      ⟨⟨p.1.1, Finset.mem_erase.mpr ⟨hpi, p.1.2⟩⟩,
        Fin.cast (hcount p.1.1
          (Finset.mem_erase.mpr ⟨hpi, p.1.2⟩)).symm p.2⟩

private def eraseBackward
    (S : Finset I) {i : I} (hi : i ∈ S)
    (n n' : I → ℕ)
    (hcount : ∀ a, a ∈ S.erase i → n' a = n a) :
    MultiplicityIndex (S.erase i) n' ⊕ Fin (n i) →
      MultiplicityIndex S n
  | Sum.inl p =>
      ⟨⟨p.1.1, (Finset.mem_erase.mp p.1.2).2⟩,
        Fin.cast (hcount p.1.1 p.1.2) p.2⟩
  | Sum.inr p => ⟨⟨i, hi⟩, p⟩

section BiproductSum

variable {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- A biproduct indexed by a sum type is the binary biproduct of its two
indexed pieces.-/
def biproductSumIso (X : J → C) (Y : K → C) :
    (⨁ fun p : J ⊕ K => Sum.elim X Y p) ≅
      biprod (⨁ X) (⨁ Y) := by
  let h : IsLimit
      (Fan.mk (biprod (⨁ X) (⨁ Y))
        (Fan.combPairHoms
          (biproduct.bicone X).toCone
          (biproduct.bicone Y).toCone
          (BinaryBiproduct.bicone (⨁ X) (⨁ Y)).toCone)) :=
    Fan.combPairIsLimit
      (biproduct.isLimit X)
      (biproduct.isLimit Y)
      (BinaryBiproduct.isLimit (⨁ X) (⨁ Y))
  exact (h.conePointUniqueUpToIso
    (biproduct.isLimit (fun p : J ⊕ K => Sum.elim X Y p))).symm

end BiproductSum

section MultiplicityBiproductErase

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

end MultiplicityBiproductErase

end QuotientSubmoduleEquidistribution.RepresentationDirected
