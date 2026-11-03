import Tengoku.Seed.RingTheory.Morita.Basic
import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.Algebra.Category.ModuleCat.Subobject
import Tengoku.Seed.Algebra.Category.FGModuleCat.Basic
import Tengoku.Seed.CategoryTheory.ObjectProperty.Equivalence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restricting a Morita equivalence to finitely generated modules

For modules over Artinian rings, finite generation is equivalent to the
ascending chain condition.  The latter is invariant under a category
equivalence because such an equivalence induces an order isomorphism on
subobjects.  This gives a restriction of Mathlib's `MoritaEquivalence`,
whose datum lives on all `ModuleCat`s, to `FGModuleCat`.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.MoritaRestriction

universe uK uA uB

section Order

variable {α : Type*} {β : Type*} [PartialOrder α] [PartialOrder β]

/-- Well-foundedness of strict descent is invariant under an order
isomorphism.
@isnad1 id=iff.0h3v.s5.0179c1955b4f from=translated src=- shape=b720df5a vocab=ec3b2cd5
-/
theorem wellFoundedGT_iff_of_orderIso (e : α ≃o β) :
    WellFoundedGT α ↔ WellFoundedGT β := by
  rw [wellFoundedGT_iff_monotone_chain_condition,
    wellFoundedGT_iff_monotone_chain_condition]
  constructor
  · intro h f
    let g : ℕ →o α :=
      ⟨fun n ↦ e.symm (f n), e.symm.monotone.comp f.monotone⟩
    obtain ⟨n, hn⟩ := h g
    exact ⟨n, fun m hm ↦ e.symm.injective (hn m hm)⟩
  · intro h f
    let g : ℕ →o β :=
      ⟨fun n ↦ e (f n), e.monotone.comp f.monotone⟩
    obtain ⟨n, hn⟩ := h g
    exact ⟨n, fun m hm ↦ e.injective (hn m hm)⟩

end Order

section Equivalence

variable {A : Type uA} [Ring A] {B : Type uB} [Ring B]

/-- A category equivalence of module categories induces the expected order
isomorphism between the lattices of algebraic submodules.-/
def submoduleOrderIso
    (e : ModuleCat.{max uA uB} A ≌ ModuleCat.{max uA uB} B)
    (M : ModuleCat.{max uA uB} A) :
    Submodule A M ≃o Submodule B (e.functor.obj M) :=
  (ModuleCat.subobjectModule M).symm |>.trans
    ((Subobject.lowerEquivalence
      (MonoOver.congr M e)).toOrderIso) |>.trans
    (ModuleCat.subobjectModule (e.functor.obj M))

end Equivalence

section Morita

variable (K : Type uK) [CommSemiring K]
  (A : Type uA) [Ring A] [Algebra K A]
  (B : Type uB) [Ring B] [Algebra K B]
  [IsArtinianRing A] [IsArtinianRing B]

end Morita

section FiniteDimensionalMorita

variable (K : Type uK) [Field K]
  (A : Type uA) [Ring A] [Algebra K A] [FiniteDimensional K A]
  (B : Type uB) [Ring B] [Algebra K B] [FiniteDimensional K B]

end FiniteDimensionalMorita

end QuotientSubmoduleEquidistribution.MoritaRestriction
