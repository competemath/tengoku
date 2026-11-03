/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vanishing of maps from a single object into `D^{≤ -1}`

Let `E : A` and let `P` be a class of objects of `A` such that `Ext^k(E, Y) = 0` for every
`k ≥ 1` and every `Y` in `P`. Then there is no nonzero map from `(singleFunctor A 0).obj E`
into a bounded object of `D^{≤ -1}` whose cohomology objects lie in `P`. This is the
statement that the hypercohomology `Hom(E, M[j])` of such an `M` is computed by
`Hom(E, H^j M)` alone, in the only case where the answer is zero; the proof is dévissage on
the amplitude along the truncation triangles.

The geometric instance is `𝒪_X` on an affine scheme with `P` quasi-coherence, where the
hypothesis is affine vanishing through `Ext^k(𝒪_X, F) ≃ H^k(F)`. That instance is the
bounded half of the compactness of `𝒪_X` in `Dqc(Spec R)` (#723); the unbounded half needs
`M ≅ holim τ≥-n M`, which is not available at this Mathlib pin.

## Main results

* `DerivedCategory.hom_singleFunctor_eq_zero_of_ext_subsingleton` — the single case.
* `DerivedCategory.hom_eq_zero_of_isGE_of_isLE_neg_of_cohomologyIn` — the dévissage.
-/

universe w v u

open CategoryTheory Category Limits Pretriangulated Abelian

namespace DerivedCategory

attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms] (E : A)
  (hE : ∀ (Y : A), P Y → ∀ (k : ℕ), Subsingleton (Ext.{w} E Y (k + 1)))

include hE

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- No maps from `single 0 E` into `single a Y` for `a < 0` and `Y` in `P`: such a map is a
class in `Ext^{-a}(E, Y)`.
@isnad1 id=eq.2h7v.s8.cfc41e9fd842 from=translated src=- shape=e0909c27 vocab=c9056607
-/
lemma hom_singleFunctor_eq_zero_of_ext_subsingleton {Y : A} (hY : P Y) {a : ℤ} (ha : a < 0)
    (f : (singleFunctor A 0).obj E ⟶ (singleFunctor A a).obj Y) : f = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, a = -((k : ℤ) + 1) := ⟨(-a - 1).toNat, by omega⟩
  let e : (singleFunctor A (-((k : ℤ) + 1))).obj Y ≅
      ((singleFunctor A 0).obj Y)⟦((k + 1 : ℕ) : ℤ)⟧ :=
    (((singleFunctors A).shiftIso ((k + 1 : ℕ) : ℤ) (-((k : ℤ) + 1)) 0
      (by push_cast; omega)).app Y).symm
  have hz : Subsingleton (ShiftedHom ((singleFunctor A 0).obj E)
      ((singleFunctor A 0).obj Y) ((k + 1 : ℕ) : ℤ)) :=
    haveI := hE Y hY k
    Ext.homEquiv.symm.subsingleton
  have h : f ≫ e.hom = 0 := @Subsingleton.elim _ hz _ _
  calc f = (f ≫ e.hom) ≫ e.inv := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = 0 := by rw [h, zero_comp]

end DerivedCategory
