import Tengoku.Seed.Algebra.Category.FGModuleCat.Colimits
import Tengoku.Seed.Algebra.Category.FGModuleCat.Limits
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finrank under additive functors of finite-dimensional vector spaces

Every finite-dimensional vector space is a finite biproduct of copies of the
ground field.  Consequently an additive endofunctor of `FGModuleCat k`
multiplies finrank by its value on the one-dimensional object.  This is the
small categorical calculation used to extend the string-detector delta
formula from coefficient space `k` to every finite coefficient space.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.FiniteVectorSpace

universe u

variable {k : Type u} [Field k]

/-- The underlying space of a finite biproduct is linearly equivalent to the
ordinary dependent product of the underlying spaces.-/
def biproductLinearEquivPi {n : ℕ} (V : Fin n → FGModuleCat.{u} k) :
    ((⨁ V : FGModuleCat.{u} k) : Type u) ≃ₗ[k]
      (∀ i, V i) :=
  let U := forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)
  ((U.mapIso (biproduct.isoProduct V)).toLinearEquiv).trans
    (((preservesLimitIso U (Discrete.functor V)).toLinearEquiv).trans
      (((HasLimit.isoOfNatIso
          (Discrete.compNatIsoDiscrete V U)).toLinearEquiv).trans
        (ModuleCat.piIsoPi (fun i ↦ (V i).obj)).toLinearEquiv))

/-- Finrank is additive on a finite biproduct of finite-dimensional vector
spaces.
@isnad1 id=eq.0h3v.s9.f1bc91e967e8 from=translated src=- shape=5a86c2b2 vocab=8ae660d2
-/
theorem finrank_biproduct {n : ℕ} (V : Fin n → FGModuleCat.{u} k) :
    Module.finrank k ((⨁ V : FGModuleCat.{u} k) : Type u) =
      ∑ i, Module.finrank k (V i) := by
  exact (biproductLinearEquivPi V).finrank_eq.trans
    (Module.finrank_pi_fintype k)

/-- The same finrank formula for an index type in the ambient universe.-/
def biproductLinearEquivPiSameUniverse {ι : Type u} [Fintype ι]
    (V : ι → FGModuleCat.{u} k) :
    ((⨁ V : FGModuleCat.{u} k) : Type u) ≃ₗ[k]
      (∀ i, V i) :=
  let U := forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)
  ((U.mapIso (biproduct.isoProduct V)).toLinearEquiv).trans
    (((preservesLimitIso U (Discrete.functor V)).toLinearEquiv).trans
      (((HasLimit.isoOfNatIso
          (Discrete.compNatIsoDiscrete V U)).toLinearEquiv).trans
        (ModuleCat.piIsoPi (fun i ↦ (V i).obj)).toLinearEquiv))

/-- A finite-dimensional vector space is isomorphic to the finite biproduct
of `finrank` copies of the ground field.-/
def isoBiproductUnit (V : FGModuleCat.{u} k) :
    V ≅ ⨁ fun _ : Fin (Module.finrank k V) ↦ FGModuleCat.of k k :=
  let coordinateEquiv : V ≃ₗ[k] (Fin (Module.finrank k V) → k) :=
    (Module.finBasis k V).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite k k (Fin (Module.finrank k V))
  let copies := fun _ : Fin (Module.finrank k V) ↦ FGModuleCat.of k k
  (coordinateEquiv.trans (biproductLinearEquivPi copies).symm).toFGModuleCatIso

/-- An additive endofunctor of finite-dimensional vector spaces scales
finrank by the finrank of its value on the ground field.
@isnad1 id=eq.0h3v.s10.e89e04f49c80 from=translated src=- shape=cb67a6ac vocab=806ca4b3
-/
theorem finrank_map_eq_mul (F : FGModuleCat.{u} k ⥤ FGModuleCat.{u} k)
    [F.Additive] (V : FGModuleCat.{u} k) :
    Module.finrank k (F.obj V) =
      Module.finrank k V * Module.finrank k (F.obj (FGModuleCat.of k k)) := by
  let copies := fun _ : Fin (Module.finrank k V) ↦ FGModuleCat.of k k
  let e : F.obj V ≅ ⨁ fun i ↦ F.obj (copies i) :=
    F.mapIso (isoBiproductUnit V) ≪≫ F.mapBiproduct copies
  calc
    Module.finrank k (F.obj V) =
        Module.finrank k (⨁ fun i ↦ F.obj (copies i) : FGModuleCat.{u} k) :=
      (FGModuleCat.isoToLinearEquiv e).finrank_eq
    _ = ∑ _ : Fin (Module.finrank k V),
        Module.finrank k (F.obj (FGModuleCat.of k k)) := by
      rw [finrank_biproduct]
    _ = Module.finrank k V *
        Module.finrank k (F.obj (FGModuleCat.of k k)) := by
      simp

end MagnitudeConjecture.FiniteVectorSpace
