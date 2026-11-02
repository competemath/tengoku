import Tengoku.Seed.Algebra.Category.ModuleCat.Biproducts
import Tengoku.Seed.Algebra.Category.ModuleCat.ChangeOfRings
import Tengoku.Seed.Algebra.Module.Pi
import Tengoku.Seed.Data.Finsupp.Single

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Modules over a finite product of copies of a field

For a finite type `V`, modules over the function ring `V → K` are equivalent
to `V`-indexed families of `K`-modules.  This file constructs the forward
total-space functor and proves it full and faithful.  The inverse object
construction by coordinate idempotents is supplied in the companion file.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.PiRingModule

universe uK uV w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V]

/-- A family of vector spaces indexed by the primitive coordinates.-/
abbrev Family := V → ModuleCat.{w} K

/-- The product of a family, with the pointwise action of `V → K`.-/
abbrev Total (D : Family.{uK, uV, w} K V) := ∀ i, D i

/-- The product family as a module over the coordinate ring.-/
abbrev totalModuleCat (D : Family.{uK, uV, w} K V) :
    ModuleCat.{max uV w} (V → K) :=
  ModuleCat.of (V → K) (Total K V D)

/-- A pointwise family of linear maps induces a linear map of product-ring
modules.-/
def mapTotal {D E : Family.{uK, uV, w} K V} (f : D ⟶ E) :
    Total K V D →ₗ[V → K] Total K V E where
  toFun x i := f i (x i)
  map_add' x y := by
    funext i
    exact (f i).hom.map_add (x i) (y i)
  map_smul' s x := by
    funext i
    exact (f i).hom.map_smul (s i) (x i)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mapTotal_apply {D E : Family.{uK, uV, w} K V} (f : D ⟶ E)
    (x : Total K V D) (i : V) :
    mapTotal (K := K) (V := V) f x i = f i (x i) := rfl

/-- Assemble a family of vector spaces into a module over `V → K`.-/
def totalFunctor :
    CategoryTheory.Functor (Family.{uK, uV, w} K V)
      (ModuleCat.{max uV w} (V → K)) where
  obj := totalModuleCat K V
  map f := ModuleCat.ofHom (mapTotal (K := K) (V := V) f)
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

/-- The coordinate idempotent at `i`.-/
def coordinateIdempotent (i : V) : V → K :=
  Pi.single i 1

omit [Fintype V] in
@[simp]
theorem coordinateIdempotent_apply_self (i : V) :
    coordinateIdempotent K V i i = 1 := by
  simp [coordinateIdempotent]

omit [Fintype V] in
theorem coordinateIdempotent_smul_total
    (D : Family.{uK, uV, w} K V) (i : V)
    (x : Total K V D) :
    coordinateIdempotent K V i • x = Pi.single i (x i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

end QuotientSubmoduleEquidistribution.PiRingModule
