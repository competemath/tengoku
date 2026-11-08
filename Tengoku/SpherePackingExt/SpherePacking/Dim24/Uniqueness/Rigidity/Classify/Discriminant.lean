module
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
public import Tengoku.Seed.LinearAlgebra.BilinearForm.DualLattice
public import Tengoku.Seed.LinearAlgebra.Quotient.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The discriminant group of a `ℤ`-lattice

This file sets up the basic objects needed for the dimension-24 rigidity step: the dual lattice
`L*` (with respect to the real inner product) and the discriminant group `L*/L`.

The eventual plan (paper: `dim_24.tex`, uniqueness clause) is to map the finite set of center
orbits into `L*/L` and use this to build a unimodular overlattice.

## Main definitions
* `Uniqueness.RigidityClassify.DualLattice`
* `Uniqueness.RigidityClassify.latticeInDual`
* `Uniqueness.RigidityClassify.DiscriminantGroup`

## Main lemmas
* `Uniqueness.RigidityClassify.mem_latticeInDual_iff`
* `Uniqueness.RigidityClassify.mk_eq_mk_iff_sub_mem`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
/-- The dual lattice of a `ℤ`-submodule in `ℝ²⁴`, with respect to the real inner product.-/
public abbrev DualLattice (L : Submodule ℤ ℝ²⁴) : Submodule ℤ ℝ²⁴ :=
  LinearMap.BilinForm.dualSubmodule (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) L

/-- View `L` as a submodule of `L*` (by preimage along the inclusion `L* → ℝ²⁴`).-/
@[expose]
public def latticeInDual (L : Submodule ℤ ℝ²⁴) : Submodule ℤ (DualLattice L) :=
  Submodule.comap (Submodule.subtype (DualLattice L)) L

/-- The discriminant group `L*/L` (as a `ℤ`-module).-/
public abbrev DiscriminantGroup (L : Submodule ℤ ℝ²⁴) : Type :=
  (DualLattice L) ⧸ (latticeInDual L)

/-- Membership in `latticeInDual L` is membership in `L` after coercion to `ℝ²⁴`.-/
@[simp]
public lemma mem_latticeInDual_iff (L : Submodule ℤ ℝ²⁴) (x : DualLattice L) :
    x ∈ latticeInDual L ↔ (x : ℝ²⁴) ∈ L :=
  Iff.rfl

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
