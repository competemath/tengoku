import Tengoku.Seed.Algebra.DirectSum.Decomposition
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite support of an internal vector-space grading

A finite-dimensional internally graded space has only finitely many nonzero
degrees. We exhibit a support from the homogeneous supports of a finite basis,
so subsequent homogeneous map constructions use finite sums.
-/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace MagnitudeConjecture.Graded

variable (k M : Type*) [Field k] [AddCommGroup M] [Module k M]

structure VectorGrading where
  component : ℤ → Submodule k M
  internal : DirectSum.IsInternal component

namespace VectorGrading

variable {k M} (G : VectorGrading k M)

def decompose : M ≃ₗ[k] DirectSum ℤ (fun d ↦ G.component d) := by
  letI := G.internal.chooseDecomposition
  exact DirectSum.decomposeLinearEquiv G.component

def projection (d : ℤ) : M →ₗ[k] M :=
  (G.component d).subtype.comp
    ((DirectSum.component k ℤ (fun i ↦ G.component i) d).comp G.decompose.toLinearMap)

/--
@isnad1 id=mem.0h5v.s7.d0e835f782f7 from=translated src=- shape=6b4cc80d vocab=ad956268
-/
theorem projection_mem (d : ℤ) (x : M) : G.projection d x ∈ G.component d :=
  (G.decompose x d).property

/--
@isnad1 id=eq.1h5v.s7.36a9df607f02 from=translated src=- shape=43c6708c vocab=ad956268
-/
theorem projection_of_mem {d : ℤ} {x : M} (hx : x ∈ G.component d) :
    G.projection d x = x := by
  letI := G.internal.chooseDecomposition
  exact DirectSum.decompose_of_mem_same G.component hx

/--
@isnad1 id=eq.2h6v.s7.b31320dd2bb9 from=translated src=- shape=5568ad4a vocab=ad956268
-/
theorem projection_of_mem_ne {d e : ℤ} {x : M} (hx : x ∈ G.component d)
    (hde : d ≠ e) : G.projection e x = 0 := by
  letI := G.internal.chooseDecomposition
  exact DirectSum.decompose_of_mem_ne G.component hx hde

variable [FiniteDimensional k M]

/-- A finite set containing the support of every vector.-/
def degreeSupport : Finset ℤ :=
  Finset.univ.biUnion fun i ↦ (G.decompose (Module.finBasis k M i)).support

/--
@isnad1 id=eq.1h4v.s7.4d82c6610f75 from=translated src=- shape=e1295bb3 vocab=8bdf3528
-/
theorem projection_eq_zero_outside {d : ℤ} (hd : d ∉ G.degreeSupport) :
    G.projection d = 0 := by
  apply (Module.finBasis k M).ext
  intro i
  have hdi : d ∉ (G.decompose (Module.finBasis k M i)).support := by
    intro hmem
    apply hd
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩
  have hz := DFinsupp.notMem_support_iff.mp hdi
  change (G.decompose (Module.finBasis k M i) d : M) = 0
  rw [hz]
  rfl

/--
@isnad1 id=eq.1h4v.s6.8d358dd86a63 from=translated src=- shape=100cad2e vocab=d4f49189
-/
theorem component_eq_bot_outside {d : ℤ} (hd : d ∉ G.degreeSupport) :
    G.component d = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hp := G.projection_of_mem hx
  rw [G.projection_eq_zero_outside hd] at hp
  simpa using hp.symm

/-- The finite degree projections sum to the identity.
@isnad1 id=eq.0h4v.s7.d05daa88bf15 from=translated src=- shape=a63ec0fd vocab=65d2b4bf
-/
theorem sum_projection (x : M) :
    ∑ d ∈ G.degreeSupport, G.projection d x = x := by
  classical
  letI := G.internal.chooseDecomposition
  have hs : (G.decompose x).support ⊆ G.degreeSupport := by
    intro d hd
    by_contra hout
    have hz : G.decompose x d = 0 := by
      apply Subtype.ext
      change G.projection d x = 0
      rw [G.projection_eq_zero_outside hout]
      rfl
    exact (DFinsupp.mem_support_iff.mp hd) hz
  calc
    _ = ∑ d ∈ (G.decompose x).support, G.projection d x := by
      symm
      apply Finset.sum_subset hs
      intro d _ hd
      have hz := DFinsupp.notMem_support_iff.mp hd
      change (G.decompose x d : M) = 0
      rw [hz]
      rfl
    _ = x := DirectSum.sum_support_decompose G.component x

end VectorGrading

end MagnitudeConjecture.Graded
