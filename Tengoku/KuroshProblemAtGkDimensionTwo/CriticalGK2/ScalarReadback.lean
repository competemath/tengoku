import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Annihilator readback after scalar extension

The scalar extension of a subspace is represented by the range of its
tensorized inclusion. Annihilator pairings characterize membership in this
range.

The proof works for an arbitrary vector space and coefficient module, so it
implies the manuscript's finite-dimensional statement for any commutative
coefficient algebra, including coefficient algebras with zero divisors.
-/

namespace CriticalGK2

open TensorProduct

section VectorSpaces

variable {F X C : Type*} [Field F]
  [AddCommGroup X] [Module F X]
  [AddCommGroup C] [Module F C]

/-- Scalar extension of a linear functional: `x ⊗ c ↦ φ(x) • c`.-/
noncomputable def extendedPair (φ : Module.Dual F X) : X ⊗[F] C →ₗ[F] C :=
  (TensorProduct.lid F C).toLinearMap.comp (φ.rTensor C)

/--
@isnad1 id=eq.0h6v.s8.fc51b2985fe6 from=translated src=- shape=2b692dae vocab=dfe9f9b9
-/
@[simp]
theorem extendedPair_tmul (φ : Module.Dual F X) (x : X) (c : C) :
    extendedPair φ (x ⊗ₜ[F] c) = φ x • c := by
  simp [extendedPair]

/-- The image of `D ⊗ C` under the tensorized inclusion in `X ⊗ C`.-/
def scalarExtension (D : Submodule F X) : Submodule F (X ⊗[F] C) :=
  LinearMap.range (D.subtype.rTensor C)

/-- Every annihilating functional vanishes on the scalar extension.
@isnad1 id=eq.2h6v.s10.cff37c20976e from=translated src=- shape=06918388 vocab=2b424b06
-/
theorem extendedPair_eq_zero_of_mem_scalarExtension
    (D : Submodule F X) (z : X ⊗[F] C)
    (hz : z ∈ scalarExtension D) (φ : Module.Dual F X)
    (hφ : φ ∈ D.dualAnnihilator) : extendedPair φ z = 0 := by
  obtain ⟨w, rfl⟩ := hz
  have hkill : ∀ d : D, φ (d : X) = 0 := fun d =>
    (Submodule.mem_dualAnnihilator φ).mp hφ d d.property
  induction w using TensorProduct.induction_on with
  | zero => simp [extendedPair]
  | tmul d c => simp [hkill d]
  | add a b ha hb => simpa only [map_add, ha, hb, add_zero]

end VectorSpaces

section CoefficientAlgebras

variable {F X C : Type*} [Field F]
  [AddCommGroup X] [Module F X] [CommRing C] [Algebra F C]

/-- In a coefficient algebra, the extended pairing is exactly the pairing
obtained by replacing the scalar value of a functional by its image under
the structure map and multiplying by the coefficient.
@isnad1 id=eq.0h6v.s9.0e3ee7bb3ef0 from=translated src=- shape=2de74789 vocab=5602cc65
-/
@[simp]
theorem extendedPair_algebra_tmul (φ : Module.Dual F X) (x : X) (c : C) :
    extendedPair φ (x ⊗ₜ[F] c) = algebraMap F C (φ x) * c := by
  rw [extendedPair_tmul, Algebra.smul_def]

end CoefficientAlgebras

end CriticalGK2
