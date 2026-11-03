import Tengoku.Seed.LinearAlgebra.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Inserting a zero coordinate in a dependent family of modules -/

set_option autoImplicit false
noncomputable section

namespace LinearMap

variable (R : Type*) [Semiring R] {ι : Type*} (M : ι → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Extend a family on the complement of one index by zero at that index.-/
def insertZeroCoordinate (a : ι) :
    (∀ i : {i : ι // i ≠ a}, M i.1) →ₗ[R] (∀ i, M i) := by
  classical
  exact LinearMap.pi fun i ↦
    if hi : i = a then 0 else
      LinearMap.proj (R := R) (φ := fun b : {i : ι // i ≠ a} ↦ M b.1) ⟨i, hi⟩

/--
@isnad1 id=eq.0h5v.s8.1f93a385fbd2 from=translated src=- shape=dbd7d6d2 vocab=5f752692
-/
theorem insertZeroCoordinate_self (a : ι)
    (g : ∀ i : {i : ι // i ≠ a}, M i.1) :
    insertZeroCoordinate R M a g a = 0 := by
  classical
  simp [insertZeroCoordinate]

/--
@isnad1 id=eq.0h6v.s8.84090c654cc5 from=translated src=- shape=9796061a vocab=5f752692
-/
theorem insertZeroCoordinate_other (a : ι)
    (g : ∀ i : {i : ι // i ≠ a}, M i.1) (b : {i : ι // i ≠ a}) :
    insertZeroCoordinate R M a g b.1 = g b := by
  classical
  simp [insertZeroCoordinate, b.2]

end LinearMap
