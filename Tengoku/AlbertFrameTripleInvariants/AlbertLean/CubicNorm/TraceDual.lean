import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms traceToDual_bijective_of_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceDualEquiv_symm_apply_apply` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Trace-dual equivalences

This file is source-independent linear algebra.  A bilinear form is represented
as a curried linear map, and nondegeneracy turns its map into the algebraic
dual into a linear equivalence in finite dimension.
-/

namespace AlbertLean.CubicNorm

open Module

section TraceDual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The map from a vector to the covector obtained by pairing on the left.-/
def traceToDual (B : V →ₗ[K] V →ₗ[K] K) : V →ₗ[K] Module.Dual K V := B

/-- Left nondegeneracy, in the exact form used by product recovery.-/
def LeftNondegenerate (B : V →ₗ[K] V →ₗ[K] K) : Prop :=
  ∀ x : V, (∀ y : V, B x y = 0) → x = 0

theorem traceToDual_injective {B : V →ₗ[K] V →ₗ[K] K}
    (hB : LeftNondegenerate B) : Function.Injective (traceToDual B) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hB (x - y)
  intro z
  have hz := DFunLike.congr_fun hxy z
  simpa [traceToDual] using sub_eq_zero.mpr hz

/-- In finite dimension a nondegenerate trace pairing identifies `V` with `V⁺`.-/
theorem traceToDual_bijective_of_nondegenerate [FiniteDimensional K V]
    {B : V →ₗ[K] V →ₗ[K] K} (hB : LeftNondegenerate B) :
    Function.Bijective (traceToDual B) := by
  have hinj := traceToDual_injective hB
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).mp hinj

/-- The trace-dual linear equivalence selected by a nondegeneracy proof.-/
noncomputable def traceDualEquiv [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : LeftNondegenerate B) :
    V ≃ₗ[K] Module.Dual K V :=
  LinearEquiv.ofBijective (traceToDual B)
    (traceToDual_bijective_of_nondegenerate hB)

@[simp] theorem traceDualEquiv_apply [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : LeftNondegenerate B) (x y : V) :
    traceDualEquiv B hB x y = B x y := rfl

@[simp] theorem traceDualEquiv_symm_apply_apply [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] K) (hB : LeftNondegenerate B)
    (f : Module.Dual K V) (y : V) :
    B ((traceDualEquiv B hB).symm f) y = f y := by
  have h := (traceDualEquiv B hB).apply_symm_apply f
  exact DFunLike.congr_fun h y

end TraceDual

end AlbertLean.CubicNorm
