import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped Quaternion

namespace QuaternionAlgebra

variable {a b : ℚ}

def qmPeriodMap (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ℍ[ℚ, a, b] →ₗ[ℤ] (Fin 2 → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => ((ι x).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1]
      map_zero' := by simp
      map_add' := fun x y => by simp [Matrix.map_add, Matrix.add_mulVec] }

/--
@isnad1 id=eq.0h5v.s9.abafe06bc969 from=translated src=- shape=a8b15ceb vocab=f90cebba
-/
@[simp]
theorem qmPeriodMap_apply (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane)
    (x : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ x = ((ι x).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1] :=
  rfl

def qmPeriodLattice (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (τ : UpperHalfPlane) : Submodule ℤ (Fin 2 → ℂ) :=
  Λ.map (qmPeriodMap ι τ)

/--
@isnad1 id=iff.0h6v.s9.0f46cb27676f from=translated src=- shape=218b9fed vocab=9f54dbcf
-/
theorem mem_qmPeriodLattice_iff (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (τ : UpperHalfPlane) (v : Fin 2 → ℂ) :
    v ∈ qmPeriodLattice ι Λ τ ↔ ∃ x ∈ Λ, qmPeriodMap ι τ x = v :=
  Submodule.mem_map

end QuaternionAlgebra

end
