import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped TensorProduct Quaternion

noncomputable section

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
variable {c₁ c₂ c₃ : R} {d₁ d₂ d₃ : S}

def Basis.ofAlgebraMapEq (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂)
    (h₃ : algebraMap R S c₃ = d₃) :
    QuaternionAlgebra.Basis (R := R) ℍ[S,d₁,d₂,d₃] c₁ c₂ c₃ where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by
    rw [← algebraMap_smul S c₁, ← algebraMap_smul S c₂, h₁, h₂]
    ext <;> simp
  j_mul_j := by
    rw [← algebraMap_smul S c₃, h₃]
    ext <;> simp
  i_mul_j := by ext <;> simp
  j_mul_i := by
    rw [← algebraMap_smul S c₂, h₂]
    ext <;> simp

variable (h₁ : algebraMap R S c₁ = d₁) (h₂ : algebraMap R S c₂ = d₂) (h₃ : algebraMap R S c₃ = d₃)

def mapOfAlgebraMapEq : ℍ[R,c₁,c₂,c₃] →ₐ[R] ℍ[S,d₁,d₂,d₃] :=
  (Basis.ofAlgebraMapEq h₁ h₂ h₃).liftHom

/--
@isnad1 id=eq.3h9v.s9.9b669cc4e62d from=translated src=- shape=18971d85 vocab=24b6e72e
-/
@[simp] theorem mapOfAlgebraMapEq_apply (x : ℍ[R,c₁,c₂,c₃]) :
    mapOfAlgebraMapEq h₁ h₂ h₃ x =
      ⟨algebraMap R S x.re, algebraMap R S x.imI, algebraMap R S x.imJ, algebraMap R S x.imK⟩ := by
  rw [mapOfAlgebraMapEq, Basis.liftHom_apply]
  unfold Basis.lift
  rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul S x.re, ← algebraMap_smul S x.imI,
    ← algebraMap_smul S x.imJ, ← algebraMap_smul S x.imK]
  ext <;> simp [Basis.ofAlgebraMapEq] <;> simp [Algebra.smul_def]

def baseChangeHom : S ⊗[R] ℍ[R,c₁,c₂,c₃] →ₐ[S] ℍ[S,d₁,d₂,d₃] :=
  Algebra.TensorProduct.lift (Algebra.ofId S ℍ[S,d₁,d₂,d₃]) (mapOfAlgebraMapEq h₁ h₂ h₃)
    (fun s _ => Algebra.commute_algebraMap_left s _)

def baseChangeInv (q : ℍ[S,d₁,d₂,d₃]) : S ⊗[R] ℍ[R,c₁,c₂,c₃] :=
  q.re ⊗ₜ[R] (1 : ℍ[R,c₁,c₂,c₃]) + q.imI ⊗ₜ[R] (⟨0, 1, 0, 0⟩ : ℍ[R,c₁,c₂,c₃]) +
    q.imJ ⊗ₜ[R] (⟨0, 0, 1, 0⟩ : ℍ[R,c₁,c₂,c₃]) + q.imK ⊗ₜ[R] (⟨0, 0, 0, 1⟩ : ℍ[R,c₁,c₂,c₃])

/--
@isnad1 id=eq.0h10v.s9.5766ba50620f from=translated src=- shape=377db6fa vocab=62dde72d
-/
theorem baseChangeInv_add (q q' : ℍ[S,d₁,d₂,d₃]) :
    (baseChangeInv (q + q') : S ⊗[R] ℍ[R,c₁,c₂,c₃]) = baseChangeInv q + baseChangeInv q' := by
  simp only [baseChangeInv]
  rw [show (q + q').re = q.re + q'.re from rfl, show (q + q').imI = q.imI + q'.imI from rfl,
    show (q + q').imJ = q.imJ + q'.imJ from rfl, show (q + q').imK = q.imK + q'.imK from rfl]
  simp only [TensorProduct.add_tmul]
  abel

end QuaternionAlgebra

end
