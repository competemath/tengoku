import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms extend_id` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms extend_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms extend_on_constants` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bilinear_eq_of_standard_basis` (it only prints; the queue checks the axioms of every declaration). -/

/-! Finite-coordinate coefficient extension.
No Sym3 automorphism definition is altered and no product law is assumed. -/

noncomputable section
namespace FiniteCoordinateExtension

open scoped Matrix

universe u v
variable {k : Type u} {R : Type v} [CommSemiring k] [CommSemiring R]
variable {n : ℕ}

/-- Entrywise base change of the matrix of a linear endomorphism.-/
def extend (j : k →+* R) (A : (Fin n → k) →ₗ[k] (Fin n → k)) :
    (Fin n → R) →ₗ[R] (Fin n → R) :=
  Matrix.toLin' (j.mapMatrix (LinearMap.toMatrix' A))

theorem extend_id (j : k →+* R) :
    extend j (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k)) = LinearMap.id := by
  simp only [extend, LinearMap.toMatrix'_id, map_one, Matrix.toLin'_one]

theorem extend_comp (j : k →+* R)
    (A B : (Fin n → k) →ₗ[k] (Fin n → k)) :
    extend j (A.comp B) = (extend j A).comp (extend j B) := by
  simp only [extend, LinearMap.toMatrix'_comp, map_mul, Matrix.toLin'_mul]

/-- On coefficient images this is the original map followed by j.-/
theorem extend_on_constants (j : k →+* R)
    (A : (Fin n → k) →ₗ[k] (Fin n → k)) (x : Fin n → k) :
    extend j A (j ∘ x) = j ∘ A x := by
  funext p
  change ((LinearMap.toMatrix' A).map j *ᵥ (j ∘ x)) p = j (A x p)
  simpa only [LinearMap.toMatrix'_mulVec] using
    (RingHom.map_mulVec j (LinearMap.toMatrix' A) x p).symm

/-- A bilinear identity over the target ring is determined by the n² standard
basis pairs.  These obligations can be the mapped identities over k.-/
theorem bilinear_eq_of_standard_basis
    (B C : (Fin n → R) →ₗ[R] (Fin n → R) →ₗ[R] (Fin n → R))
    (h : ∀ i j : Fin n,
      B (Pi.single i 1) (Pi.single j 1) = C (Pi.single i 1) (Pi.single j 1)) :
    B = C := by
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  apply (Pi.basisFun R (Fin n)).ext
  intro j
  simpa only [Pi.basisFun_apply] using h i j

end FiniteCoordinateExtension
