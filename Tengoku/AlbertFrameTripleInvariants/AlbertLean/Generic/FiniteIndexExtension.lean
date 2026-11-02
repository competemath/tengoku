import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms extend_id` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms extend_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms extend_on_constants` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bilinear_eq_of_standard_basis` (it only prints; the queue checks the axioms of every declaration). -/

/-! The `FiniteCoordinateExtension` construction with an arbitrary finite
coordinate index. -/

noncomputable section
namespace FiniteIndexExtension

open scoped Matrix

universe u v w
variable {k : Type u} {R : Type v} [CommSemiring k] [CommSemiring R]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

def extend (j : k →+* R) (A : (ι → k) →ₗ[k] (ι → k)) :
    (ι → R) →ₗ[R] (ι → R) :=
  Matrix.toLin' (j.mapMatrix (LinearMap.toMatrix' A))

theorem extend_id (j : k →+* R) :
    extend j (LinearMap.id : (ι → k) →ₗ[k] (ι → k)) = LinearMap.id := by
  simp [extend]

theorem extend_comp (j : k →+* R)
    (A B : (ι → k) →ₗ[k] (ι → k)) :
    extend j (A.comp B) = (extend j A).comp (extend j B) := by
  simp only [extend, LinearMap.toMatrix'_comp, map_mul, Matrix.toLin'_mul]

theorem extend_on_constants (j : k →+* R)
    (A : (ι → k) →ₗ[k] (ι → k)) (x : ι → k) :
    extend j A (j ∘ x) = j ∘ A x := by
  funext p
  change ((LinearMap.toMatrix' A).map j *ᵥ (j ∘ x)) p = j (A x p)
  simpa only [LinearMap.toMatrix'_mulVec] using
    (RingHom.map_mulVec j (LinearMap.toMatrix' A) x p).symm

theorem bilinear_eq_of_standard_basis
    (B C : (ι → R) →ₗ[R] (ι → R) →ₗ[R] (ι → R))
    (h : ∀ i j : ι,
      B (Pi.single i 1) (Pi.single j 1) = C (Pi.single i 1) (Pi.single j 1)) :
    B = C := by
  apply (Pi.basisFun R ι).ext
  intro i
  apply (Pi.basisFun R ι).ext
  intro j
  simpa only [Pi.basisFun_apply] using h i j

end FiniteIndexExtension
