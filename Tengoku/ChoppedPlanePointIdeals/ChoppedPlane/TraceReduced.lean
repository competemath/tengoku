module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Nondegenerate trace forms certify reduced finite algebras

A nilpotent element pairs to zero with every element under the algebra trace
form. Thus a nondegenerate trace form rules out nonzero nilpotents. For a finite
product of copies of the base field, the standard trace matrix is the identity.
-/

noncomputable section
namespace ChoppedPlane
open Module

variable {K A J : Type*} [Field K] [CommRing A] [Algebra K A]

/-- A nilpotent element lies in the left radical of the algebra trace form.
@isnad1 id=eq.1h4v.s9.4ff8d4686d7b from=translated src=- shape=23069faa vocab=b5cfa9ea
-/
theorem traceForm_eq_zero_of_nilpotent {x : A} (hx : IsNilpotent x) (y : A) :
    Algebra.traceForm K A x y = 0 := by
  rw [Algebra.traceForm_apply]
  exact (Algebra.isNilpotent_trace_of_isNilpotent
    ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- Nondegeneracy of the trace form implies that the algebra is reduced.
@isnad1 id=isreduce.1h2v.s6.8bac1ca13951 from=translated src=- shape=9868579c vocab=b98a6ff7
-/
theorem isReduced_of_traceForm_nondegenerate
    (h : (Algebra.traceForm K A).Nondegenerate) : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  exact h.1 x (fun y => traceForm_eq_zero_of_nilpotent hx y)

/-- A nonzero determinant of the trace matrix certifies reducedness.
@isnad1 id=isreduce.1h4v.s11.8dea77767eff from=translated src=- shape=2f9c8318 vocab=006bc4e2
-/
theorem isReduced_of_traceForm_det_ne_zero [Fintype J] [DecidableEq J]
    (b : Basis J K A)
    (h : ((Algebra.traceForm K A).toMatrix b).det ≠ 0) : IsReduced A :=
  isReduced_of_traceForm_nondegenerate
    (LinearMap.BilinForm.nondegenerate_of_det_ne_zero (Algebra.traceForm K A) b h)

/-- Trace in a finite product of the base field is the sum of its coordinates.
@isnad1 id=eq.0h3v.s8.89e943e31c8d from=translated src=- shape=24fea275 vocab=d71612d0
-/
theorem algebra_trace_pi [Fintype J] (x : J → K) :
    Algebra.trace K (J → K) x = ∑ j, x j := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  change Algebra.leftMulMatrix (Pi.basisFun K J) x j j = x j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr]
  simp [Pi.basisFun_apply]

/-- The trace form of a finite product is the usual coordinate pairing.
@isnad1 id=eq.0h4v.s10.d5d23af2430c from=translated src=- shape=1e1a60cf vocab=9ff46caf
-/
theorem algebra_traceForm_pi [Fintype J] (x y : J → K) :
    Algebra.traceForm K (J → K) x y = ∑ j, x j * y j := by
  rw [Algebra.traceForm_apply, algebra_trace_pi]
  rfl

/-- The standard basis has identity trace matrix over every base field.
@isnad1 id=eq.0h2v.s11.62cb5b1b8187 from=translated src=- shape=8f3ad232 vocab=17ec61e0
-/
theorem algebra_traceForm_pi_matrix [Fintype J] [DecidableEq J] :
    (Algebra.traceForm K (J → K)).toMatrix (Pi.basisFun K J) = 1 := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, algebra_traceForm_pi]
  simp [Pi.basisFun_apply, Pi.single_apply, mul_ite, Matrix.one_apply, eq_comm]

/-- A finite product of the base field has nondegenerate algebra trace form.
@isnad1 id=nondegen.0h2v.s7.b328675ebc32 from=translated src=- shape=3bf33cb6 vocab=7c4224a3
-/
theorem algebra_traceForm_pi_nondegenerate [Fintype J] :
    (Algebra.traceForm K (J → K)).Nondegenerate := by
  classical
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero
    (Algebra.traceForm K (J → K)) (Pi.basisFun K J)
  rw [algebra_traceForm_pi_matrix, Matrix.det_one]
  exact one_ne_zero

/-- Algebra equivalences preserve the trace pairing.
@isnad1 id=eq.0h6v.s10.4ddfb8e357ab from=translated src=- shape=5d331194 vocab=e96b2f20
-/
theorem algebra_traceForm_equiv {A' : Type*} [CommRing A'] [Algebra K A']
    (e : A ≃ₐ[K] A') (x y : A) :
    Algebra.traceForm K A' (e x) (e y) = Algebra.traceForm K A x y := by
  rw [Algebra.traceForm_apply, ← map_mul, Algebra.trace_eq_of_algEquiv,
    Algebra.traceForm_apply]

/-- Nondegeneracy of the trace form is preserved by an algebra equivalence.
@isnad1 id=nondegen.1h4v.s7.2be39d4d4041 from=translated src=- shape=a7c5a766 vocab=2a69310c
-/
theorem traceForm_nondegenerate_of_algEquiv {A' : Type*} [CommRing A'] [Algebra K A']
    (e : A ≃ₐ[K] A') (h : (Algebra.traceForm K A').Nondegenerate) :
    (Algebra.traceForm K A).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply h.1 (e x)
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [algebra_traceForm_equiv]
    exact hx z
  · intro y hy
    apply e.injective
    rw [map_zero]
    apply h.2 (e y)
    intro x
    obtain ⟨z, rfl⟩ := e.surjective x
    rw [algebra_traceForm_equiv]
    exact hy z

/-- An algebra split as a finite product of the base field has nondegenerate
trace form in every characteristic.
@isnad1 id=nondegen.0h4v.s6.e8d512c04244 from=translated src=- shape=6958530c vocab=b1d140d9
-/
theorem traceForm_nondegenerate_of_split [Fintype J] (e : A ≃ₐ[K] (J → K)) :
    (Algebra.traceForm K A).Nondegenerate :=
  traceForm_nondegenerate_of_algEquiv e algebra_traceForm_pi_nondegenerate

end ChoppedPlane
