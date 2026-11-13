/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.TensorOperators
import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Euclidean realization of the finite sparse--Fock space

The sparse--Fock space used in the paper is finite.  This file equips the
concrete matrix model from `ExternalOperators` with its genuine Euclidean
operator norm and defines the orthogonal projections onto exact total grades.
Nothing in this layer is an abstract operator interface.
-/

namespace NLAlib.SparseSketch

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d m n : ℕ}

/-- The actual Euclidean space indexed by the external coordinate and a
sparse--Fock pattern.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev FullSpace (d m n : ℕ) := EuclideanSpace ℝ (Fin d × Pattern m n)

/-- The continuous Euclidean operator represented by a concrete full matrix.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def asOperator (A : FullOp d m n) :
    FullSpace d m n →L[ℝ] FullSpace d m n :=
  (Matrix.toEuclideanCLM
    (n := Fin d × Pattern m n) (𝕜 := ℝ)) A

/-- The represented Euclidean operator acts by the concrete matrix-vector product.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h5v.s9.5077a26aa541 from=translated src=- shape=3f840a96 vocab=f5114a96
-/
@[simp] theorem asOperator_apply (A : FullOp d m n)
    (x : Fin d × Pattern m n → ℝ) :
    asOperator A (WithLp.toLp 2 x) =
      WithLp.toLp 2 (Matrix.mulVec A x) :=
  rfl

/-- In the L2-operator-norm scope, the matrix norm is definitionally the norm
of its represented Euclidean operator.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s9.3ea962b7eb18 from=translated src=- shape=1caa79e2 vocab=5372fad1
-/
theorem norm_asOperator (A : FullOp d m n) : ‖asOperator A‖ = ‖A‖ :=
  Matrix.l2_opNorm_toEuclideanCLM A

/-- The integer grade used by homogeneous matrices is the cast of the natural
occupation grade.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s4.5f82dec3680c from=translated src=- shape=55a22ace vocab=758b09e4
-/
theorem gradeZ_eq_cast_grade (p : Pattern m n) :
    Pattern.gradeZ p = (p.grade : ℤ) := by
  classical
  simp only [Pattern.gradeZ, weightZ, Pattern.grade]
  norm_cast

/-- The external-coordinate grade is the integer cast of its Fock-pattern grade.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.e30f5972e8a0 from=translated src=- shape=0c60719c vocab=79f7995a
-/
theorem fullGradeZ_eq_cast_grade (x : Fin d × Pattern m n) :
    fullGradeZ x = (x.2.grade : ℤ) :=
  gradeZ_eq_cast_grade x.2

/-- The diagonal orthogonal projection onto total grade `nu`.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def gradeProjection (nu : ℕ) : FullOp d m n :=
  Matrix.diagonal fun x ↦ if x.2.grade = nu then 1 else 0

/-- An exact-grade projection has unit diagonal precisely on the selected grade.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s7.e520ef0e5cd2 from=translated src=- shape=730d42a2 vocab=eb09ef7b
-/
@[simp] theorem gradeProjection_apply (nu : ℕ)
    (out inp : Fin d × Pattern m n) :
    gradeProjection (d := d) nu out inp =
      if out = inp ∧ out.2.grade = nu then 1 else 0 := by
  classical
  by_cases h : out = inp
  · subst inp
    by_cases hg : out.2.grade = nu <;>
      simp [gradeProjection, hg]
  · simp [gradeProjection, h]

/-- Each exact-grade projection is symmetric.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.c9c0ba0be84f from=translated src=- shape=b4a58625 vocab=a7eb1070
-/
@[simp] theorem gradeProjection_transpose (nu : ℕ) :
    (gradeProjection (d := d) (m := m) (n := n) nu).transpose =
      gradeProjection nu := by
  ext out inp
  simp only [Matrix.transpose_apply, gradeProjection_apply]
  by_cases hEq : out = inp
  · subst inp
    simp
  · have h' : inp ≠ out := Ne.symm hEq
    simp [hEq, h']

/-- Each exact-grade projection is idempotent.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s6.30edc863976f from=translated src=- shape=af293580 vocab=7b7e78ed
-/
@[simp] theorem gradeProjection_mul_self (nu : ℕ) :
    gradeProjection (d := d) (m := m) (n := n) nu * gradeProjection nu =
      gradeProjection nu := by
  classical
  rw [gradeProjection, Matrix.diagonal_mul_diagonal]
  ext out inp
  by_cases hEq : out = inp
  · subst inp
    by_cases hg : out.2.grade = nu <;> simp [hg]
  · simp [hEq]

/-- Every exact-grade projection has Euclidean operator norm at most one.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h4v.s7.7db9a091f8c1 from=translated src=- shape=6a8f25cd vocab=d90820ee
-/
theorem gradeProjection_norm_le_one (nu : ℕ) :
    ‖gradeProjection (d := d) (m := m) (n := n) nu‖ ≤ 1 := by
  rw [gradeProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro x
  by_cases h : x.2.grade = nu <;> simp [h]

/-- Projections onto distinct exact grades have zero product.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h5v.s7.da4c13d6a849 from=translated src=- shape=28c40c9a vocab=7b7e78ed
-/
@[simp] theorem gradeProjection_mul_gradeProjection
    {mu nu : ℕ} (h : mu ≠ nu) :
    gradeProjection (d := d) (m := m) (n := n) mu * gradeProjection nu = 0 := by
  classical
  rw [gradeProjection, gradeProjection, Matrix.diagonal_mul_diagonal]
  ext out inp
  by_cases hEq : out = inp
  · subst inp
    by_cases hmu : out.2.grade = mu
    · have hnu : out.2.grade ≠ nu := by
        intro hx
        exact h (hmu.symm.trans hx)
      simp [hmu, h]
    · simp [hmu]
  · simp [hEq]

/-- Multiplication by the grade projection simply keeps coordinates in the
specified grade.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s7.4b792879bf9a from=translated src=- shape=a15cc700 vocab=ca3c539b
-/
theorem gradeProjection_mulVec (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) (a : Fin d × Pattern m n) :
    Matrix.mulVec (gradeProjection (d := d) nu) x a =
      if a.2.grade = nu then x a else 0 := by
  classical
  simp [gradeProjection, Matrix.mulVec_diagonal]

/-- The squared Euclidean norm `∑ i, x i ^ 2` of a finitely indexed real vector.

This is the single sum-of-squares spelling of the sparse-sketch proof: it replaces the
former copies `LightSectorConcrete.energy`, `LightSectorConcrete.coordinateEnergy`,
`HeavyBandsConcrete.coordNormSq` and `HeavyBandsConcrete.fockNormSq`. It is an interim
definition (decision D9 of `docs/SPARSE_INTEGRATION.md`): it equals `x ⬝ᵥ x`
(`sumSq_eq_dotProduct`) and is to be replaced by that expression.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def sumSq {I : Type*} [Fintype I] (x : I → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- The finite coordinate squared energy is nonnegative.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h2v.s4.64c550372c8d from=translated src=- shape=c8b3cbfd vocab=51f202f3
-/
theorem sumSq_nonneg {I : Type*} [Fintype I] (x : I → ℝ) :
    0 ≤ sumSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The interim sum of squares is the self dot product.
Source: decision D9 of `docs/SPARSE_INTEGRATION.md`; supports `sparse-ose`.
@isnad1 id=eq.0h2v.s4.63599b07df5f from=translated src=- shape=09d07411 vocab=2015807d
-/
theorem sumSq_eq_dotProduct {I : Type*} [Fintype I] (x : I → ℝ) :
    sumSq x = dotProduct x x := by
  simp [sumSq, dotProduct, pow_two]

/-- The Euclidean norm squared equals the explicit finite coordinate energy.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h2v.s6.d2ffb219c69c from=translated src=- shape=2711de83 vocab=a355fec2
-/
theorem norm_toLp_sq {I : Type*} [Fintype I] (x : I → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = sumSq x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sumSq]

/-- Projecting to one grade retains exactly the energy in that grade.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h5v.s8.f5b7ae435a2e from=translated src=- shape=53be4900 vocab=02bcedc4
-/
theorem gradeProjection_normSq (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq (Matrix.mulVec (gradeProjection (d := d) nu) x) =
      ∑ a with a.2.grade = nu, x a ^ 2 := by
  classical
  simp only [sumSq, gradeProjection_mulVec]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a.2.grade = nu <;> simp [h]

/-- Grade projections are Euclidean contractions, stated in exact coordinate
energy form.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.c9d0ed8c06cb from=translated src=- shape=56520f40 vocab=a36af21c
-/
theorem gradeProjection_normSq_le (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq (Matrix.mulVec (gradeProjection (d := d) nu) x) ≤ sumSq x := by
  rw [gradeProjection_normSq]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun a : Fin d × Pattern m n ↦ a.2.grade = nu)
      Finset.univ) ?_
  intro a _ _
  exact sq_nonneg (x a)

/-- A coordinatewise squared-energy estimate yields the corresponding L2
operator-norm bound for the concrete finite matrix.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h4v.s6.fadaac647016 from=translated src=- shape=541d48a6 vocab=6c1785bd
-/
theorem norm_le_of_normSq_mulVec_le {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {A : Matrix I J ℝ} {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ x : J → ℝ,
      sumSq (Matrix.mulVec A x) ≤ C ^ 2 * sumSq x) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  change ‖WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp x))‖ ≤ C * ‖x‖
  have hsq := henergy (WithLp.ofLp x)
  have hout := norm_toLp_sq (Matrix.mulVec A (WithLp.ofLp x))
  have hin := norm_toLp_sq (WithLp.ofLp x)
  have hx : ‖x‖ ^ 2 = sumSq (WithLp.ofLp x) := by
    simpa using hin
  rw [← hout, ← hx] at hsq
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2
    (Matrix.mulVec A (WithLp.ofLp x)))]

/-- A concrete matrix is grade homogeneous iff every nonzero entry has the
advertised casted occupation shift.  This is a convenient natural-grade form
of `IsFullGradeShift`.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h7v.s6.1a00227eda46 from=translated src=- shape=05fcefb4 vocab=8b072208
-/
theorem homogeneous_grade_relation {delta : ℤ} {A : FullOp d m n}
    (hA : IsFullGradeShift delta A)
    {out inp : Fin d × Pattern m n} (hentry : A out inp ≠ 0) :
    (out.2.grade : ℤ) = (inp.2.grade : ℤ) + delta := by
  simpa [fullGradeZ_eq_cast_grade] using hA hentry

/-- Scalar multiplication preserves a matrix's grade shift.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=isfullgr.1h6v.s5.e8ede388e684 from=translated src=- shape=2bd2c61a vocab=29a0834d
-/
theorem homogeneous_smul {delta : ℤ} {A : FullOp d m n}
    (hA : IsFullGradeShift delta A) (c : ℝ) :
    IsFullGradeShift delta (c • A) := by
  intro out inp hentry
  have hAentry : A out inp ≠ 0 := by
    intro hz
    apply hentry
    simp [hz]
  exact hA hAentry

/-- Adding matrices with the same grade shift preserves that shift.
Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=isfullgr.2h6v.s6.a59097c2c53f from=translated src=- shape=b7839b00 vocab=d9998b60
-/
theorem homogeneous_add {delta : ℤ} {A B : FullOp d m n}
    (hA : IsFullGradeShift delta A)
    (hB : IsFullGradeShift delta B) :
    IsFullGradeShift delta (A + B) := by
  intro out inp hentry
  by_cases hAz : A out inp = 0
  · have hBn : B out inp ≠ 0 := by
      intro hBz
      exact hentry (by simp [hAz, hBz])
    exact hB hBn
  · exact hA hAz

/-- If `mu` is the grade forced from input grade `nu` by homogeneity, then
the output-grade projection can be inserted without changing the restricted
operator.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h7v.s8.e7f13e9c4315 from=translated src=- shape=0bcc02cd vocab=7d51840c
-/
theorem output_projection_of_homogeneous {delta : ℤ} {A : FullOp d m n}
    (hA : IsFullGradeShift delta A) (mu nu : ℕ)
    (hcompatible : (mu : ℤ) = (nu : ℤ) + delta) :
    gradeProjection (d := d) mu * A * gradeProjection nu =
      A * gradeProjection nu := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : A out inp = 0
    · simp [hin, hentry]
    · have hrel := homogeneous_grade_relation hA hentry
      have houtInt : (out.2.grade : ℤ) = (mu : ℤ) := by
        rw [hrel, hin, ← hcompatible]
      have hout : out.2.grade = mu := by exact_mod_cast houtInt
      simp [hin, hout]
  · simp [hin]

/-- If homogeneity would force a negative or otherwise impossible natural
output grade, the operator vanishes on the stated input grade.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h6v.s7.aca3f010b42f from=translated src=- shape=6cacb091 vocab=7d51840c
-/
theorem input_grade_vanishes_of_no_output {delta : ℤ} {A : FullOp d m n}
    (hA : IsFullGradeShift delta A) (nu : ℕ)
    (himpossible : ∀ mu : ℕ, (mu : ℤ) ≠ (nu : ℤ) + delta) :
    A * gradeProjection (d := d) nu = 0 := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hin : inp.2.grade = nu
  · by_cases hentry : A out inp = 0
    · simp [hin, hentry]
    · have hrel := homogeneous_grade_relation hA hentry
      exfalso
      exact (himpossible out.2.grade (by simpa [hin] using hrel))
  · simp [hin]

/-- Projecting a homogeneous matrix onto an incompatible output grade kills
its action on one fixed input grade.

Source: ported from `SparseFockFormal.FiniteHilbert`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h7v.s7.7a3e05f4c6cd from=translated src=- shape=d9471026 vocab=7d51840c
-/
theorem incompatible_grade_block_zero {delta : ℤ} {A : FullOp d m n}
    (hA : IsFullGradeShift delta A) (mu nu : ℕ)
    (hincompatible : (mu : ℤ) ≠ (nu : ℤ) + delta) :
    gradeProjection (d := d) mu * A * gradeProjection nu = 0 := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.zero_apply]
  by_cases hout : out.2.grade = mu
  · by_cases hin : inp.2.grade = nu
    · by_cases hentry : A out inp = 0
      · simp [hout, hin, hentry]
      · have hrel := homogeneous_grade_relation hA hentry
        exfalso
        apply hincompatible
        simpa [hout, hin] using hrel
    · simp [hout, hin]
  · simp [hout]

end

end NLAlib.SparseSketch
