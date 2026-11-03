import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.EulerSurplus
import Tengoku.Seed.Data.Matrix.Diagonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Auslander--Reiten mesh matrix

This file packages the signed incidence matrix used in the frozen manuscript.
An arrow `X ⟶ Y` contributes its negative multiplicity in row `X`, column `Y`,
while the mesh ending at a nonprojective vertex `Y` contributes `1` in row
`τ Y`, column `Y`.  The total sum of the entries is therefore the
Auslander--Reiten Euler expression `vertices - arrows + meshes`.

The construction is deliberately combinatorial.  A later categorical layer
will identify this matrix with the inverse Hom matrix.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.ARCount

universe u v w

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Sum of every entry of a finite integer matrix.-/
def matrixTotal {κ : Type v} [Fintype κ] (M : Matrix ι κ ℤ) : ℤ :=
  ∑ row, ∑ column, M row column

/-- A matrix with one unit entry in row `row`, column `column`.-/
def singletonMatrix (row column : ι) : Matrix ι ι ℤ :=
  fun i j ↦ if i = row ∧ j = column then 1 else 0

/-- The signed arrow-incidence matrix.  Its `(X,Y)` entry is the negative
multiplicity of arrows `X ⟶ Y`.-/
def arrowMatrix (arrowMultiplicity : ι → ι → ℕ) : Matrix ι ι ℤ :=
  fun source target ↦ -(arrowMultiplicity source target : ℤ)

/-- Sum of the unit matrices contributed by the almost-split meshes.-/
def meshContribution
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι) : Matrix ι ι ℤ :=
  ∑ Y, singletonMatrix (tau Y) Y.1

/-- The paper-oriented Auslander--Reiten mesh matrix

`I - (arrow multiplicities) + (mesh contributions)`.-/
def meshMatrix
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι) : Matrix ι ι ℤ :=
  1 + arrowMatrix arrowMultiplicity + meshContribution IsProjective tau

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h4v.s6.ad61cf43cce5 from=translated src=- shape=db7aabb3 vocab=39caa981
-/
theorem matrixTotal_add {κ : Type v} [Fintype κ] (M N : Matrix ι κ ℤ) :
    matrixTotal (M + N) = matrixTotal M + matrixTotal N := by
  simp only [matrixTotal, Matrix.add_apply, Finset.sum_add_distrib]

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h4v.s6.3cd67ea7b221 from=translated src=- shape=20a2a676 vocab=b325a1cd
-/
theorem matrixTotal_sum
    {κ : Type v} [Fintype κ] {σ : Type w} [Fintype σ]
    (M : σ → Matrix ι κ ℤ) :
    matrixTotal (∑ k, M k) = ∑ k, matrixTotal (M k) := by
  simp only [matrixTotal, Matrix.sum_apply]
  calc
    (∑ row, ∑ column, ∑ k, M k row column) =
        ∑ row, ∑ k, ∑ column, M k row column := by
          apply Finset.sum_congr rfl
          intro row _
          rw [Finset.sum_comm]
    _ = ∑ k, ∑ row, ∑ column, M k row column := by
      rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h3v.s4.d2c699f0bb27 from=translated src=- shape=0d7e757a vocab=e75097b1
-/
theorem matrixTotal_singletonMatrix (row column : ι) :
    matrixTotal (singletonMatrix row column) = 1 := by
  rw [matrixTotal]
  calc
    (∑ i, ∑ j, singletonMatrix row column i j) =
        ∑ i, if i = row then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i = row
          · subst i
            simp [singletonMatrix]
          · simp [singletonMatrix, hi]
    _ = 1 := by simp

/--
@isnad1 id=eq.0h1v.s5.f98e17c0f3ec from=translated src=- shape=7506545e vocab=4de77856
-/
theorem matrixTotal_one : matrixTotal (1 : Matrix ι ι ℤ) = vertexCount (ι := ι) := by
  simp [matrixTotal, Matrix.one_apply, vertexCount]

omit [DecidableEq ι] in
/--
@isnad1 id=eq.0h2v.s4.8d8bb49bf4e6 from=translated src=- shape=fe650822 vocab=09edbfe0
-/
theorem matrixTotal_arrowMatrix (arrowMultiplicity : ι → ι → ℕ) :
    matrixTotal (arrowMatrix arrowMultiplicity) = -arrowCount arrowMultiplicity := by
  simp [matrixTotal, arrowMatrix, arrowCount]

/--
@isnad1 id=eq.0h3v.s5.5ac4d62a05eb from=translated src=- shape=7a582030 vocab=387b8bcd
-/
theorem matrixTotal_meshContribution
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι) :
    matrixTotal (meshContribution IsProjective tau) = meshCount IsProjective := by
  rw [meshContribution, matrixTotal_sum]
  simp [matrixTotal_singletonMatrix, meshCount]

/--
@isnad1 id=eq.0h6v.s5.32ce5b2cfd47 from=translated src=- shape=1bca377a vocab=a0b56428
-/
theorem meshContribution_apply_of_projective
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι)
    {source target : ι} (hTarget : IsProjective target) :
    meshContribution IsProjective tau source target = 0 := by
  classical
  simp only [meshContribution, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases h : source = tau Y ∧ target = Y.1
  · exfalso
    apply Y.property
    rw [← h.2]
    exact hTarget
  · simp [singletonMatrix, h]

/--
@isnad1 id=eq.1h5v.s6.6d4a6439e9aa from=translated src=- shape=dc8cee4f vocab=16f74a57
-/
theorem meshContribution_apply_of_nonprojective
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι)
    {source target : ι} (hTarget : ¬ IsProjective target) :
    meshContribution IsProjective tau source target =
      if source = tau ⟨target, hTarget⟩ then 1 else 0 := by
  classical
  simp only [meshContribution, Matrix.sum_apply]
  rw [Finset.sum_eq_single ⟨target, hTarget⟩]
  · simp [singletonMatrix]
  · intro Y _ hY
    by_cases h : source = tau Y ∧ target = Y.1
    · exfalso
      apply hY
      apply Subtype.ext
      exact h.2.symm
    · simp [singletonMatrix, h]
  · simp

/--
@isnad1 id=eq.0h7v.s6.0ea589761c0d from=translated src=- shape=f72490f1 vocab=fcbf4b43
-/
theorem meshMatrix_apply_of_projective
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι)
    {source target : ι} (hTarget : IsProjective target) :
    meshMatrix arrowMultiplicity IsProjective tau source target =
      (if source = target then 1 else 0) - arrowMultiplicity source target := by
  rw [meshMatrix, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    arrowMatrix, meshContribution_apply_of_projective IsProjective tau hTarget]
  simp [sub_eq_add_neg]

/--
@isnad1 id=eq.1h6v.s7.0a3f611f5a4f from=translated src=- shape=14e6af09 vocab=7d93f3b8
-/
theorem meshMatrix_apply_of_nonprojective
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι)
    {source target : ι} (hTarget : ¬ IsProjective target) :
    meshMatrix arrowMultiplicity IsProjective tau source target =
      (if source = target then 1 else 0) - arrowMultiplicity source target +
        if source = tau ⟨target, hTarget⟩ then 1 else 0 := by
  rw [meshMatrix, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    arrowMatrix, meshContribution_apply_of_nonprojective IsProjective tau hTarget]
  simp [sub_eq_add_neg]

/-- Frozen manuscript, equation (2.1): the total entry sum of the mesh matrix
is the Auslander--Reiten Euler expression.
@isnad1 id=eq.0h4v.s5.6c24d02f88dd from=translated src=- shape=6d6a6971 vocab=0372e3bc
-/
theorem matrixTotal_meshMatrix_eq_eulerMagnitude
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (tau : {Y : ι // ¬ IsProjective Y} → ι) :
    matrixTotal (meshMatrix arrowMultiplicity IsProjective tau) =
      eulerMagnitude arrowMultiplicity IsProjective := by
  rw [meshMatrix, matrixTotal_add, matrixTotal_add, matrixTotal_one,
    matrixTotal_arrowMatrix, matrixTotal_meshContribution]
  simp [eulerMagnitude, sub_eq_add_neg]

end MagnitudeConjecture.ARCount
