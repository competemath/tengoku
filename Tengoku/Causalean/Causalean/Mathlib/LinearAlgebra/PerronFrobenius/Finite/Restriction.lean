module
public import Tengoku.Causalean.Causalean.Mathlib.LinearAlgebra.PerronFrobenius.Finite.Basic

/-!
# Restriction and zero extension

This file supplies the coordinate bridges used for finite connected components.
It defines principal-submatrix restriction and zero extension, proves the exact
`mulVec` identities they satisfy, and relates the corresponding top Rayleigh
values.  Cross-boundary hypotheses are stated explicitly whenever an identity
for the original matrix would otherwise be false.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Mathlib.LinearAlgebra.PerronFrobenius.Finite

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The principal submatrix of [a real square matrix](hyp:A) on [a finite set of coordinates](hyp:s), called [its restricted matrix](goal), [is given by selecting those rows and columns](step:1). -/
def restrictMatrix (A : Matrix ι ι ℝ) (s : Finset ι) : Matrix s s ℝ :=
  A.submatrix Subtype.val Subtype.val

/-- The Euclidean vector obtained by restricting [a finite real vector](hyp:x) to [a finite coordinate set](hyp:s), called [its restricted vector](goal), [is given by retaining those coordinates](step:1). -/
def restrictVec (s : Finset ι) (x : EVec ι) : EVec s :=
  WithLp.toLp 2 fun i => x i.1

/-- The Euclidean vector obtained by extending [a vector on a finite coordinate subtype](hyp:x) by zero outside [that finite coordinate set](hyp:s), called [its zero extension](goal), [is given coordinate by coordinate](step:1). -/
def zeroExtendVec (s : Finset ι) (x : EVec s) : EVec ι :=
  WithLp.toLp 2 fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 0

/-- The matrix obtained by extending [a matrix on a finite coordinate subtype](hyp:B) by zero outside [that coordinate set](hyp:s), called [its zero extension](goal), [is given entry by entry](step:1). -/
def zeroExtendMatrix (s : Finset ι) (B : Matrix s s ℝ) : Matrix ι ι ℝ :=
  fun i j => if hi : i ∈ s then
    if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- A [finite coordinate set](hyp:s) and [a vector on its subtype](hyp:x) satisfy [that restricting its zero extension recovers the original subtype vector](goal).
@isnad1 id=eq.0h3v.s6.5bfcd166ed6e from=translated src=- shape=281c6946 vocab=5d9084f5
-/
@[simp] theorem restrictVec_zeroExtendVec (s : Finset ι) (x : EVec s) :
    restrictVec s (zeroExtendVec s x) = x := by
  ext i
  simp [restrictVec, zeroExtendVec]

/-- A [finite coordinate set](hyp:s) and [a vector on its subtype](hyp:x) satisfy [that zero extension preserves Euclidean norm](goal).
@isnad1 id=eq.0h3v.s7.d7fd37693778 from=translated src=- shape=1f021d68 vocab=2957ac71
-/
@[simp] theorem norm_zeroExtendVec (s : Finset ι) (x : EVec s) :
    ‖zeroExtendVec s x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : ι, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) ^ 2) =
    ∑ i : s, (x i) ^ 2
  calc
    _ = ∑ i ∈ s, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hi]
    _ = ∑ i : s, (x i) ^ 2 := by
      rw [← Finset.sum_coe_sort]
      simp

/-- A [finite coordinate set](hyp:s), [a subtype matrix](hyp:B), and [a subtype vector](hyp:x) satisfy [that applying the zero-extended matrix to the zero-extended vector equals the zero extension of the subtype action](goal).
@isnad1 id=eq.0h4v.s8.2d2b097258da from=translated src=- shape=4541e7bc vocab=7a5abbe8
-/
theorem zeroExtendMatrix_mulVec_zeroExtendVec
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec s) :
    (zeroExtendMatrix s B).mulVec (zeroExtendVec s x) =
      zeroExtendVec s (WithLp.toLp 2 (B.mulVec x)) := by
  ext i
  by_cases hi : i ∈ s
  · simp only [zeroExtendMatrix, zeroExtendVec, Matrix.mulVec, dotProduct,
      hi, dite_true]
    calc
      _ = ∑ j ∈ s, (if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0) *
          (if hj : j ∈ s then x ⟨j, hj⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp [hj]
      _ = ∑ j : s, B ⟨i, hi⟩ j * x j := by
        rw [← Finset.sum_coe_sort]
        simp
  · simp [zeroExtendMatrix, zeroExtendVec, Matrix.mulVec, dotProduct, hi]

/-- A [finite coordinate set](hyp:s), [a subtype matrix](hyp:B), and [a subtype vector](hyp:x) satisfy [that zero extension preserves their Rayleigh form](goal).
@isnad1 id=eq.0h4v.s6.5d45bce5cb22 from=translated src=- shape=84db323a vocab=d7a8d830
-/
theorem rayleighForm_zeroExtendMatrix_zeroExtendVec
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec s) :
    rayleighForm (zeroExtendMatrix s B) (zeroExtendVec s x) =
      rayleighForm B x := by
  unfold rayleighForm
  rw [zeroExtendMatrix_mulVec_zeroExtendVec]
  change (∑ i : ι, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) *
      (if hi : i ∈ s then (B.mulVec x) ⟨i, hi⟩ else 0)) =
    ∑ i : s, x i * (B.mulVec x) i
  calc
    _ = ∑ i ∈ s, (if hi : i ∈ s then x ⟨i, hi⟩ else 0) *
        (if hi : i ∈ s then (B.mulVec x) ⟨i, hi⟩ else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hi]
    _ = ∑ i : s, x i * (B.mulVec x) i := by
      rw [← Finset.sum_coe_sort]
      simp

private theorem norm_restrictVec_le (s : Finset ι) (x : EVec ι) :
    ‖restrictVec s x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : s, (x i.1) ^ 2) ≤ ∑ i : ι, (x i) ^ 2
  calc
    _ = ∑ i ∈ s, (x i) ^ 2 := Finset.sum_coe_sort s (fun i => (x i) ^ 2)
    _ ≤ ∑ i : ι, (x i) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      intro i _ _
      exact sq_nonneg (x i)

private theorem rayleighForm_smul (A : Matrix ι ι ℝ) (c : ℝ) (x : EVec ι) :
    rayleighForm A (c • x) = c ^ 2 * rayleighForm A x := by
  simp [rayleighForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
  ring_nf

private theorem zeroExtendMatrix_mulVec
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec ι) :
    (zeroExtendMatrix s B).mulVec x =
      zeroExtendVec s (WithLp.toLp 2 (B.mulVec (restrictVec s x))) := by
  ext i
  by_cases hi : i ∈ s
  · simp only [zeroExtendMatrix, zeroExtendVec, restrictVec, Matrix.mulVec,
      dotProduct, hi, dite_true]
    calc
      _ = ∑ j ∈ s, (if hj : j ∈ s then B ⟨i, hi⟩ ⟨j, hj⟩ else 0) * x j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp [hj]
      _ = ∑ j : s, B ⟨i, hi⟩ j * x j.1 := by
        rw [← Finset.sum_coe_sort]
        simp
  · simp [zeroExtendMatrix, zeroExtendVec, Matrix.mulVec, dotProduct, hi]

private theorem rayleighForm_zeroExtendMatrix
    (s : Finset ι) (B : Matrix s s ℝ) (x : EVec ι) :
    rayleighForm (zeroExtendMatrix s B) x =
      rayleighForm B (restrictVec s x) := by
  unfold rayleighForm
  rw [zeroExtendMatrix_mulVec]
  change (∑ i : ι, x i *
      (if hi : i ∈ s then (B.mulVec (restrictVec s x)) ⟨i, hi⟩ else 0)) =
    ∑ i : s, x i.1 * (B.mulVec (restrictVec s x)) i
  calc
    _ = ∑ i ∈ s, x i *
        (if hi : i ∈ s then (B.mulVec (restrictVec s x)) ⟨i, hi⟩ else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hi]
    _ = ∑ i : s, x i.1 * (B.mulVec (restrictVec s x)) i := by
      rw [← Finset.sum_coe_sort]
      simp

private theorem rayleighForm_le_sphereRayleighValue [Nonempty ι]
    (A : Matrix ι ι ℝ) (x : EVec ι) (hx : ‖x‖ = 1) :
    rayleighForm A x ≤ sphereRayleighValue A := by
  unfold sphereRayleighValue
  apply le_csSup
  · rw [show {r : ℝ | ∃ y : EVec ι, ‖y‖ = 1 ∧ r = rayleighForm A y} =
        rayleighForm A '' Metric.sphere (0 : EVec ι) 1 by
      ext r
      simp [eq_comm]]
    apply (isCompact_sphere (0 : EVec ι) 1).bddAbove_image
    unfold rayleighForm Matrix.mulVec dotProduct
    fun_prop
  · exact ⟨x, hx, rfl⟩

private theorem sphereRayleighValue_nonneg [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ sphereRayleighValue A := by
  let i : ι := Classical.choice inferInstance
  let e : EVec ι := EuclideanSpace.single i 1
  have he_norm : ‖e‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [e]
  have he_form : rayleighForm A e = A i i := by
    simp [rayleighForm, Matrix.mulVec, dotProduct, e]
  calc
    0 ≤ A i i := hA i i
    _ = rayleighForm A e := he_form.symm
    _ ≤ sphereRayleighValue A := rayleighForm_le_sphereRayleighValue A e he_norm

/-- On a nonempty finite coordinate space, [a nonempty finite coordinate set](hyp:s) and [an entrywise nonnegative subtype matrix](hyp:B,hB) satisfy [that zero extension preserves its top Rayleigh value](goal).
@isnad1 id=eq.1h3v.s7.c952ad42636d from=translated src=- shape=a2bd9634 vocab=6b669879
-/
theorem sphereRayleighValue_zeroExtendMatrix [Nonempty ι]
    (s : Finset ι) [Nonempty s] (B : Matrix s s ℝ)
    (hB : ∀ i j, 0 ≤ B i j) :
    sphereRayleighValue (zeroExtendMatrix s B) = sphereRayleighValue B := by
  apply le_antisymm
  · apply csSup_le
    · obtain ⟨x, hx⟩ : (Metric.sphere (0 : EVec ι) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr (by norm_num)
      exact ⟨rayleighForm (zeroExtendMatrix s B) x, x, by simpa using hx, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      rw [rayleighForm_zeroExtendMatrix]
      let y := restrictVec s x
      have hy_norm : ‖y‖ ≤ 1 := (norm_restrictVec_le s x).trans_eq hx
      by_cases hy : y = 0
      · change rayleighForm B y ≤ sphereRayleighValue B
        simpa [hy, rayleighForm, Matrix.mulVec, dotProduct] using
          sphereRayleighValue_nonneg B hB
      · have hy_norm_ne : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
        let u : EVec s := ‖y‖⁻¹ • y
        have hu_norm : ‖u‖ = 1 := by
          simp [u, norm_smul, hy_norm_ne]
        have hu_le : rayleighForm B u ≤ sphereRayleighValue B :=
          rayleighForm_le_sphereRayleighValue B u hu_norm
        have htop : 0 ≤ sphereRayleighValue B :=
          sphereRayleighValue_nonneg B hB
        have hy_sq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
        have hy_eq : ‖y‖ • u = y := by
          simp [u, smul_smul, hy_norm_ne]
        calc
          rayleighForm B y = rayleighForm B (‖y‖ • u) :=
            congrArg (rayleighForm B) hy_eq.symm
          _ = ‖y‖ ^ 2 * rayleighForm B u := rayleighForm_smul B ‖y‖ u
          _ ≤ ‖y‖ ^ 2 * sphereRayleighValue B :=
            mul_le_mul_of_nonneg_left hu_le (sq_nonneg _)
          _ ≤ 1 * sphereRayleighValue B :=
            mul_le_mul_of_nonneg_right hy_sq htop
          _ = sphereRayleighValue B := one_mul _
  · apply csSup_le
    · obtain ⟨x, hx⟩ : (Metric.sphere (0 : EVec s) 1).Nonempty :=
        NormedSpace.sphere_nonempty.mpr (by norm_num)
      exact ⟨rayleighForm B x, x, by simpa using hx, rfl⟩
    · rintro r ⟨x, hx, rfl⟩
      calc
        rayleighForm B x =
            rayleighForm (zeroExtendMatrix s B) (zeroExtendVec s x) :=
          (rayleighForm_zeroExtendMatrix_zeroExtendVec s B x).symm
        _ ≤ sphereRayleighValue (zeroExtendMatrix s B) :=
          rayleighForm_le_sphereRayleighValue _ _ (by simpa using hx)

/-- A [symmetric finite matrix](hyp:hA) and [a finite coordinate set](hyp:s) ensure [that the principal restricted matrix remains symmetric](goal).
@isnad1 id=issymm.1h3v.s5.42a4e4401e46 from=translated src=- shape=60273dc7 vocab=ca02de10
-/
theorem restrictMatrix_isSymm {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (s : Finset ι) :
    (restrictMatrix A s).IsSymm := by
  exact hA.submatrix Subtype.val

/-- An [entrywise nonnegative finite matrix](hyp:hA) and [a finite coordinate set](hyp:s) ensure [that the principal restricted matrix remains entrywise nonnegative](goal).
@isnad1 id=le.1h5v.s6.acc464e0b983 from=translated src=- shape=2e63423b vocab=9cffe890
-/
theorem restrictMatrix_nonneg {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (s : Finset ι) :
    ∀ i j, 0 ≤ restrictMatrix A s i j := by
  intro i j
  exact hA i.1 j.1

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [a vector](hyp:x) that [vanishes outside the set](hyp:hx) ensure [that restriction commutes with applying the matrix](goal).
@isnad1 id=eq.1h4v.s8.fe6849d6acad from=translated src=- shape=b62a9473 vocab=7e936cab
-/
theorem restrictMatrix_mulVec_restrictVec_of_zero_off
    (A : Matrix ι ι ℝ) (s : Finset ι) (x : EVec ι)
    (hx : ∀ i, i ∉ s → x i = 0) :
    (restrictMatrix A s).mulVec (restrictVec s x) =
      restrictVec s (WithLp.toLp 2 (A.mulVec x)) := by
  ext i
  change (∑ j : s, A i.1 j.1 * x j.1) = ∑ j : ι, A i.1 j * x j
  calc
    _ = ∑ j ∈ s, A i.1 j * x j := by
      simpa using Finset.sum_coe_sort s (fun j => A i.1 j * x j)
    _ = ∑ j : ι, A i.1 j * x j := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j _ hj
      simp [hx j hj]

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [block closure from outside rows into the set](hyp:hclosed) ensure [that applying the original matrix to a zero extension equals the zero extension of the restricted action](goal).
@isnad1 id=eq.1h4v.s8.5fc4f1051df7 from=translated src=- shape=ce540599 vocab=854eb166
-/
theorem mulVec_zeroExtendVec_of_closed
    (A : Matrix ι ι ℝ) (s : Finset ι)
    (hclosed : ∀ i j, i ∉ s → j ∈ s → A i j = 0)
    (x : EVec s) :
    A.mulVec (zeroExtendVec s x) =
      zeroExtendVec s (WithLp.toLp 2 ((restrictMatrix A s).mulVec x)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, zeroExtendVec, restrictMatrix,
    Matrix.submatrix_apply]
  by_cases hi : i ∈ s
  · simp only [hi, dite_true]
    calc
      _ = ∑ j ∈ s, A i j * (if hj : j ∈ s then x ⟨j, hj⟩ else 0) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp [hj]
      _ = ∑ j : s, A i j.1 * x j := by
        rw [← Finset.sum_coe_sort]
        simp
  · simp only [hi, dite_false]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s
    · simp [hj, hclosed i j hi hj]
    · simp [hj]

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), [block closure from outside rows into the set](hyp:hclosed), and [a restricted eigen-equation](hyp:x,hx) ensure [that zero extension satisfies the corresponding global eigen-equation](goal).
@isnad1 id=eq.2h5v.s8.b7c55e97c558 from=translated src=- shape=511e7548 vocab=a6d790c1
-/
theorem zeroExtendVec_eigenvector_of_closed
    (A : Matrix ι ι ℝ) (s : Finset ι)
    (hclosed : ∀ i j, i ∉ s → j ∈ s → A i j = 0)
    {x : EVec s} {ρ : ℝ}
    (hx : (restrictMatrix A s).mulVec x = ρ • x) :
    A.mulVec (zeroExtendVec s x) = ρ • zeroExtendVec s x := by
  rw [mulVec_zeroExtendVec_of_closed A s hclosed, hx]
  ext i
  by_cases hi : i ∈ s <;> simp [zeroExtendVec, hi]

/-- A [finite matrix](hyp:A), [a finite coordinate set](hyp:s), and [a vector that vanishes outside that set](hyp:x,hx) ensure [that restriction preserves its Rayleigh form](goal).
@isnad1 id=eq.1h4v.s6.403e704a5e89 from=translated src=- shape=a78bb047 vocab=08d3b4a3
-/
theorem rayleighForm_restrictVec_of_zero_off
    (A : Matrix ι ι ℝ) (s : Finset ι) (x : EVec ι)
    (hx : ∀ i, i ∉ s → x i = 0) :
    rayleighForm (restrictMatrix A s) (restrictVec s x) =
      rayleighForm A x := by
  unfold rayleighForm
  rw [restrictMatrix_mulVec_restrictVec_of_zero_off A s x hx]
  change (∑ i : s, x i.1 * (A.mulVec x) i.1) =
    ∑ i : ι, x i * (A.mulVec x) i
  calc
    _ = ∑ i ∈ s, x i * (A.mulVec x) i := by
      simpa using Finset.sum_coe_sort s (fun i => x i * (A.mulVec x) i)
    _ = ∑ i : ι, x i * (A.mulVec x) i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      simp [hx i hi]

/-- On a nonempty finite coordinate space, [a finite matrix](hyp:A) and [a nonempty finite coordinate set](hyp:s) satisfy [that the restricted top Rayleigh value is at most the global top Rayleigh value](goal).
@isnad1 id=le.0h3v.s6.070503ff39d3 from=translated src=- shape=cbdc68c4 vocab=ee44501c
-/
theorem sphereRayleighValue_restrictMatrix_le [Nonempty ι]
    (A : Matrix ι ι ℝ) (s : Finset ι) [Nonempty s] :
    sphereRayleighValue (restrictMatrix A s) ≤ sphereRayleighValue A := by
  apply csSup_le
  · obtain ⟨x, hx⟩ : (Metric.sphere (0 : EVec s) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr (by norm_num)
    exact ⟨rayleighForm (restrictMatrix A s) x, x, by simpa using hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    have hx_off : ∀ i, i ∉ s → zeroExtendVec s x i = 0 := by
      intro i hi
      simp [zeroExtendVec, hi]
    have hform :=
      rayleighForm_restrictVec_of_zero_off A s (zeroExtendVec s x) hx_off
    calc
      rayleighForm (restrictMatrix A s) x =
          rayleighForm A (zeroExtendVec s x) := by simpa using hform
      _ ≤ sphereRayleighValue A :=
        rayleighForm_le_sphereRayleighValue A (zeroExtendVec s x) (by simpa using hx)

/-- On a nonempty finite coordinate space, [a finite matrix](hyp:A), [a nonempty finite coordinate set](hyp:s), and [a global unit maximizer supported on that set](hyp:x,hx_norm,hx_support,hx_top) ensure [that the restricted and global top Rayleigh values agree](goal).
@isnad1 id=eq.3h4v.s7.4566a2b97a31 from=translated src=- shape=1c1f8f8c vocab=ae469308
-/
theorem sphereRayleighValue_restrictMatrix_eq_of_supported_maximizer
    [Nonempty ι] (A : Matrix ι ι ℝ) (s : Finset ι) [Nonempty s]
    {x : EVec ι} (hx_norm : ‖x‖ = 1)
    (hx_support : ∀ i, i ∉ s → x i = 0)
    (hx_top : rayleighForm A x = sphereRayleighValue A) :
    sphereRayleighValue (restrictMatrix A s) = sphereRayleighValue A := by
  apply le_antisymm
  · exact sphereRayleighValue_restrictMatrix_le A s
  · have hzeroExtend : zeroExtendVec s (restrictVec s x) = x := by
      ext i
      by_cases hi : i ∈ s
      · simp [zeroExtendVec, restrictVec, hi]
      · simp [zeroExtendVec, hi, hx_support i hi]
    have hrestrict_norm : ‖restrictVec s x‖ = 1 := by
      rw [← norm_zeroExtendVec s (restrictVec s x), hzeroExtend, hx_norm]
    calc
      sphereRayleighValue A = rayleighForm A x := hx_top.symm
      _ = rayleighForm (restrictMatrix A s) (restrictVec s x) :=
        (rayleighForm_restrictVec_of_zero_off A s x hx_support).symm
      _ ≤ sphereRayleighValue (restrictMatrix A s) :=
        rayleighForm_le_sphereRayleighValue _ _ hrestrict_norm

end

end Causalean.Mathlib.LinearAlgebra.PerronFrobenius.Finite
