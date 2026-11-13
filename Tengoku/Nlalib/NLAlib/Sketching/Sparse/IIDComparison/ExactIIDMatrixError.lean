/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.IIDComparison.ExactConditionalBarycenter
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.IIDComparison.MomentTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Literal exact-s iid matrix errors

Finite iid sample transports and exact identities for the flattened corrected matrix error.
Ported from `SparseFockFormal.UniformExactSTransfer` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped InnerProductSpace Matrix

namespace NLAlib.SparseSketch.UniformSparse

noncomputable section

variable {b s n d : ℕ}

/-! ## Column-first iid presentation and exact reindexing -/

/-- The iid comparison sample, presented one whole nested column at a time.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev IidColumnSample (b s n : ℕ) := Fin n → NestedY b s

/-- Independent nested iid columns.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def iidColumnSampleLaw {b : ℕ} (hb : 0 < b) (s n : ℕ) :
    FiniteLaw (IidColumnSample b s n) :=
  FiniteLaw.independentProduct (fun _ : Fin n => nestedYLaw hb s)

/-- The iid column-sample law weight is the product of its iid column masses.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h4v.s7.788d8e18d1cf from=translated src=- shape=97aba209 vocab=7d857a47
-/
@[simp] theorem iidColumnSampleLaw_weight {b : ℕ} (hb : 0 < b)
    (s n : ℕ) (Y : IidColumnSample b s n) :
    (iidColumnSampleLaw hb s n).weight Y =
      ∏ i, (nestedYLaw hb s).weight (Y i) := rfl

/-- Reindex a column-first sample as the `(block,column)` array used by the
existing iid/Fock bridge.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def toYArray (Y : IidColumnSample b s n) : YArray b s n :=
  fun z => Y z.2 z.1

/-- Inverse reindexing from `(block,column)` arrays to whole columns.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def ofYArray (y : YArray b s n) : IidColumnSample b s n :=
  fun i g => y (g, i)

/-- Converting an iid array to column samples and back recovers the array.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s4.a8746f0e67a5 from=translated src=- shape=17a9dd6c vocab=c039c24b
-/
@[simp] theorem toYArray_ofYArray (y : YArray b s n) :
    toYArray (ofYArray y) = y := by
  funext z
  rcases z with ⟨g, i⟩
  rfl

/-- Converting column samples to an iid array and back recovers the column samples.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s4.3af55d774280 from=translated src=- shape=17a9dd6c vocab=3eb3c974
-/
@[simp] theorem ofYArray_toYArray (Y : IidColumnSample b s n) :
    ofYArray (toYArray Y) = Y := by
  funext i g
  rfl

/-- The two iid presentations are literally equivalent finite types.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def iidColumnSampleEquiv : IidColumnSample b s n ≃ YArray b s n where
  toFun := toYArray
  invFun := ofYArray
  left_inv := ofYArray_toYArray
  right_inv := toYArray_ofYArray

/-- Reindexing preserves the point mass of the iid law.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h4v.s7.e14babaa707a from=translated src=- shape=a096fe56 vocab=3264ae3b
-/
theorem iidColumnSampleLaw_weight_eq_iidArrayLaw_weight
    (hb : 0 < b) (Y : IidColumnSample b s n) :
    (iidColumnSampleLaw hb s n).weight Y =
      (iidArrayLaw hb s n).weight (toYArray Y) := by
  simp only [iidColumnSampleLaw_weight, nestedYLaw_weight,
    iidArrayLaw_weight, toYArray]
  calc
    (∏ i : Fin n, ∏ g : Fin s, (yVectorLaw b hb).weight (Y i g)) =
        ∏ g : Fin s, ∏ i : Fin n, (yVectorLaw b hb).weight (Y i g) := by
      rw [Finset.prod_comm]
    _ = ∏ z : Fin s × Fin n, (yVectorLaw b hb).weight (Y z.2 z.1) := by
      rw [Fintype.prod_prod_type]

/-- Consequently every real observable has exactly the same expectation in
the two iid presentations.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h4v.s7.48bb08659784 from=translated src=- shape=1dfcc8c7 vocab=38de8f41
-/
theorem iidColumnSampleLaw_expect_toYArray_eq_iidArrayLaw_expect
    (hb : 0 < b) (f : YArray b s n → ℝ) :
    (iidColumnSampleLaw hb s n).expect (fun Y => f (toYArray Y)) =
      (iidArrayLaw hb s n).expect f := by
  simp only [FiniteLaw.expect]
  apply Fintype.sum_equiv (iidColumnSampleEquiv (b := b) (s := s) (n := n))
  intro Y
  rw [iidColumnSampleLaw_weight_eq_iidArrayLaw_weight hb Y]
  rfl

/-! ## The iid comparison error at the fill/thin scale -/

/-- One nested iid column, flattened to its `s*b` physical coordinates.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def flatYVector (Y : NestedY b s) : EVec (s * b) :=
  WithLp.toLp 2 (fun r => flatYValue Y r)

/-- The flattened iid column multiplied by the exact fill/thin inverse
barycenter coefficient.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def exactScaledFlatYVector (hb : 0 < b) (Y : NestedY b s) : EVec (s * b) :=
  WithLp.toLp 2 (fun r => exactScale (s := s) hb * flatYValue Y r)

/-- The flattened Euclidean iid vector reads the flattened ternary coordinate value.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s6.3d2d75de7a0e from=translated src=- shape=a3a6e799 vocab=a874766d
-/
@[simp] theorem flatYVector_apply (Y : NestedY b s) (r : Fin (s * b)) :
    flatYVector Y r = flatYValue Y r := rfl

/-- The corrected flattened iid vector scales its ternary coordinate by the exact-s normalization.
Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h4v.s6.87ecc3f4110c from=translated src=- shape=7faedab0 vocab=fb53b0ed
-/
@[simp] theorem exactScaledFlatYVector_apply (hb : 0 < b)
    (Y : NestedY b s) (r : Fin (s * b)) :
    exactScaledFlatYVector hb Y r =
      exactScale (s := s) hb * flatYValue Y r := rfl

/-- The hollow iid Gram error with the genuine exact-`s` coupling scale on
each whole column.  It is expressed through the existing block-first error so
the already-proved iid/Fock bridge can be reused literally.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def exactScaledIIDError (hb : 0 < b) (F : Frame n d)
    (Y : IidColumnSample b s n) : Matrix (Fin d) (Fin d) ℝ :=
  exactScale (s := s) hb ^ 2 • iidVectorError F (toYArray Y)

/-- A flattened inner product is the sum of its block inner products.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s7.e9cd28abdc95 from=translated src=- shape=c367b324 vocab=f0222ea8
-/
theorem flatYVector_inner_eq_sum_blocks (Y Z : NestedY b s) :
    inner ℝ (flatYVector Y) (flatYVector Z) =
      ∑ g, inner ℝ (unscaledYVector (Y g)) (unscaledYVector (Z g)) := by
  simp only [PiLp.inner_apply, Real.inner_apply, flatYVector_apply,
    unscaledYVector_apply, flatYValue]
  calc
    (∑ r : Fin (s * b),
        yValue (flatOutcome Y r) * yValue (flatOutcome Z r)) =
        ∑ ga : Fin s × Fin b,
          yValue (flatOutcome Y (finProdFinEquiv ga)) *
            yValue (flatOutcome Z (finProdFinEquiv ga)) := by
      exact (finProdFinEquiv.sum_comp (fun r : Fin (s * b) =>
        yValue (flatOutcome Y r) * yValue (flatOutcome Z r))).symm
    _ = ∑ g : Fin s, ∑ a : Fin b,
          yValue (Y g a) * yValue (Z g a) := by
      rw [Fintype.sum_prod_type]
      simp only [flatOutcome_pair]

/-- Scaling both flattened columns contributes `exactScale²`.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h4v.s8.1cc96ee110d7 from=translated src=- shape=61f5aa78 vocab=c5a75dea
-/
theorem exactScaledFlatYVector_inner (hb : 0 < b)
    (Y Z : NestedY b s) :
    inner ℝ (exactScaledFlatYVector hb Y) (exactScaledFlatYVector hb Z) =
      exactScale (s := s) hb ^ 2 * inner ℝ (flatYVector Y) (flatYVector Z) := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    exactScaledFlatYVector_apply, flatYVector_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The column-first scaled error is exactly a scalar multiple of the existing
block-first iid error.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s6.da018701e94a from=translated src=- shape=8d231f9f vocab=2cc66196
-/
theorem exactScaledIIDError_eq_smul (hb : 0 < b) (F : Frame n d)
    (Y : IidColumnSample b s n) :
    exactScaledIIDError hb F Y =
      exactScale (s := s) hb ^ 2 • iidVectorError F (toYArray Y) := by
  rfl

/-- The scaled iid comparison error is real symmetric.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s5.e26fcd862ca3 from=translated src=- shape=846ca211 vocab=861bb8e4
-/
theorem exactScaledIIDError_symmetric (hb : 0 < b) (F : Frame n d)
    (Y : IidColumnSample b s n) :
    (exactScaledIIDError hb F Y).transpose = exactScaledIIDError hb F Y := by
  rw [exactScaledIIDError_eq_smul]
  ext a c
  simp only [Matrix.transpose_apply, Matrix.smul_apply]
  have h := congrFun (congrFun
    (iidVectorError_symmetric F (toYArray Y)) a) c
  simp only [Matrix.transpose_apply] at h
  rw [h]

/-- The exact hollow error, grouped into the same `s` blocks as the iid
comparison.  The following theorem proves this is only a reindexing of the
physical-row formula from `UniformExactSModel`.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def groupedExactError (F : Frame n d) (X : UniformSparseSample (s * b) s n) :
    Matrix (Fin d) (Fin d) ℝ := fun a c =>
  (1 / (s : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    (∑ g, ∑ q, UniformSparseColumn.value (X i) (finProdFinEquiv (g, q)) *
      UniformSparseColumn.value (X j) (finProdFinEquiv (g, q))) * F.u i a * F.u j c

/-- Grouping physical rows into blocks changes no matrix entry.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s5.0b55ba1e75c0 from=translated src=- shape=13547b03 vocab=86233613
-/
theorem groupedExactError_eq_hollow (F : Frame n d)
    (X : UniformSparseSample (s * b) s n) :
    groupedExactError F X = UniformSparse.hollowGram F X := by
  ext a c
  simp only [groupedExactError, UniformSparse.hollowGram]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hrows :
    (∑ g : Fin s, ∑ q : Fin b,
        UniformSparseColumn.value (X i) (finProdFinEquiv (g, q)) *
          UniformSparseColumn.value (X j) (finProdFinEquiv (g, q))) =
        ∑ z : Fin s × Fin b,
          UniformSparseColumn.value (X i) (finProdFinEquiv z) *
            UniformSparseColumn.value (X j) (finProdFinEquiv z) := by
      rw [Fintype.sum_prod_type]
  calc
    (∑ g : Fin s, ∑ q : Fin b,
        UniformSparseColumn.value (X i) (finProdFinEquiv (g, q)) *
          UniformSparseColumn.value (X j) (finProdFinEquiv (g, q))) * F.u i a * F.u j c =
        (∑ z : Fin s × Fin b,
          UniformSparseColumn.value (X i) (finProdFinEquiv z) *
            UniformSparseColumn.value (X j) (finProdFinEquiv z)) * F.u i a * F.u j c := by
      rw [hrows]
    _ = (∑ r : Fin (s * b),
          UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r) * F.u i a * F.u j
              c := by
      rw [finProdFinEquiv.sum_comp (fun r : Fin (s * b) =>
        UniformSparseColumn.value (X i) r * UniformSparseColumn.value (X j) r)]

/-- Entrywise block-grouped expansion of the scaled iid error.

Source: ported from `SparseFockFormal.UniformExactSTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h8v.s8.25cd207cba5d from=translated src=- shape=1b87add9 vocab=97c108ad
-/
theorem exactScaledIIDError_apply_grouped (hb : 0 < b) (F : Frame n d)
    (Y : IidColumnSample b s n) (a c : Fin d) :
    exactScaledIIDError hb F Y a c =
      (1 / (s : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
        (∑ g, exactScale (s := s) hb ^ 2 *
          inner ℝ (unscaledYVector (Y i g))
            (unscaledYVector (Y j g))) * F.u i a * F.u j c := by
  simp only [exactScaledIIDError, iidVectorError, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul, toYArray]
  ring_nf
  have hreorder :
      (∑ g : Fin s, ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        inner ℝ (unscaledYVector (Y i g)) (unscaledYVector (Y j g)) *
          F.u i a * F.u j c) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (∑ g : Fin s,
          inner ℝ (unscaledYVector (Y i g)) (unscaledYVector (Y j g))) *
          F.u i a * F.u j c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hreorder]
  have hfactor :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        (∑ g : Fin s, exactScale (s := s) hb ^ 2 *
            inner ℝ (unscaledYVector (Y i g)) (unscaledYVector (Y j g))) *
          F.u i a * F.u j c) =
      exactScale (s := s) hb ^ 2 *
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          (∑ g : Fin s,
            inner ℝ (unscaledYVector (Y i g)) (unscaledYVector (Y j g))) *
            F.u i a * F.u j c := by
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor]
  ring

/-! ## Independent-column disintegration -/

end

end NLAlib.SparseSketch.UniformSparse
