/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.VacuumMoment
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.Bands.GlobalBands
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.FockSpace
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact passage from the iid multiplication operator to concrete grade bands

This module closes the algebraic seam between the product-probability
realization in `VacuumMoment` and the physical, distinct-site bands in
`GlobalBands`.  In particular, the global operator in the vacuum moment is
literally the normalized sum of the three concrete bands.
-/

namespace NLAlib.SparseSketch

noncomputable section

variable {m n d b : ℕ}

/-- Kernels lifted at two distinct sites multiply to the simultaneous
two-site kernel.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s6.a675c61c5fec from=translated src=- shape=a6115260 vocab=089d52f5
-/
theorem siteKernel_mul_siteKernel_of_ne
    (s t : Site m n) (hst : s ≠ t) (A B : LevelOp) :
    siteKernel s A * siteKernel t B = pairKernel s t A B := by
  classical
  ext out inp
  by_cases hoff : agreesOutsidePair s t out inp
  · let mid : Pattern m n := Function.update out s (inp s)
    rw [Matrix.mul_apply, Finset.sum_eq_single mid]
    · have hs : agreesOutsideSite s out mid := by
        intro x hxs
        simp [mid, hxs]
      have ht : agreesOutsideSite t mid inp := by
        intro x hxt
        by_cases hxs : x = s
        · subst x
          simp [mid]
        · simp [mid, hxs, hoff x hxs hxt]
      have hmids : mid s = inp s := by simp [mid]
      have hmidt : mid t = out t := by
        simp [mid, Ne.symm hst]
      simp [siteKernel, pairKernel, hoff, hs, ht, hmids, hmidt]
    · intro other _ hother
      by_cases hs : agreesOutsideSite s out other
      · by_cases ht : agreesOutsideSite t other inp
        · have heq : other = mid := by
            funext x
            by_cases hxs : x = s
            · subst x
              have hst' : s ≠ t := hst
              simpa [mid] using ht s hst'
            · have hx := hs x hxs
              simpa [mid, hxs] using hx.symm
          exact (hother heq).elim
        · simp [siteKernel, ht]
      · simp [siteKernel, hs]
    · intro hnot
      exact (hnot (Finset.mem_univ mid)).elim
  · rw [Matrix.mul_apply]
    simp only [pairKernel, hoff, ite_false]
    apply (Finset.sum_eq_zero fun mid _ ↦ ?_)
    by_cases hs : agreesOutsideSite s out mid
    · by_cases ht : agreesOutsideSite t mid inp
      · exfalso
        apply hoff
        intro x hxs hxt
        exact (hs x hxs).trans (ht x hxt)
      · simp [siteKernel, ht]
    · simp [siteKernel, hs]

/-- At distinct columns in one row, the product appearing in the product-L2
model is exactly the physical pair kernel used by the band inventory.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s7.94983d0fc459 from=translated src=- shape=d2167687 vocab=2d905d15
-/
theorem siteJacobiProduct_eq_pairKernel
    (r : Fin m) (i j : Fin n) (hij : i ≠ j) (ρ : ℝ) :
    siteKernel (r, i) (jacobi ρ) * siteKernel (r, j) (jacobi ρ) =
      pairKernel (r, i) (r, j) (jacobi ρ) (jacobi ρ) := by
  apply siteKernel_mul_siteKernel_of_ne
  intro h
  exact hij (congrArg Prod.snd h)

/-- The global Jacobi operator from the exact vacuum moment is the normalized
physical multiplication matrix from `GlobalBands`.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h5v.s7.4a8d76f37275 from=translated src=- shape=f1c144cf vocab=7c38a1e0
-/
theorem globalJacobiOperator_eq_smul_rawMultiplication
    (F : Frame n d) :
    globalJacobiOperator (m := m) b F =
      (1 / (m : ℝ)) • rawMultiplication m (fun i a ↦ F.u i a)
        (Real.sqrt ((b : ℝ) - 1)) := by
  classical
  simp only [globalJacobiOperator]
  unfold rawMultiplication orderedJacobiTerm
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
  rw [siteJacobiProduct_eq_pairKernel r i j hij]

/-- One normalized concrete grade band.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def normalizedBand (m : ℕ) (F : Frame n d) (b : ℕ)
    (δ : Shift) : FullOp d m n :=
  (1 / (m : ℝ)) •
    band m (fun i a ↦ F.u i a)
      (Real.sqrt ((b : ℝ) - 1)) δ

/-- The normalized physical band retains its advertised grade shift.
Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=isfullgr.0h6v.s4.cbc0732d92f8 from=translated src=- shape=375f5d9a vocab=c5ff6139
-/
theorem normalizedBand_homogeneous (F : Frame n d) (b : ℕ)
    (δ : Shift) :
  IsFullGradeShift δ.degree (normalizedBand m F b δ) := by
  apply homogeneous_smul
  exact band_homogeneous
    (m := m) (fun i a ↦ F.u i a) (Real.sqrt ((b : ℝ) - 1)) δ

/-- The all-zero vacuum pattern has occupation grade zero.
Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h2v.s4.516c2e4115bc from=translated src=- shape=515d1a8c vocab=a2057d64
-/
@[simp] theorem vacuumPattern_grade :
    (vacuumPattern m n).grade = 0 := by
  classical
  simp [vacuumPattern, Pattern.grade, Level.weight]

/-- Natural output grade of one band, with `none` for an impossible downward
step from grade zero or one.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def nextGrade : Shift → ℕ → Option ℕ
  | .plus, nu => some (nu + 2)
  | .zero, nu => some nu
  | .minus, nu => if 2 ≤ nu then some (nu - 2) else none

/-- A successful next-grade computation has the band's integer grade change.
Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h3v.s5.f71afa328768 from=translated src=- shape=af4509ef vocab=b45ab189
-/
theorem nextGrade_compatible {delta : Shift} {nu mu : ℕ}
    (hnext : nextGrade delta nu = some mu) :
    (mu : ℤ) = (nu : ℤ) + delta.degree := by
  cases delta with
  | plus =>
      simp [nextGrade] at hnext
      subst mu
      simp [Shift.degree]
  | zero =>
      simp [nextGrade] at hnext
      subst mu
      simp [Shift.degree]
  | minus =>
      simp only [nextGrade] at hnext
      split at hnext
      case isTrue htwo =>
        simp only [Option.some.injEq] at hnext
        subst mu
        simp [Shift.degree]
        omega
      case isFalse htwo => simp at hnext

/-- A failed next-grade computation admits no compatible natural output grade.
Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=ne.1h3v.s5.b66f4fcc8eb8 from=translated src=- shape=3ec11045 vocab=e8b3ff1f
-/
theorem nextGrade_none_impossible {delta : Shift} {nu : ℕ}
    (hnext : nextGrade delta nu = none) :
    ∀ mu : ℕ, (mu : ℤ) ≠ (nu : ℤ) + delta.degree := by
  cases delta with
  | plus => simp [nextGrade] at hnext
  | zero => simp [nextGrade] at hnext
  | minus =>
      simp only [nextGrade] at hnext
      split at hnext
      case isTrue htwo => simp at hnext
      case isFalse htwo =>
        intro mu hmu
        simp [Shift.degree] at hmu
        omega

/-- Exact projection insertion for one concrete band step.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h8v.s8.f5833600c8c5 from=translated src=- shape=f262edab vocab=861444f4
-/
theorem normalizedBand_output_projection
    (F : Frame n d) (b : ℕ) (delta : Shift)
    (nu mu : ℕ) (hnext : nextGrade delta nu = some mu) :
    gradeProjection (d := d) mu * normalizedBand m F b delta *
        gradeProjection nu =
      normalizedBand m F b delta * gradeProjection nu := by
  apply output_projection_of_homogeneous
    (normalizedBand_homogeneous F b delta)
  exact nextGrade_compatible hnext

/-- An impossible downward band vanishes on the input grade.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h7v.s7.402668e32022 from=translated src=- shape=1626a931 vocab=5a3dbf79
-/
theorem normalizedBand_vanishes_of_nextGrade_none
    (F : Frame n d) (b : ℕ) (delta : Shift)
    (nu : ℕ) (hnext : nextGrade delta nu = none) :
    normalizedBand m F b delta * gradeProjection (d := d) nu = 0 := by
  apply input_grade_vanishes_of_no_output
    (normalizedBand_homogeneous F b delta) nu
  exact nextGrade_none_impossible hnext

/-- The multiplication operator in the exact iid vacuum moment is literally
the sum of its three normalized physical grade bands.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h5v.s6.8bc04ce2ba30 from=translated src=- shape=9b66c32c vocab=ac94ff5e
-/
theorem multiplicationOperator_eq_sum_normalizedBands
    (hb : 1 < b) (F : Frame n d) :
    multiplicationOperator (m := m) b hb F =
      ∑ δ : Shift, normalizedBand m F b δ := by
  rw [multiplicationOperator_eq_globalJacobi hb F,
    globalJacobiOperator_eq_smul_rawMultiplication]
  rw [rawMultiplication_eq_sum_bands]
  simp [normalizedBand, Finset.smul_sum]

/-- Exact vacuum identity with the concrete three-band sum substituted.

Source: ported from `SparseFockFormal.ConcreteLadder`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s8.90b94801ecf3 from=translated src=- shape=e67a453b vocab=62689256
-/
theorem vacuum_moment_identity_bands
    (hb : 1 < b) (F : Frame n d) (k : ℕ) :
    (∑ a : Fin d,
      ((∑ δ : Shift, normalizedBand m F b δ) ^ k)
        (a, vacuumPattern m n) (a, vacuumPattern m n)) =
      (iidLaw b hb m n).expect
        (fun omega ↦ Matrix.trace ((iidGramError b F omega) ^ k)) := by
  rw [← multiplicationOperator_eq_sum_normalizedBands hb F]
  exact vacuum_moment_identity hb F k

end

end NLAlib.SparseSketch
