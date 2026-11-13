/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.IIDComparison.ConditionalBarycenter
import Tengoku.Nlalib.NLAlib.Matrix.Functions.TracePowerConvexity
import Tengoku.Nlalib.NLAlib.ForMathlib.Algebra.OffDiagonalSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independent-copy lift of the sparse--iid coupling

This file lifts the one-column martingale coupling to every `(g,i)` and proves
the off-diagonal matrix conditional-barycenter identity from TeX lines
237--250.  The restriction `i ≠ j` appears explicitly in the theorem.
-/

open scoped InnerProductSpace

namespace NLAlib.SparseSketch

noncomputable section

/-- Finite-law expectation commutes with a finite-type sum.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.ed6139c4b575 from=translated src=- shape=4a393e12 vocab=6c152d74
-/
theorem FiniteLaw.expect_sum {Omega K : Type*} [Fintype Omega] [Fintype K]
    (mu : FiniteLaw Omega) (f : K → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ k, f k omega) = ∑ k, mu.expect (f k) := by
  rw [FiniteLaw.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- Finite-law expectation commutes with a finite-set sum.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h5v.s5.4bce3b131f11 from=translated src=- shape=aff0bcc2 vocab=0eaa105e
-/
theorem FiniteLaw.expect_finset_sum {Omega K : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (S : Finset K) (f : K → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ k ∈ S, f k omega) = ∑ k ∈ S, mu.expect (f k) := by
  rw [FiniteLaw.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- A constant scalar factor may be taken outside finite-law expectation.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.e01a18c4b894 from=translated src=- shape=e399dc76 vocab=8847f0a1
-/
theorem FiniteLaw.expect_mul_const {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (f : Omega → ℝ) (c : ℝ) :
    mu.expect (fun omega ↦ f omega * c) = mu.expect f * c := by
  simp only [FiniteLaw.expect]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  ring

/-- Two distinct coordinates of a literal finite product law factorize.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h7v.s6.17130db32fd7 from=translated src=- shape=4d93df4b vocab=1c94901e
-/
theorem expect_two_coordinates
    {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (mu : I → FiniteLaw A) {i j : I} (hij : i ≠ j) (f g : A → ℝ) :
    (FiniteLaw.independentProduct mu).expect (fun x ↦ f (x i) * g (x j)) =
      (mu i).expect f * (mu j).expect g := by
  have h := FiniteLaw.expect_independentProduct_factorizes_on mu {i, j}
    (fun k a ↦ if k = i then f a else g a)
  simpa [hij, Ne.symm hij] using h

/-- An iid array site consists of its physical block and column labels.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev ArraySite (s n : ℕ) := Fin s × Fin n
/-- A selector array assigns one signed hash to every block-column site.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev XArray (b s n : ℕ) := ArraySite s n → SignedHash b
/-- An iid array assigns one ternary block vector to every block-column site.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev YArray (b s n : ℕ) := ArraySite s n → YVector b

/-- Given every sparse selector, the iid vectors are conditionally independent
with the explicit one-column conditional laws.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def conditionalArrayLaw {b s n : ℕ} (hb : 0 < b) (x : XArray b s n) :
    FiniteLaw (YArray b s n) :=
  FiniteLaw.independentProduct (fun z ↦ conditionalYLaw hb (x z))

/-- The unscaled Euclidean iid block vector uses its ternary coordinate values.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def unscaledYVector {b : ℕ} (y : YVector b) : EVec b :=
  WithLp.toLp 2 (fun a ↦ yValue (y a))

/-- The Euclidean iid block vector is scaled by the reciprocal support correction.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def scaledYVector {b : ℕ} (y : YVector b) : EVec b :=
  WithLp.toLp 2 (fun a ↦ cB b * yValue (y a))

/-- The unscaled iid block vector reads its ternary coordinate value.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s5.2d3613ef0726 from=translated src=- shape=192ef4af vocab=25be6420
-/
@[simp] theorem unscaledYVector_apply {b : ℕ} (y : YVector b) (a : Fin b) :
    unscaledYVector y a = yValue (y a) := rfl

/-- The scaled iid block vector reads its corrected ternary coordinate value.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s5.11a091c6a94d from=translated src=- shape=2e692519 vocab=bee719f1
-/
@[simp] theorem scaledYVector_apply {b : ℕ} (y : YVector b) (a : Fin b) :
    scaledYVector y a = cB b * yValue (y a) := rfl

/-- The inner product of corrected iid vectors is the squared correction times the unscaled inner product.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s7.f7dac46be770 from=translated src=- shape=471828d3 vocab=9a5b384b
-/
theorem scaled_inner_eq {b : ℕ} (y z : YVector b) :
    inner ℝ (scaledYVector y) (scaledYVector z) =
      cB b ^ 2 * inner ℝ (unscaledYVector y) (unscaledYVector z) := by
  simp only [PiLp.inner_apply, Real.inner_apply,
    scaledYVector_apply, unscaledYVector_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Conditional independence plus the one-column barycenter gives the exact
cross-inner-product identity at distinct array sites.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h6v.s7.1e4655fcb1a0 from=translated src=- shape=19c19abb vocab=75c601f1
-/
theorem conditional_cross_inner
    {b s n : ℕ} (hb : 0 < b) (x : XArray b s n)
    {z z' : ArraySite s n} (hzz : z ≠ z') :
    (conditionalArrayLaw hb x).expect
        (fun y ↦ inner ℝ (scaledYVector (y z)) (scaledYVector (y z'))) =
      inner ℝ (selectorVector (x z)) (selectorVector (x z')) := by
  unfold conditionalArrayLaw
  simp only [PiLp.inner_apply, Real.inner_apply,
    scaledYVector_apply, selectorVector]
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (FiniteLaw.independentProduct (fun q ↦ conditionalYLaw hb (x q))).expect
        (fun y ↦ (cB b * yValue (y z a)) * (cB b * yValue (y z' a))) =
        (conditionalYLaw hb (x z)).expect (fun yz ↦ cB b * yValue (yz a)) *
          (conditionalYLaw hb (x z')).expect (fun yz ↦ cB b * yValue (yz a)) :=
      expect_two_coordinates (mu := fun q ↦ conditionalYLaw hb (x q))
        (i := z) (j := z') hzz
        (fun yz : YVector b ↦ cB b * yValue (yz a))
        (fun yz : YVector b ↦ cB b * yValue (yz a))
    _ = (if a = (x z).1 then (x z).2.val else 0) *
        (if a = (x z').1 then (x z').2.val else 0) := by
      rw [conditional_barycenter_coordinate hb (x z) a,
        conditional_barycenter_coordinate hb (x z') a]

/-- The hollow sparse-selector Gram error from the coupling section, written
directly in signed-basis-vector form.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def sparseVectorError {b s n d : ℕ} (F : Frame n d) (x : XArray b s n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (s : ℝ)) •
    ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (selectorVector (x (g, i))) (selectorVector (x (g, j))) •
        Matrix.vecMulVec (WithLp.ofLp (F.u i)) (WithLp.ofLp (F.u j))

/-- The iid-vector hollow Gram error before multiplying by `c_b²`.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def iidVectorError {b s n d : ℕ} (F : Frame n d) (y : YArray b s n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (s : ℝ)) •
    ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (unscaledYVector (y (g, i))) (unscaledYVector (y (g, j))) •
        Matrix.vecMulVec (WithLp.ofLp (F.u i)) (WithLp.ofLp (F.u j))

/-- The same iid error with `c_b` placed on each of its two column vectors.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def scaledIIDVectorError {b s n d : ℕ} (F : Frame n d) (y : YArray b s n) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 / (s : ℝ)) •
    ∑ g, ∑ i, ∑ j ∈ Finset.univ.erase i,
      inner ℝ (scaledYVector (y (g, i))) (scaledYVector (y (g, j))) •
        Matrix.vecMulVec (WithLp.ofLp (F.u i)) (WithLp.ofLp (F.u j))

/-- The corrected iid Gram error is the squared scalar correction times the unscaled error.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s6.5709abaa9fe1 from=translated src=- shape=9a64edf7 vocab=dc09ff90
-/
theorem scaledIIDVectorError_eq_smul {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) :
    scaledIIDVectorError F y = cB b ^ 2 • iidVectorError F y := by
  ext a c
  simp only [scaledIIDVectorError, iidVectorError, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  simp_rw [scaled_inner_eq]
  simp_rw [Finset.mul_sum]
  ring

/-- Barycenter of a finite law in any real vector space.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def FiniteLaw.barycenter {Omega E : Type*} [Fintype Omega]
    [AddCommGroup E] [Module ℝ E]
    (mu : FiniteLaw Omega) (p : Omega → E) : E :=
  ∑ omega, mu.weight omega • p omega

/-- A matrix-valued barycenter is the entrywise finite expectation.
Source: ported from `SparseFockFormal.SparseIIDTransfer` (`matrixExpectation`),
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s5.3f17c7a2c673 from=translated src=- shape=fc3e123e vocab=089ce741
-/
theorem FiniteLaw.barycenter_apply {Omega A : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (M : Omega → Matrix A A ℝ) (a c : A) :
    FiniteLaw.barycenter mu M a c = mu.expect (fun omega ↦ M omega a c) := by
  simp [FiniteLaw.barycenter, Matrix.sum_apply, FiniteLaw.expect]

/-- Exact off-diagonal conditional transfer.  No diagonal term is present,
and the proof uses `i ≠ j` to invoke independence at two distinct sites.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s7.bf7470cbab6d from=translated src=- shape=9ef991af vocab=278f351f
-/
theorem conditional_matrix_transfer {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) :
    FiniteLaw.barycenter (conditionalArrayLaw hb x) (scaledIIDVectorError F) =
      sparseVectorError F x := by
  ext a c
  simp only [FiniteLaw.barycenter_apply, scaledIIDVectorError, sparseVectorError,
    Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [FiniteLaw.expect_smul]
  congr 1
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [FiniteLaw.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [FiniteLaw.expect_mul_const]
  rw [conditional_cross_inner hb x (hzz := by
    intro hsite
    exact (Ne.symm (Finset.mem_erase.mp hj).1) (congrArg Prod.snd hsite))]

/-- The literal selector-vector Gram error is symmetric.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s5.82e3adc1b21d from=translated src=- shape=96ec25d8 vocab=8c9a34a8
-/
theorem sparseVectorError_symmetric {b s n d : ℕ}
    (F : Frame n d) (x : XArray b s n) :
    (sparseVectorError F x).transpose = sparseVectorError F x := by
  ext a c
  simp only [Matrix.transpose_apply, sparseVectorError, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply congrArg ((1 / (s : ℝ)) * ·)
  apply Finset.sum_congr rfl
  intro g _
  rw [sum_sum_erase_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm]
  ring

/-- The literal iid-vector Gram error is symmetric.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s5.f8f06c2de93f from=translated src=- shape=96ec25d8 vocab=9e1bc210
-/
theorem iidVectorError_symmetric {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) :
    (iidVectorError F y).transpose = iidVectorError F y := by
  ext a c
  simp only [Matrix.transpose_apply, iidVectorError, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply congrArg ((1 / (s : ℝ)) * ·)
  apply Finset.sum_congr rfl
  intro g _
  rw [sum_sum_erase_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm]
  ring

/-- The corrected iid-vector Gram error is symmetric.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h6v.s5.e3e8da69c9ba from=translated src=- shape=96ec25d8 vocab=9269aeee
-/
theorem scaledIIDVectorError_symmetric {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) :
    (scaledIIDVectorError F y).transpose = scaledIIDVectorError F y := by
  rw [scaledIIDVectorError_eq_smul]
  ext a c
  simp only [Matrix.transpose_apply, Matrix.smul_apply]
  have hs := congrFun (congrFun (iidVectorError_symmetric F y) a) c
  simp only [Matrix.transpose_apply] at hs
  rw [hs]

/-- The selector-vector Gram error is bundled as a symmetric matrix.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def sparseSymmetricError {b s n d : ℕ}
    (F : Frame n d) (x : XArray b s n) : symmetricMatrices d :=
  ⟨sparseVectorError F x, sparseVectorError_symmetric F x⟩

/-- The corrected iid Gram error is bundled as a symmetric matrix.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def scaledIIDSymmetricError {b s n d : ℕ}
    (F : Frame n d) (y : YArray b s n) : symmetricMatrices d :=
  ⟨scaledIIDVectorError F y, scaledIIDVectorError_symmetric F y⟩

/-- Finite Jensen inequality for the project's explicit normalized weights.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h5v.s6.b8fc68c10742 from=translated src=- shape=78e1807f vocab=420f933e
-/
theorem FiniteLaw.map_barycenter_le_expect {Omega E : Type*} [Fintype Omega]
    [AddCommGroup E] [Module ℝ E]
    (mu : FiniteLaw Omega) (p : Omega → E) (Phi : E → ℝ)
    (hPhi : ConvexOn ℝ Set.univ Phi) :
    Phi (FiniteLaw.barycenter mu p) ≤ mu.expect (fun omega ↦ Phi (p omega)) := by
  simpa [FiniteLaw.barycenter, FiniteLaw.expect, smul_eq_mul] using
    hPhi.map_sum_le (t := Finset.univ) (w := mu.weight) (p := p)
      (fun i _ ↦ mu.weight_nonneg i) mu.sum_weight (fun _ _ ↦ Set.mem_univ _)

/-- The symmetric-matrix barycenter coerces to the matrix barycenter.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s8.79733766ee3e from=translated src=- shape=ba586de2 vocab=219915a9
-/
theorem coe_barycenter_scaledIID {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) :
    ((FiniteLaw.barycenter (conditionalArrayLaw hb x) (scaledIIDSymmetricError F) :
        symmetricMatrices d) : Matrix (Fin d) (Fin d) ℝ) =
      FiniteLaw.barycenter (conditionalArrayLaw hb x) (scaledIIDVectorError F) := by
  ext a c
  simp only [FiniteLaw.barycenter, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Matrix.sum_apply, Matrix.smul_apply,
    scaledIIDSymmetricError, smul_eq_mul]

/-- The conditional corrected iid matrix barycenter equals the literal selector-vector error.
Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h6v.s8.b8ad9ab68d17 from=translated src=- shape=15dee5ec vocab=aaa72a64
-/
theorem barycenter_scaledIID_eq_sparse {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) :
    FiniteLaw.barycenter (conditionalArrayLaw hb x) (scaledIIDSymmetricError F) =
      sparseSymmetricError F x := by
  apply Subtype.ext
  rw [coe_barycenter_scaledIID hb F x]
  exact conditional_matrix_transfer hb F x

/-- Pointwise conditional Jensen on the correct vector space of real
symmetric matrices.

Source: ported from `SparseFockFormal.SparseIIDTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h7v.s9.df0a03c2f77b from=translated src=- shape=13d2e39c vocab=b603dda3
-/
theorem conditional_convex_order {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n)
    (Phi : symmetricMatrices d → ℝ) (hPhi : ConvexOn ℝ Set.univ Phi) :
    Phi (sparseSymmetricError F x) ≤
      (conditionalArrayLaw hb x).expect
        (fun y ↦ Phi (scaledIIDSymmetricError F y)) := by
  rw [← barycenter_scaledIID_eq_sparse hb F x]
  exact FiniteLaw.map_barycenter_le_expect (conditionalArrayLaw hb x)
    (scaledIIDSymmetricError F) Phi hPhi

end

end NLAlib.SparseSketch
