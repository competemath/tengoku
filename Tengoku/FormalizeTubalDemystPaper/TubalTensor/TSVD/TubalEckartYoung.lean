import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TSVD.Rank
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Prerequisites.EckartYoung
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TSVD.HilbertAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/TSVD/TubalEckartYoung.lean
  Lemma 33, Corollary 34, Theorem 35, Theorem 37.

  Eckart-Young-like results for tubal tensors.
  These require M = cW (scaled unitary) as a hypothesis.
-/

namespace TubalTensor

open BigOperators Matrix Complex Classical

variable {n : ℕ} {td : TubalData n} {m p l : ℕ}

/-! ## Frobenius norm squared -/

/-- Squared Frobenius norm for a tubal matrix: ∑ᵢⱼₖ (A i j k)².-/
noncomputable def tubalFrobNormSq (A : TubalMatrix m p n td) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, (KM.toFun (A i j) k) ^ 2

/-! ## IsScaledUnitary: M = cW for some nonzero scalar c and unitary W -/

/-- M is a scaled unitary: M = c • W for some nonzero c ∈ ℂ and unitary W.-/
def IsScaledUnitary (td : TubalData n) : Prop :=
  ∃ (c : ℂ) (W : Matrix (Fin n) (Fin n) ℂ), c ≠ 0 ∧ IsUnitary W ∧ td.M = c • W

/-! ## Parseval: unitary preserves ∑ normSq for vectors -/

/-- Parseval's identity: unitary matrices preserve ∑ normSq of vectors.-/
theorem sum_normSq_unitary_mulVec {n' : ℕ}
    (W : Matrix (Fin n') (Fin n') ℂ) (hW : IsUnitary W) (v : Fin n' → ℂ) :
    ∑ k, Complex.normSq ((W.mulVec v) k) = ∑ k, Complex.normSq (v k) := by
  -- We prove this via the trace approach: view v as a 1-column matrix.
  -- frobNormSq of a single-column matrix = ∑ᵢ normSq(vᵢ)
  -- W * (single-column) = single-column of W.mulVec v
  -- Then use frobNormSq_unitary_mul_left.
  -- Define a column matrix as fun i (_ : Fin 1) => v i
  set A : Matrix (Fin n') (Fin 1) ℂ := fun i _ => v i
  have hA : frobNormSq A = ∑ i, Complex.normSq (v i) := by
    unfold frobNormSq; congr 1; funext i
    exact Fin.sum_univ_one _
  have hWA : W * A = fun i (_ : Fin 1) => (W.mulVec v) i := by
    ext i j
    simp only [Matrix.mul_apply, mulVec, dotProduct]
    rfl
  have hWA_frob : frobNormSq (W * A) = ∑ i, Complex.normSq ((W.mulVec v) i) := by
    unfold frobNormSq; rw [hWA]; congr 1; funext i
    exact Fin.sum_univ_one _
  rw [← hWA_frob, frobNormSq_unitary_mul_left W A hW, hA]

/-! ## Key identity: normSq(c) * tubalFrobNormSq = ∑ₖ frobNormSq(Â_k) -/

/-! ## Transform slices of ⋆_M-unitary are unitary -/

/-- If U is ⋆_M-unitary, each transform slice is unitary.-/
theorem transform_slice_unitary_of_starMUnitary
    (U : TubalMatrix m m n td) (hU : IsStarMUnitary U) (k : Fin n) :
    IsUnitary (transform U k) := by
  show (transform U k)ᴴ * transform U k = 1
  have h1 : transform (Uᴴ * U) = fun k => (transform U k)ᴴ * transform U k := by
    have hfact := (transform_eq_facewise_iff Uᴴ U (Uᴴ * U)).mp rfl
    funext k'; have := congr_fun hfact k'
    simp only [facewise_apply] at this
    rw [this, congr_fun (transform_conjTranspose U) k']
  rw [← congr_fun h1 k, hU.conjTranspose_mul_self, congr_fun transform_one k]

/-! ## Lemma 33: ⋆_M-unitary tensors are Frobenius isometries -/

/-! ## Corollary 34: ‖A‖²_F from singular tubes -/

/-- Frobenius norm squared of a single tube: ∑ₖ (a k)².-/
noncomputable def tubeFrobNormSq {n : ℕ} {td : TubalData n} (a : KM n td) : ℝ :=
  ∑ k : Fin n, (KM.toFun a k) ^ 2

/-! ## Transform linearity helpers -/

/-! ## IsSVDDiagC → IsSVDDiag bridge -/

/-- Extract a real SVD-diagonal matrix from a complex one.-/
private noncomputable def realOfSVDDiagC {m' p' : ℕ}
    (S : Matrix (Fin m') (Fin p') ℂ) : Matrix (Fin m') (Fin p') ℝ :=
  fun i j => (S i j).re

/-! ## Tubal truncation and Theorem 35 -/

/-- Truncate an f-diagonal tubal matrix at rank k: zero out singular tubes past index k.-/
noncomputable def tubalTrunc (S : TubalMatrix m p n td)
    (_hS : IsFDiagonal S) (k : ℕ) : TubalMatrix m p n td :=
  fun i j => if (i : ℕ) < k ∧ (i : ℕ) = (j : ℕ) then S i j else 0

/-- The rank-k truncated t-SVD approximation.-/
noncomputable def tsvdTruncApprox {A : TubalMatrix m p n td}
    (svd : TSVD A) (k : ℕ) : TubalMatrix m p n td :=
  svd.U * tubalTrunc svd.S svd.hS_fdiag k * svd.Vᴴ

/-! ## Theorem 37 (Eckart-Young, multirank version) -/

/-- A multirank tuple r respects the conjugate-pair structure of M:
    conjugate-paired rows must have the same truncation level.
    This is necessary for the per-slice truncation to produce a valid
    real tubal matrix (the invTransform round-trip requires paired structure).-/
def RespectsConjPairing (td : TubalData n) (r : Fin n → ℕ) : Prop :=
  ∀ k k', k ≠ k' → IsConjRow td.M k k' → r k = r k'

/-- Truncate an f-diagonal tubal matrix with per-slice truncation levels r.
    At transform-domain slice k, keep the first r(k) diagonal entries and zero the rest.
    Defined via invTransform of the per-slice truncated slices.
    Requires r to respect the conjugate-pair structure of M so that the
    per-slice truncation preserves paired structure and invTransform round-trips.-/
noncomputable def tubalTruncMulti (S : TubalMatrix m p n td)
    (_hS : IsFDiagonal S) (r : Fin n → ℕ) (_hr : RespectsConjPairing td r) :
    TubalMatrix m p n td :=
  invTransform (fun k i j =>
    if (i : ℕ) < r k ∧ (i : ℕ) = (j : ℕ) then transform S k i j else 0)

/-- The multirank-r truncated t-SVD approximation.
    Requires r to respect the conjugate-pair structure of M.-/
noncomputable def tsvdTruncMulti {A : TubalMatrix m p n td}
    (svd : TSVD A) (r : Fin n → ℕ) (hr : RespectsConjPairing td r) :
    TubalMatrix m p n td :=
  svd.U * tubalTruncMulti svd.S svd.hS_fdiag r hr * svd.Vᴴ

/-! ## Generalized Eckart-Young (Theorem 3.2 / Lemma 3.3): M = DW (row-scaled unitary) -/

end TubalTensor
