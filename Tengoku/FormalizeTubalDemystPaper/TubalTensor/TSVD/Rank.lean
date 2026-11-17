import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TSVD.TSVD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/SVD/Rank.lean
  Definition 31 (⋆_M-rank), Lemma 32, Definition 36 (⋆_M-multirank).

  Definition 31 defines ⋆_M-rank as the number of nonzero singular tubes
  from the t-SVD. Lemma 32 shows this equals the maximal frontal-slice
  rank in the transform domain.
-/

namespace TubalTensor

open BigOperators Matrix Classical
open scoped ComplexOrder

variable {n : ℕ} {td : TubalData n} {m p : ℕ}

/-! ## Definition 36: ⋆_M-multirank -/

/-- **Definition 36.** The ⋆_M-multirank of a tensor A ∈ K_M^{m×p} is the
    n-tuple where the j-th entry is the rank of the j-th frontal slice
    of the transformed tensor Â.-/
noncomputable def starMMultirank (A : TubalMatrix m p n td) : Fin n → ℕ :=
  fun k => (transform A k).rank

/-- **Definition 36 (second part).** A tensor X has ⋆_M-multirank at most r
    if ⋆_M−multirank(X) ≤ r entrywise.-/
def HasStarMMultirankAtMost (A : TubalMatrix m p n td) (r : Fin n → ℕ) : Prop :=
  ∀ k, starMMultirank A k ≤ r k

/-! ## Definition 31: ⋆_M-rank -/

/-! ## Auxiliary lemmas for Lemma 32 -/

/-! ## Lemma 32: ⋆_M-rank = max frontal-slice rank -/

end TubalTensor
