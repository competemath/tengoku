import Tengoku.Seed.Algebra.Algebra.Bilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sequence multiplication operators

Pointwise multiplication of sequences as a linear map into linear endomorphisms.
-/

namespace AlternatingAnalytic

variable (L : Type*) [Field L]

/-- Send a sequence to the linear operator given by pointwise multiplication by it.-/
def sequenceMultiplier : (ℕ → L) →ₗ[L] Module.End L (ℕ → L) :=
  LinearMap.mul L (ℕ → L)

/--
@isnad1 id=eq.0h4v.s10.43707995bcb2 from=translated src=- shape=01193956 vocab=503ab118
-/
@[simp]
theorem sequenceMultiplier_apply (a x : ℕ → L) (n : ℕ) :
    sequenceMultiplier L a x n = a n * x n :=
  rfl

end AlternatingAnalytic
