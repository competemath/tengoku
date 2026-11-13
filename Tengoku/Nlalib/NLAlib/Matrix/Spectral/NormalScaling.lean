import Tengoku.Nlalib.NLAlib.Matrix.Spectral.NormalSpectral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Real scalar multiplication preserves matrix normality -/

namespace NLAlib
open scoped Matrix
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- A real multiple of a normal matrix commutes with its adjoint.
@isnad1 id=eq.1h4v.s9.37f72c1c0940 from=translated src=- shape=71c905f2 vocab=ac5d517a
-/
theorem normal_real_smul {A : Matrix n n 𝕜} (hA : A*Aᴴ=Aᴴ*A) (c : ℝ) :
    (c•A)*(c•A)ᴴ=(c•A)ᴴ*(c•A) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, hA]

end NLAlib
