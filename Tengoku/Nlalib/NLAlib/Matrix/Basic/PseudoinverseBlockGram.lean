import Tengoku.Nlalib.NLAlib.Matrix.Basic.Pseudoinverse
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Frobenius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pseudoinverse noise in an orthonormal row block

The bottom-block correction in Haar sketch-and-solve has squared Frobenius norm
equal to the inverse top-Gram trace minus its dimension. These are deterministic
identities over both real and complex scalars.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 s r q : Type*} [RCLike 𝕜] [Fintype s] [Fintype r] [Fintype q]
  [DecidableEq s] [DecidableEq r]

omit [DecidableEq s] in
/-- The full-column-rank pseudoinverse has inverse Gram as its row Gram.
@isnad1 id=eq.1h4v.s8.555fd0efe3a0 from=translated src=- shape=5b8854a5 vocab=b5760890
-/
theorem pinvL_mul_conjTranspose_eq_inv_gram (F : Matrix s r 𝕜) (hF : IsUnit (Fᴴ*F)) :
    pinvL F*(pinvL F)ᴴ=(Fᴴ*F)⁻¹ := by
  rw [pinvL_conjTranspose, pinvL, pinvR, Matrix.conjTranspose_conjTranspose]
  calc
    _ = ((Fᴴ*F)⁻¹*(Fᴴ*F))*(Fᴴ*F)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hF), Matrix.one_mul]

/-- The true lower-block noise Gram is inverse top Gram minus identity.
@isnad1 id=eq.2h6v.s9.91c5cdecaf3e from=translated src=- shape=3afed62c vocab=d7e50abf
-/
theorem pinvL_blockNoise_mul_conjTranspose (F : Matrix s r 𝕜) (H : Matrix s q 𝕜)
    (hF : IsUnit (Fᴴ*F)) (hrow : F*Fᴴ+H*Hᴴ=1) :
    (pinvL F*H)*(pinvL F*H)ᴴ=(Fᴴ*F)⁻¹-1 := by
  have hH : H*Hᴴ=1-F*Fᴴ := by rw [← hrow]; abel
  calc
    _ = (pinvL F*(H*Hᴴ))*(pinvL F)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = pinvL F*(pinvL F)ᴴ-(pinvL F*F)*(pinvL F*F)ᴴ := by
      rw [hH, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [pinvL_mul_conjTranspose_eq_inv_gram F hF, pinvL_mul hF,
        Matrix.conjTranspose_one, Matrix.one_mul]

/-- Exact deterministic scalar trace of the actual block noise.
@isnad1 id=eq.2h6v.s9.687cc2ea5da1 from=translated src=- shape=029b1e93 vocab=f010cc46
-/
theorem frobSq_pinvL_blockNoise_eq_trace_inv_sub_card (F : Matrix s r 𝕜) (H : Matrix s q 𝕜)
    (hF : IsUnit (Fᴴ*F)) (hrow : F*Fᴴ+H*Hᴴ=1) :
    frobSq (pinvL F*H)=RCLike.re ((Fᴴ*F)⁻¹).trace-Fintype.card r := by
  rw [frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.trace_mul_comm,
    pinvL_blockNoise_mul_conjTranspose F H hF hrow, Matrix.trace_sub, map_sub]
  simp

omit [Fintype s] [DecidableEq r] in
/-- Splitting a complete fixed frame inside an orthonormal sketch produces the
exact row-block identity, with no probabilistic or rank hypotheses.
@isnad1 id=eq.2h8v.s10.17f25835d74b from=translated src=- shape=fc525b7d vocab=c92df3b4
-/
theorem rowGram_sketch_blocks_eq_one {m : Type*} [Fintype m] [DecidableEq m]
    (Ω : Matrix m s 𝕜) (U : Matrix m r 𝕜) (V : Matrix m q 𝕜)
    (hΩ : HasOrthonormalCols Ω) (hcomp : U*Uᴴ+V*Vᴴ=1) :
    (Ωᴴ*U)*(Ωᴴ*U)ᴴ+(Ωᴴ*V)*(Ωᴴ*V)ᴴ=1 := by
  calc
    _ = Ωᴴ*(U*Uᴴ+V*Vᴴ)*Ω := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hcomp, Matrix.mul_one]; exact hΩ

end NLAlib
