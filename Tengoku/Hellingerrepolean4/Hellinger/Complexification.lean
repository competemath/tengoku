import Tengoku.Hellingerrepolean4.Hellinger.ComplexSpectral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The real matrices used by the Boolean-cube construction are embedded into
the complex matrices appearing in the manuscript. The positive square root,
absolute value, and unnormalized Schatten 1 norm are all preserved. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace Hellinger.Complexification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexify : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix

/--
@isnad1 id=eq.0h4v.s6.77485649d1e5 from=translated src=- shape=5d7c9511 vocab=8ca01e67
-/
@[simp] theorem complexify_apply (A : Matrix ι ι ℝ) (i j : ι) :
    complexify A i j = (A i j : ℂ) := rfl

/--
@isnad1 id=eq.0h2v.s7.5b46d9d0b988 from=translated src=- shape=2f762912 vocab=220db039
-/
@[simp] theorem complexify_conjTranspose (A : Matrix ι ι ℝ) :
    (complexify A).conjTranspose = complexify A.transpose := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/--
@isnad1 id=ishermit.1h2v.s7.66a901e1c78a from=translated src=- shape=067423eb vocab=63cad66c
-/
theorem complexify_isHermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (complexify A).IsHermitian := by
  change (complexify A).conjTranspose = complexify A
  rw [complexify_conjTranspose]
  exact congrArg complexify (by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq)

/--
@isnad1 id=possemid.1h2v.s6.ec4d846b172d from=translated src=- shape=b9394b3f vocab=cb3cb8ad
-/
theorem complexify_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (complexify A).PosSemidef := by
  have hs : (CFC.sqrt A).transpose = CFC.sqrt A := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq
  have h := Matrix.posSemidef_conjTranspose_mul_self (complexify (CFC.sqrt A))
  rw [complexify_conjTranspose, ← map_mul, hs, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

/--
@isnad1 id=eq.1h2v.s8.d925ae22aa8d from=translated src=- shape=b8c28148 vocab=b372c9be
-/
theorem sqrt_complexify {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    CFC.sqrt (complexify A) = complexify (CFC.sqrt A) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (complexify_posSemidef (CFC.sqrt_nonneg A).posSemidef).nonneg

/--
@isnad1 id=eq.0h2v.s8.915ce2563ed3 from=translated src=- shape=03485ee7 vocab=1f7168ce
-/
theorem abs_complexify (A : Matrix ι ι ℝ) :
    CFC.abs (complexify A) = complexify (CFC.abs A) := by
  change CFC.sqrt ((complexify A).conjTranspose * complexify A) = _
  have hp : (A.transpose * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  rw [complexify_conjTranspose, ← map_mul,
    sqrt_complexify hp]
  rfl

/--
@isnad1 id=eq.0h2v.s6.c4753164bf3d from=translated src=- shape=615b3325 vocab=7680f89e
-/
theorem trace_complexify (A : Matrix ι ι ℝ) : (complexify A).trace = (A.trace : ℂ) := by
  simp [Matrix.trace, Matrix.diag, ← Complex.ofReal_sum]

/--
@isnad1 id=eq.0h2v.s6.32affe696227 from=translated src=- shape=cb9a6ac4 vocab=95afb61f
-/
theorem realTrace_complexify (A : Matrix ι ι ℝ) :
    ComplexSpectral.realTrace (complexify A) = A.trace := by
  rw [ComplexSpectral.realTrace, trace_complexify, Complex.ofReal_re]

/-- Equality of the actual complex and real Schatten 1 norms under the
canonical real-to-complex embedding, for every real square matrix.
@isnad1 id=eq.0h2v.s6.81fc03ff9730 from=translated src=- shape=911e818b vocab=3cc4ad86
-/
theorem traceNorm_complexify (A : Matrix ι ι ℝ) :
    ComplexSpectral.traceNorm (complexify A) = TraceNorm.traceNorm A := by
  rw [ComplexSpectral.traceNorm, abs_complexify, realTrace_complexify]
  rfl

/--
@isnad1 id=eq.0h3v.s8.56edef6d9a3d from=translated src=- shape=40d7cbab vocab=19e55cc7
-/
theorem traceNorm_reflection_difference (K F : Matrix ι ι ℝ) :
    ComplexSpectral.traceNorm (complexify K - complexify F * complexify K * complexify F) =
      TraceNorm.traceNorm (K - F * K * F) := by
  rw [← map_mul, ← map_mul, ← map_sub, traceNorm_complexify]

end Hellinger.Complexification
