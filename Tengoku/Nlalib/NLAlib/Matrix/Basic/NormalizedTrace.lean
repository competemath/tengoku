import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.Analysis.RCLike.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized trace

The dimension-normalized trace uses the reciprocal of the dimension, with
value zero for the empty index type. Algebraic identities hold uniformly;
normalization of the identity requires a positive dimension.
-/

noncomputable section
namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- The dimension-normalized matrix trace. It is zero on empty matrices.-/
def normalizedTrace (A : Matrix n n 𝕜) : 𝕜 := (Fintype.card n : 𝕜)⁻¹ * A.trace

/-- Normalized trace is linear over the scalar field.-/
def normalizedTraceLinearMap : Matrix n n 𝕜 →ₗ[𝕜] 𝕜 :=
  (Fintype.card n : 𝕜)⁻¹ • Matrix.traceLinearMap n 𝕜 𝕜

/-- Evaluation of the normalized trace linear map.
@isnad1 id=eq.0h3v.s8.36d73dbb0578 from=translated src=- shape=c68ddb27 vocab=64826431
-/
@[simp] theorem normalizedTraceLinearMap_apply (A : Matrix n n 𝕜) :
    normalizedTraceLinearMap A = normalizedTrace A := rfl

/-- Normalized trace preserves sums.
@isnad1 id=eq.0h4v.s6.aa473f5fcddf from=translated src=- shape=b54181ab vocab=a4acd82e
-/
@[simp] theorem normalizedTrace_add (A B : Matrix n n 𝕜) :
    normalizedTrace (A+B) = normalizedTrace A + normalizedTrace B :=
  normalizedTraceLinearMap.map_add A B

/-- Normalized trace preserves scalar multiplication.
@isnad1 id=eq.0h4v.s6.5feaa18aa59b from=translated src=- shape=e3acf643 vocab=633d5ea5
-/
@[simp] theorem normalizedTrace_smul (c : 𝕜) (A : Matrix n n 𝕜) :
    normalizedTrace (c • A) = c * normalizedTrace A :=
  normalizedTraceLinearMap.map_smul c A

/-- The normalized trace of zero is zero.
@isnad1 id=eq.0h2v.s6.6b2e81481a31 from=translated src=- shape=4c0b4019 vocab=e4cd224f
-/
@[simp] theorem normalizedTrace_zero : normalizedTrace (0 : Matrix n n 𝕜) = 0 :=
  normalizedTraceLinearMap.map_zero

/-- Normalized trace preserves differences.
@isnad1 id=eq.0h4v.s6.031fe18a814f from=translated src=- shape=b54181ab vocab=080cdb91
-/
@[simp] theorem normalizedTrace_sub (A B : Matrix n n 𝕜) :
    normalizedTrace (A-B) = normalizedTrace A - normalizedTrace B :=
  normalizedTraceLinearMap.map_sub A B

/-- Normalized trace is cyclic on square matrix products.
@isnad1 id=eq.0h4v.s7.23d0f4903f52 from=translated src=- shape=3cca2006 vocab=3012c1b6
-/
theorem normalizedTrace_mul_comm (A B : Matrix n n 𝕜) :
    normalizedTrace (A*B) = normalizedTrace (B*A) := by
  simp only [normalizedTrace,Matrix.trace_mul_comm A B]

/-- The normalized trace of the identity is one in positive dimension.
@isnad1 id=eq.0h2v.s6.276b9bcfd528 from=translated src=- shape=7164259a vocab=9de5c9c1
-/
@[simp] theorem normalizedTrace_one [DecidableEq n] [Nonempty n] :
    normalizedTrace (1 : Matrix n n 𝕜) = 1 := by
  simp [normalizedTrace,Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

end NLAlib
