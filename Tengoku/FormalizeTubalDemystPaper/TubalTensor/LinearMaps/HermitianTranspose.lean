import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Modules.TensorMatrix
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.StarRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/LinearMaps/HermitianTranspose.lean
  ⋆_M-Hermitian transpose.

  The ⋆_M-Hermitian transpose of a tubal matrix A ∈ K_M^{m×p} is
  defined by (A^H)ᵢⱼ = (Aⱼᵢ)*, i.e., transpose then ⋆_M-conjugate.

  Since KM n td has a StarRing instance, this is exactly Mathlib's
  `Matrix.conjTranspose` (notation `ᴴ`). All standard properties —
  `conjTranspose_apply`, `conjTranspose_mul`, `conjTranspose_conjTranspose`,
  `conjTranspose_add` — are available directly from Mathlib.
-/

namespace TubalTensor

open Matrix

variable {n : ℕ} {td : TubalData n} {m p l : ℕ}

/-! ## ⋆_M-Hermitian transpose

  The ⋆_M-Hermitian transpose is Mathlib's `conjTranspose` (notation `ᴴ`).

  Key Mathlib lemmas available for `TubalMatrix`:
  - `conjTranspose_apply A i j : Aᴴ j i = star (A i j)`
  - `conjTranspose_mul A B : (A * B)ᴴ = Bᴴ * Aᴴ`
  - `conjTranspose_conjTranspose A : Aᴴᴴ = A`
  - `conjTranspose_add A B : (A + B)ᴴ = Aᴴ + Bᴴ`
-/

/-- **Section 5.1**: The ⋆_M-Hermitian transpose of a tubal matrix.
    This is `Matrix.conjTranspose` (notation `ᴴ`), which applies the
    StarRing conjugation `star` entrywise and transposes.-/
noncomputable abbrev starMHermitianTranspose (A : TubalMatrix m p n td) : TubalMatrix p m n td :=
  Aᴴ

end TubalTensor
