import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Data.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/TransformDomain/FacewiseProduct.lean
  Facewise product △ (Section 6).

  The frontal facewise product of two tensors (viewed as arrays of
  frontal slices): (A △ B)_k := A_k * B_k (matrix product on each
  frontal slice independently).
-/

namespace TubalTensor

open Matrix

variable {n : ℕ} {m p l : ℕ}

/-! ## Facewise product (Section 6) -/

/-- Facewise product of two arrays of frontal slices.
    `(A △ B) k := A k * B k` (ordinary matrix product on each slice).-/
noncomputable def facewise
    (A : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (B : Fin n → Matrix (Fin p) (Fin l) ℂ) :
    Fin n → Matrix (Fin m) (Fin l) ℂ :=
  fun k => A k * B k

scoped notation:70 A " △ " B => facewise A B

/--
@isnad1 id=eq.0h7v.s6.79e3fd3e5d9c from=translated src=- shape=60aec030 vocab=93b4956d
-/
@[simp]
theorem facewise_apply
    (A : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (B : Fin n → Matrix (Fin p) (Fin l) ℂ) (k : Fin n) :
    (A △ B) k = A k * B k := rfl

end TubalTensor
