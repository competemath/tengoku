import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluGx (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

def veluGy (x y : R) : R := -(2 * y + W.a₁ * x + W.a₃)

def veluT (x y : R) : R := 2 * W.veluGx x y - W.a₁ * W.veluGy x y

def veluU (x y : R) : R := W.veluGy x y ^ 2

def veluW (x y : R) : R := W.veluU x y + x * W.veluT x y

/--
@isnad1 id=eq.0h4v.s7.38e555497dea from=translated src=- shape=f8676ec6 vocab=e8b8a7a8
-/
lemma veluT_eq (x y : R) : W.veluT x y = 6 * x ^ 2 + W.b₂ * x + W.b₄ := by
  simp only [veluT, veluGx, veluGy, b₂, b₄]; ring

/--
@isnad1 id=eq.1h4v.s5.68eeeaba9672 from=translated src=- shape=ba53045a vocab=3a53fc85
-/
lemma veluU_eq_Ψ₂Sq_eval {x y : R} (h : W.toAffine.Equation x y) :
    W.veluU x y = W.Ψ₂Sq.eval x := by
  rw [Affine.equation_iff] at h
  simp only [veluU, veluGy, Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * h

/--
@isnad1 id=eq.0h4v.s5.dcc7110aa3f2 from=translated src=- shape=50b82554 vocab=505f53e4
-/
lemma veluGy_negY (x y : R) : W.veluGy x (W.toAffine.negY x y) = -W.veluGy x y := by
  simp only [veluGy, Affine.negY]; ring

/--
@isnad1 id=eq.0h4v.s5.5fadb707a8bd from=translated src=- shape=06f3ebc5 vocab=483f1fb3
-/
lemma veluT_negY (x y : R) : W.veluT x (W.toAffine.negY x y) = W.veluT x y := by
  simp only [veluT_eq]

/--
@isnad1 id=eq.0h4v.s5.f0814f9d4480 from=translated src=- shape=06f3ebc5 vocab=b4d7cd44
-/
lemma veluU_negY (x y : R) : W.veluU x (W.toAffine.negY x y) = W.veluU x y := by
  simp only [veluU, veluGy, Affine.negY]; ring

/--
@isnad1 id=eq.0h4v.s5.755f87519e72 from=translated src=- shape=06f3ebc5 vocab=b81fa99f
-/
lemma veluW_negY (x y : R) : W.veluW x (W.toAffine.negY x y) = W.veluW x y := by
  simp only [veluW, veluU_negY, veluT_negY]

/--
@isnad1 id=eq.1h4v.s5.b819e8f7f11b from=translated src=- shape=aa9f96cc vocab=4f980d43
-/
lemma veluGy_eq_zero_of_negY_eq {x y : R} (h : W.toAffine.negY x y = y) :
    W.veluGy x y = 0 := by
  have : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have := h
    simp only [Affine.negY] at this
    linear_combination -this
  simp [veluGy, this]

variable (S : Finset (R × R))

def veluTSum : R := ∑ P ∈ S, W.veluT P.1 P.2

def veluWSum : R := ∑ P ∈ S, W.veluW P.1 P.2

/--
@isnad1 id=eq.0h2v.s5.a0c4b60e381a from=translated src=- shape=3cf39731 vocab=ee389bb7
-/
@[simp] lemma veluTSum_empty : W.veluTSum ∅ = 0 := by simp [veluTSum]

/--
@isnad1 id=eq.0h2v.s5.8be74438ea04 from=translated src=- shape=3cf39731 vocab=acaf968d
-/
@[simp] lemma veluWSum_empty : W.veluWSum ∅ = 0 := by simp [veluWSum]

def veluQuotient : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluTSum S
  a₆ := W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S

/--
@isnad1 id=eq.0h3v.s4.904b9a662297 from=translated src=- shape=bc36041e vocab=0bc8479a
-/
@[simp] lemma veluQuotient_a₁ : (W.veluQuotient S).a₁ = W.a₁ := rfl
/--
@isnad1 id=eq.0h3v.s4.5dbef25ffffc from=translated src=- shape=bc36041e vocab=6965f0fc
-/
@[simp] lemma veluQuotient_a₂ : (W.veluQuotient S).a₂ = W.a₂ := rfl
/--
@isnad1 id=eq.0h3v.s4.061cac6b127b from=translated src=- shape=bc36041e vocab=dc8e6d37
-/
@[simp] lemma veluQuotient_a₃ : (W.veluQuotient S).a₃ = W.a₃ := rfl
/--
@isnad1 id=eq.0h3v.s6.e88a428ae65a from=translated src=- shape=d7c8c7eb vocab=cc6ae995
-/
lemma veluQuotient_a₄ : (W.veluQuotient S).a₄ = W.a₄ - 5 * W.veluTSum S := rfl
/--
@isnad1 id=eq.0h3v.s6.bb1cd7e0de2d from=translated src=- shape=c2bb2de5 vocab=72a4e4bd
-/
lemma veluQuotient_a₆ :
    (W.veluQuotient S).a₆ = W.a₆ - W.b₂ * W.veluTSum S - 7 * W.veluWSum S := rfl

/--
@isnad1 id=eq.0h2v.s4.4b2324ad6075 from=translated src=- shape=374d0946 vocab=4ac9aec2
-/
@[simp] lemma veluQuotient_empty : W.veluQuotient ∅ = W := by
  ext <;> simp [veluQuotient]

/--
@isnad1 id=eq.0h3v.s4.13426efde6f8 from=translated src=- shape=bc36041e vocab=f90415fe
-/
lemma veluQuotient_b₂ : (W.veluQuotient S).b₂ = W.b₂ := by
  simp [b₂]

/--
@isnad1 id=eq.0h3v.s6.8d836f4cc27b from=translated src=- shape=d7c8c7eb vocab=fb800a85
-/
lemma veluQuotient_b₄ : (W.veluQuotient S).b₄ = W.b₄ - 10 * W.veluTSum S := by
  simp only [b₄, veluQuotient_a₃, veluQuotient_a₁, veluQuotient_a₄]; ring

/--
@isnad1 id=eq.0h3v.s7.414ca5c837d9 from=translated src=- shape=227a2186 vocab=efe57c71
-/
lemma veluQuotient_b₆ :
    (W.veluQuotient S).b₆ = W.b₆ - 4 * W.b₂ * W.veluTSum S - 28 * W.veluWSum S := by
  simp only [b₆, b₂, veluQuotient_a₃, veluQuotient_a₆]; ring

/--
@isnad1 id=eq.0h3v.s8.2a7c0f7e5e2f from=translated src=- shape=af91360d vocab=15bc4ee7
-/
lemma veluQuotient_b₈ :
    (W.veluQuotient S).b₈ = W.b₈ + (5 * W.b₄ - W.b₂ ^ 2) * W.veluTSum S
      - 7 * W.b₂ * W.veluWSum S - 25 * W.veluTSum S ^ 2 := by
  simp only [b₈, b₂, b₄, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃, veluQuotient_a₄,
    veluQuotient_a₆]
  ring

structure IsVeluSet : Prop where
  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2

/--
@isnad1 id=isveluse.0h2v.s4.7117351d9c2d from=translated src=- shape=1d715c28 vocab=03094441
-/
lemma isVeluSet_empty : W.IsVeluSet ∅ := ⟨by simp⟩

end WeierstrassCurve
