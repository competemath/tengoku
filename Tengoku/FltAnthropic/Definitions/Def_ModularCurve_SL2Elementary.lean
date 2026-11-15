import Tengoku.Seed.LinearAlgebra.Matrix.FixedDetMatrices
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.GroupTheory.Index
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix MatrixGroups Subgroup

namespace ModularCurve

section Elementary

variable {R : Type*} [CommRing R]

def upperElem (c : R) : SL(2, R) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def lowerElem (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

/--
@isnad1 id=eq.0h2v.s8.9debe4985966 from=translated src=- shape=3783ae51 vocab=8252df06
-/
@[simp] lemma upperElem_coe (c : R) :
    (upperElem c : Matrix (Fin 2) (Fin 2) R) = !![1, c; 0, 1] := rfl

/--
@isnad1 id=eq.0h2v.s8.73846e8d61f0 from=translated src=- shape=0d2d5694 vocab=76146f6b
-/
@[simp] lemma lowerElem_coe (c : R) :
    (lowerElem c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl

/--
@isnad1 id=eq.0h3v.s7.c1f6ef7ea11e from=translated src=- shape=9de823f5 vocab=54a58c52
-/
lemma upperElem_mul (a b : R) : upperElem a * upperElem b = upperElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/--
@isnad1 id=eq.0h3v.s7.073ea08b31d7 from=translated src=- shape=9de823f5 vocab=5269472e
-/
lemma lowerElem_mul (a b : R) : lowerElem a * lowerElem b = lowerElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h1v.s6.1bc29bfc6a3b from=translated src=- shape=82a407f1 vocab=6c6f2c55
-/
@[simp] lemma upperElem_zero : upperElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.0h1v.s6.9af6cd120770 from=translated src=- shape=82a407f1 vocab=c08963f5
-/
@[simp] lemma lowerElem_zero : lowerElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.0h3v.s7.d1a1a57bd8e6 from=translated src=- shape=adea5fea vocab=4789a1dc
-/
lemma upperElem_pow (a : R) (n : ℕ) : upperElem a ^ n = upperElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, upperElem_mul]
    congr 1
    push_cast
    ring

/--
@isnad1 id=eq.0h3v.s7.ad8cebd41618 from=translated src=- shape=adea5fea vocab=e9a5c572
-/
lemma lowerElem_pow (a : R) (n : ℕ) : lowerElem a ^ n = lowerElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, lowerElem_mul]
    congr 1
    push_cast
    ring

def elemSet (R : Type*) [CommRing R] : Set SL(2, R) :=
  Set.range upperElem ∪ Set.range lowerElem

/--
@isnad1 id=mem.0h2v.s7.88d3f5ed7d40 from=translated src=- shape=9f611aff vocab=cc485cab
-/
lemma upperElem_mem_closure_elemSet (c : R) : upperElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inl ⟨c, rfl⟩)

/--
@isnad1 id=mem.0h2v.s7.cf8c15cb753f from=translated src=- shape=9f611aff vocab=986de948
-/
lemma lowerElem_mem_closure_elemSet (c : R) : lowerElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inr ⟨c, rfl⟩)

end Elementary

end ModularCurve
