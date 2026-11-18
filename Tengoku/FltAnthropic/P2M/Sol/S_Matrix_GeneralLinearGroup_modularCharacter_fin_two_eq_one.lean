import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Matrix

namespace SolGL2Unimodular

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [LocallyCompactSpace (GL (Fin 2) F)]

section Elements

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)]

def glOf (M : Matrix (Fin 2) (Fin 2) F) (h : M.det ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero M h

/--
@isnad1 id=eq.1h2v.s7.de9b0af92cd3 from=translated src=- shape=7ffb5e52 vocab=c59aabba
-/
@[scoped simp] theorem coe_glOf (M : Matrix (Fin 2) (Fin 2) F) (h : M.det ≠ 0) :
    ((glOf M h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M := rfl

/--
@isnad1 id=ne.0h2v.s8.05805382264b from=translated src=- shape=d31933af vocab=21efa1c7
-/
theorem det_T01 (c : F) : (!![(1 : F), c; 0, 1]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp

/--
@isnad1 id=ne.0h2v.s8.522b2864f783 from=translated src=- shape=11622ff1 vocab=21efa1c7
-/
theorem det_T10 (c : F) : (!![(1 : F), 0; c, 1]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp

/--
@isnad1 id=ne.2h3v.s8.6928f76ea103 from=translated src=- shape=bc2a0118 vocab=21efa1c7
-/
theorem det_Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : (!![a, 0; 0, b]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp [ha, hb]

/--
@isnad1 id=ne.0h1v.s8.1e52d14c66d0 from=translated src=- shape=efecacee vocab=21efa1c7
-/
theorem det_W : (!![(0 : F), 1; 1, 0]).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]; simp

def T01 (c : F) : GL (Fin 2) F := glOf !![(1 : F), c; 0, 1] (det_T01 c)

def T10 (c : F) : GL (Fin 2) F := glOf !![(1 : F), 0; c, 1] (det_T10 c)

def Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : GL (Fin 2) F := glOf !![a, 0; 0, b] (det_Dg ha hb)

def W : GL (Fin 2) F := glOf !![(0 : F), 1; 1, 0] det_W

/--
@isnad1 id=eq.0h2v.s7.a8cf1023c144 from=translated src=- shape=b2ac6b74 vocab=2db1a1fb
-/
theorem T01_mul_T01 (c : F) : T01 c * T01 c = T01 (c + c) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h2v.s7.1a9371733347 from=translated src=- shape=b2ac6b74 vocab=0065ea69
-/
theorem T10_mul_T10 (c : F) : T10 c * T10 c = T10 (c + c) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T10, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h1v.s7.327568ad1958 from=translated src=- shape=82a407f1 vocab=a9a4ce5b
-/
theorem T01_zero : T01 (0 : F) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [T01, coe_glOf, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.0h1v.s7.5416dfe8e80e from=translated src=- shape=82a407f1 vocab=910f49f8
-/
theorem T10_zero : T10 (0 : F) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [T10, coe_glOf, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=eq.1h2v.s8.45819db56f35 from=translated src=- shape=f55c0ad2 vocab=7a6255ef
-/
theorem Dg_mul_T01 (h2 : (2 : F) ≠ 0) (c : F) :
    Dg h2 one_ne_zero * T01 c = T01 (c + c) * Dg h2 one_ne_zero := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T01, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/--
@isnad1 id=eq.1h2v.s8.74b4a6afaf3e from=translated src=- shape=611fefe5 vocab=475410f6
-/
theorem Dg_mul_T10 (h2 : (2 : F) ≠ 0) (c : F) :
    Dg one_ne_zero h2 * T10 c = T10 (c + c) * Dg one_ne_zero h2 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, T10, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/--
@isnad1 id=eq.2h3v.s8.1fdded644138 from=translated src=- shape=eea94770 vocab=2807b4bf
-/
theorem W_mul_Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : W * Dg ha hb = Dg hb ha * W := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, W, Dg, coe_glOf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.2h4v.s9.4311a070e55c from=translated src=- shape=286e4a5b vocab=d2e13855
-/
theorem Dg_mul_Dg_comm {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (g : GL (Fin 2) F) :
    g * (Dg ha hb * Dg hb ha) = Dg ha hb * Dg hb ha * g := by
  have hval : ((Dg ha hb : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((Dg hb ha : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a * b) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    simp only [Dg, coe_glOf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  apply Units.ext
  simp only [Units.val_mul]
  rw [hval, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

end Elements

noncomputable abbrev mc : GL (Fin 2) F →* NNReal := modularCharacter

/--
@isnad1 id=lt.0h2v.s8.ca8cad857efb from=translated src=- shape=d2ef0c11 vocab=598e6e44
-/
theorem mc_pos (g : GL (Fin 2) F) : 0 < mc g := modularCharacterFun_pos g

/--
@isnad1 id=eq.1h4v.s10.7531763edd7c from=translated src=- shape=593dcbfc vocab=ffb88c5b
-/
theorem mc_eq_of_mul_eq_mul {x y y' : GL (Fin 2) F} (h : x * y = y' * x) : mc y = mc y' := by
  have h1 : mc x * mc y = mc y' * mc x := by rw [← map_mul, ← map_mul, h]
  rw [mul_comm (mc y') (mc x)] at h1
  exact mul_left_cancel₀ (mc_pos x).ne' h1

/--
@isnad1 id=eq.1h2v.s9.1615109de60f from=translated src=- shape=365e859d vocab=ffb88c5b
-/
theorem mc_eq_one_of_forall_comm {z : GL (Fin 2) F} (hz : ∀ g : GL (Fin 2) F, g * z = z * g) :
    mc z = 1 := by
  borelize (GL (Fin 2) F)
  show modularCharacterFun z = 1
  rw [modularCharacterFun_eq_haarScalarFactor MeasureTheory.Measure.haar z]
  have hfun : (fun x : GL (Fin 2) F => x * z) = fun x => z * x := funext fun x => hz x
  have h1 : Measure.map (fun x : GL (Fin 2) F => x * z) haar = haar := by
    rw [hfun]; exact map_mul_left_eq_self haar z
  have key : ∀ (μ' : Measure (GL (Fin 2) F)) [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'],
      μ' = haar → haarScalarFactor μ' haar = 1 := by
    intro μ' _ _ h
    subst h
    exact haarScalarFactor_self _
  exact key _ h1

/--
@isnad1 id=eq.1h1v.s5.18d8d18b15f3 from=translated src=- shape=805e5ce5 vocab=290eddd5
-/
theorem nnreal_eq_one_of_mul_self_eq_one {a : NNReal} (h : a * a = 1) : a = 1 := by
  have h' : (a : ℝ) * a = 1 := by exact_mod_cast h
  have ha : (0 : ℝ) ≤ a := a.coe_nonneg
  have : (a : ℝ) = 1 := by nlinarith
  exact_mod_cast this

/--
@isnad1 id=eq.2h1v.s5.2bc1d03a8dbc from=translated src=- shape=81766222 vocab=290eddd5
-/
theorem nnreal_eq_one_of_mul_self_eq_self {a : NNReal} (ha : a ≠ 0) (h : a * a = a) : a = 1 := by
  have h2 : a * a = 1 * a := by rw [one_mul]; exact h
  exact mul_right_cancel₀ ha h2

/--
@isnad1 id=eq.0h2v.s8.ae5d7b392dd5 from=translated src=- shape=6c40b128 vocab=8d72365c
-/
theorem mc_T01 (c : F) : mc (T01 c) = 1 := by
  by_cases h2 : (2 : F) = 0
  · have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    apply nnreal_eq_one_of_mul_self_eq_one
    rw [← map_mul, T01_mul_T01, hcc, T01_zero, map_one]
  · apply nnreal_eq_one_of_mul_self_eq_self (mc_pos _).ne'
    rw [← map_mul, T01_mul_T01]
    exact (mc_eq_of_mul_eq_mul (Dg_mul_T01 h2 c)).symm

/--
@isnad1 id=eq.0h2v.s8.dc8a96deb104 from=translated src=- shape=6c40b128 vocab=b556efb0
-/
theorem mc_T10 (c : F) : mc (T10 c) = 1 := by
  by_cases h2 : (2 : F) = 0
  · have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
    apply nnreal_eq_one_of_mul_self_eq_one
    rw [← map_mul, T10_mul_T10, hcc, T10_zero, map_one]
  · apply nnreal_eq_one_of_mul_self_eq_self (mc_pos _).ne'
    rw [← map_mul, T10_mul_T10]
    exact (mc_eq_of_mul_eq_mul (Dg_mul_T10 h2 c)).symm

/--
@isnad1 id=eq.2h3v.s8.a1c610177c90 from=translated src=- shape=9f8c46bc vocab=3dc8514d
-/
theorem mc_Dg {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : mc (Dg ha hb) = 1 := by
  apply nnreal_eq_one_of_mul_self_eq_one
  have h1 : mc (Dg ha hb) = mc (Dg hb ha) := mc_eq_of_mul_eq_mul (W_mul_Dg ha hb)
  calc mc (Dg ha hb) * mc (Dg ha hb) = mc (Dg ha hb) * mc (Dg hb ha) := by rw [← h1]
    _ = mc (Dg ha hb * Dg hb ha) := (map_mul _ _ _).symm
    _ = 1 := mc_eq_one_of_forall_comm (Dg_mul_Dg_comm ha hb)

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in

/--
@isnad1 id=or.1h2v.s7.27ada9eae498 from=translated src=- shape=2a7ea492 vocab=8aeb5b90
-/
theorem glOf_toMatrix_eq (t : TransvectionStruct (Fin 2) F) (h : t.toMatrix.det ≠ 0) :
    glOf t.toMatrix h = T01 t.c ∨ glOf t.toMatrix h = T10 t.c := by
  obtain ⟨i, j, hij, c⟩ := t
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · left
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    simp only [coe_glOf, T01, TransvectionStruct.toMatrix, Matrix.transvection]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · right
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    simp only [coe_glOf, T10, TransvectionStruct.toMatrix, Matrix.transvection]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single]
  · exact absurd rfl hij

/--
@isnad1 id=eq.1h2v.s9.e214fa4398be from=translated src=- shape=218af014 vocab=98be6105
-/
theorem mc_glOf_toMatrix (t : TransvectionStruct (Fin 2) F) (h : t.toMatrix.det ≠ 0) :
    mc (glOf t.toMatrix h) = 1 := by
  rcases glOf_toMatrix_eq t h with h' | h' <;> rw [h']
  · exact mc_T01 _
  · exact mc_T10 _

omit [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace (GL (Fin 2) F)] in
/--
@isnad1 id=ne.0h2v.s7.8910a7a366f5 from=translated src=- shape=f1f6068f vocab=2a5b4bb6
-/
theorem det_prod_toMatrix_ne_zero (L : List (TransvectionStruct (Fin 2) F)) :
    ((L.map TransvectionStruct.toMatrix).prod).det ≠ 0 := by
  rw [TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero

/--
@isnad1 id=eq.0h2v.s9.781b89e41737 from=translated src=- shape=0183d0d6 vocab=307f2f2a
-/
theorem mc_glOf_prod (L : List (TransvectionStruct (Fin 2) F)) :
    mc (glOf (L.map TransvectionStruct.toMatrix).prod (det_prod_toMatrix_ne_zero L)) = 1 := by
  induction L with
  | nil =>
    have : glOf (([] : List (TransvectionStruct (Fin 2) F)).map TransvectionStruct.toMatrix).prod
        (det_prod_toMatrix_ne_zero []) = 1 := Units.ext (by simp)
    rw [this, map_one]
  | cons t L ih =>
    have ht : t.toMatrix.det ≠ 0 := by rw [TransvectionStruct.det]; exact one_ne_zero
    have hsplit : glOf ((t :: L).map TransvectionStruct.toMatrix).prod
        (det_prod_toMatrix_ne_zero (t :: L)) =
        glOf t.toMatrix ht * glOf (L.map TransvectionStruct.toMatrix).prod
          (det_prod_toMatrix_ne_zero L) := Units.ext (by simp)
    rw [hsplit, map_mul, mc_glOf_toMatrix, ih, one_mul]

/--
@isnad1 id=eq.0h2v.s9.e217a6e793b4 from=translated src=- shape=75129050 vocab=9f71e39b
-/
theorem modularCharacter_eq_one (g : GL (Fin 2) F) : modularCharacter g = 1 := by
  obtain ⟨L, L', D, hg⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (g : Matrix (Fin 2) (Fin 2) F)
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [hg, Matrix.det_mul, Matrix.det_mul, TransvectionStruct.det_toMatrix_prod,
    TransvectionStruct.det_toMatrix_prod, Matrix.det_diagonal, Fin.prod_univ_two, one_mul,
    mul_one] at hdet
  have hD0 : D 0 ≠ 0 := left_ne_zero_of_mul hdet
  have hD1 : D 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hdiag : glOf (Matrix.diagonal D) (by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]; exact mul_ne_zero hD0 hD1) = Dg hD0 hD1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [coe_glOf, Dg]
    fin_cases i <;> fin_cases j <;> simp
  have hgU : g = glOf (L.map TransvectionStruct.toMatrix).prod (det_prod_toMatrix_ne_zero L) *
      glOf (Matrix.diagonal D) (by
        rw [Matrix.det_diagonal, Fin.prod_univ_two]; exact mul_ne_zero hD0 hD1) *
      glOf (L'.map TransvectionStruct.toMatrix).prod (det_prod_toMatrix_ne_zero L') := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glOf, coe_glOf, coe_glOf]
    exact hg
  show mc g = 1
  rw [hgU, map_mul, map_mul, mc_glOf_prod, mc_glOf_prod, hdiag, mc_Dg, one_mul, one_mul]

end SolGL2Unimodular
open scoped _root_.P2MW.S_Matrix_GeneralLinearGroup_modularCharacter_fin_two_eq_one.SolGL2Unimodular

/--
@isnad1 id=eq.0h2v.s9.e217a6e793b4 from=translated src=- shape=75129050 vocab=9f71e39b
-/
theorem solution
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] (g : GL (Fin 2) F) :
    MeasureTheory.Measure.modularCharacter g = 1 :=
  SolGL2Unimodular.modularCharacter_eq_one g
