import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckeCosetLocal
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckePair
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow.lean`: removed 3 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LocalGL2_unipotentGL2_mem_doubleCoset_diagPi_zpow_neg_mul_localRepInf_zpow

set_option autoImplicit false

open LocalGL2 HeckePair

namespace R5UnipCartan

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)

/--
@isnad1 id=eq.1h3v.s9.75fc68f650bf from=translated src=- shape=1df1012a vocab=9e8f76ab
-/
theorem coe_z :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.1h4v.s9.a93a59e1ac94 from=translated src=- shape=6f3675ce vocab=da2d9e4e
-/
theorem coe_z_pow (n : ℕ) :
    (((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ ^ n • (1 : Matrix (Fin 2) (Fin 2) K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_z, smul_mul_smul_comm, one_mul, ← pow_succ]

/--
@isnad1 id=eq.1h4v.s9.f13c423732a4 from=translated src=- shape=cd477d59 vocab=b66833e0
-/
theorem coe_localRepInf_pow (n : ℕ) :
    ((localRepInf ϖ hϖ0 ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, algebraMap R K ϖ ^ n] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, coe_localRepInf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/--
@isnad1 id=eq.1h4v.s9.e48de5cd69c2 from=translated src=- shape=c863bae3 vocab=2ec55e22
-/
theorem z_central (g : GL (Fin 2) K) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * g = g * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) := by
  apply Units.ext
  have h := coe_z ϖ hϖ0
  rw [Units.val_mul] at h
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, h, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

/--
@isnad1 id=commute.1h3v.s7.8b16fdd4d61b from=translated src=- shape=6aaeb39e vocab=719dcd72
-/
theorem commute_diagPi_localRepInf : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0 : GL (Fin 2) K) := by
  show diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_diagPi, coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.1h4v.s10.18682e5922b5 from=translated src=- shape=5f98a8e4 vocab=35c88c0e
-/
theorem zpow_neg_mul_zpow_eq (r : ℕ) :
    diagPi ϖ hϖ0 ^ (-(r : ℤ)) * localRepInf ϖ hϖ0 ^ (r : ℤ) =
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(r : ℤ)) * localRepInf ϖ hϖ0 ^ (2 * r) := by
  rw [(commute_diagPi_localRepInf ϖ hϖ0).mul_zpow, mul_assoc, ← zpow_natCast, ← zpow_add]
  congr 2
  push_cast
  ring

/--
@isnad1 id=iff.1h5v.s7.3f980faaf4a4 from=translated src=- shape=9914596d vocab=7c7b6497
-/
theorem mem_doubleCoset_central_mul_iff {G : Type*} [Group G] {U : Subgroup G} {c g x : G}
    (hc : ∀ y : G, c * y = y * c) :
    x ∈ doubleCoset U (c * g) ↔ c⁻¹ * x ∈ doubleCoset U g := by
  rw [mem_doubleCoset_iff, mem_doubleCoset_iff]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, ← hc u]; group]
    rw [inv_mul_cancel_left]
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, ← hc u]; group, huv,
      mul_inv_cancel_left]

def lowerR (c : R) : GL (Fin 2) R :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def rightR (u : Rˣ) (t : R) : GL (Fin 2) R :=
  ⟨!![t, (u : R); -((u⁻¹ : Rˣ) : R), 0], !![0, -(u : R); ((u⁻¹ : Rˣ) : R), t], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]⟩

/--
@isnad1 id=eq.1h5v.s11.bd8f3f4c5110 from=translated src=- shape=ead169d9 vocab=2f506c62
-/
theorem key (u : Rˣ) (r : ℕ) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (lowerR (((u⁻¹ : Rˣ) : R) * ϖ ^ r)) *
        localRepInf ϖ hϖ0 ^ (2 * r) *
        Matrix.GeneralLinearGroup.map (algebraMap R K) (rightR u (ϖ ^ r)) =
      (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ r *
        AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hu0 : algebraMap R K u ≠ 0 := (Units.map (algebraMap R K : R →* K) u).ne_zero
  simp only [Units.val_mul, coe_z_pow, coe_localRepInf_pow, AutomorphicForm.unipotentGL2_coe,
    Matrix.smul_mul, Matrix.one_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerR, rightR, map_mul, map_pow, map_neg] <;>
    field_simp <;> ring

/--
@isnad1 id=mem.0h3v.s8.56a7dd80637f from=translated src=- shape=df5b0741 vocab=5a18ab5a
-/
theorem unipotentGL2_algebraMap_mem (b : R) :
    AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈ integralSubgroup R K := by
  refine ⟨AutomorphicForm.unipotentGL2 b, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply, AutomorphicForm.unipotentGL2_coe, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

/--
@isnad1 id=mem.1h4v.s9.a48d91f1ae02 from=translated src=- shape=824e496a vocab=d1a39ebf
-/
theorem integral_case (b : R) :
    AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈
      doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ (0 : ℤ) * localRepInf ϖ hϖ0 ^ (0 : ℤ)) := by
  rw [zpow_zero, zpow_zero, mul_one]
  exact mem_doubleCoset_iff.mpr ⟨_, unipotentGL2_algebraMap_mem b, 1, one_mem _, by rw [mul_one, mul_one]⟩

/--
@isnad1 id=mem.1h5v.s10.11972f69dd0b from=translated src=- shape=4978ebc4 vocab=e2f5159f
-/
theorem polar_case (u : Rˣ) (r : ℕ) :
    AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) ∈
      doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0 ^ (-(r : ℤ)) * localRepInf ϖ hϖ0 ^ (r : ℤ)) := by
  have hc : ∀ y : GL (Fin 2) K, (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(r : ℤ)) * y =
      y * (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) ^ (-(r : ℤ)) := fun y =>
    (Commute.zpow_left (show Commute (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) y from z_central ϖ hϖ0 y) _).eq
  rw [zpow_neg_mul_zpow_eq, mem_doubleCoset_central_mul_iff hc, zpow_neg, inv_inv, zpow_natCast, ← key]
  exact mem_doubleCoset_iff.mpr ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩

end R5UnipCartan

open R5UnipCartan in
/--
@isnad1 id=and.1h3v.s10.c004b6f393e6 from=translated src=- shape=7526ebdb vocab=e2f5159f
-/
theorem solution
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) :
    (∀ b : R, AutomorphicForm.unipotentGL2 (algebraMap R K b) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (0 : ℤ) * LocalGL2.localRepInf ϖ hϖ0 ^ (0 : ℤ))) ∧
    ∀ (u : Rˣ) (r : ℕ),
      AutomorphicForm.unipotentGL2 (algebraMap R K u * ((algebraMap R K ϖ)⁻¹) ^ r) ∈
        HeckePair.doubleCoset (LocalGL2.integralSubgroup R K)
          (LocalGL2.diagPi ϖ hϖ0 ^ (-(r : ℤ)) * LocalGL2.localRepInf ϖ hϖ0 ^ (r : ℤ)) :=
  ⟨integral_case ϖ hϖ0, polar_case ϖ hϖ0⟩
