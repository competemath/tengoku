import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_ConstantReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue

open _root_.AlgebraicCurve open _root_.IsLocalRing

namespace AlgebraicCurve
export _root_.AlgebraicCurve (ConstantReduction)
namespace ConstantReduction
export _root_.AlgebraicCurve.ConstantReduction (integers residue algebraMap_mem_iff residue_algebraMap)
namespace W7B2B
open _root_.AlgebraicCurve.ConstantReduction open _root_.AlgebraicCurve

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : ConstantReduction A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : ConstantReduction A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : ConstantReduction A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem linearIndependent_of_linearIndependent_residue' (R : ConstantReduction A F Fbar)
    {ι : Type*} (v : ι → R.integers)
    (hv : LinearIndependent (ResidueField A) (fun i => R.residue (v i))) :
    LinearIndependent L (fun i => (v i : F)) := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum
  by_contra hne
  obtain ⟨i₀, hi₀t, hgi₀⟩ := not_forall₂.mp hne
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀t⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀t
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
    exact hgi₀ h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  set c : L := (g i₁)⁻¹ with hc
  have hcA : ∀ i ∈ t, c * g i ∈ A := by
    intro i hi
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
        ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
      _ = 1 := inv_mul_cancel₀ hv₁
  have hc1 : c * g i₁ = 1 := inv_mul_cancel₀ hg₁

  let a : ι → A := fun i => if hi : i ∈ t then ⟨c * g i, hcA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = c * g i := fun i hi => by simp [a, dite_eq_left hi]

  set X : R.integers := ∑ i ∈ t, constHom R (a i) * v i with hX
  have hX0 : X = 0 := by
    apply Subtype.ext
    have : ((X : R.integers) : F) = ∑ i ∈ t, (c * g i) • (v i : F) := by
      rw [hX]
      push_cast
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [coe_constHom, ha i hi, Algebra.smul_def]
    rw [this]
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    rfl
  have hres : ∑ i ∈ t, (IsLocalRing.residue A (a i)) • R.residue (v i) = 0 := by
    have h := congrArg R.residue hX0
    rw [map_zero, hX, map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, residue_constHom, Algebra.smul_def]
  have hall : IsLocalRing.residue A (a i₁) = 0 :=
    linearIndependent_iff'.mp hv t (fun i => IsLocalRing.residue A (a i)) hres i₁ hi₁t
  have ha1 : a i₁ = 1 := Subtype.ext (by rw [ha i₁ hi₁t, hc1]; rfl)
  rw [ha1, map_one] at hall
  exact one_ne_zero hall

end AlgebraicCurve.ConstantReduction.W7B2B
open scoped _root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.AlgebraicCurve.ConstantReduction _root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.AlgebraicCurve.ConstantReduction.W7B2B
open scoped _root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.AlgebraicCurve.ConstantReduction
open scoped _root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.AlgebraicCurve

open AlgebraicCurve.ConstantReduction.W7B2B in
theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar)
    {ι : Type*} (v : ι → R.integers)
    (hv : LinearIndependent (IsLocalRing.ResidueField A) (fun i => R.residue (v i))) :
    LinearIndependent L (fun i => (v i : F)) :=
  linearIndependent_of_linearIndependent_residue' R v hv
