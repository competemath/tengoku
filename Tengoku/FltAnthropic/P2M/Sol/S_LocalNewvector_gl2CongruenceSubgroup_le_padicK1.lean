import Tengoku.FltAnthropic.Definitions.Def_LocalNewvector_ConductorDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms LocalNewvector.gl2CongruenceSubgroup_le_padicK1_impl` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LocalNewvector_gl2CongruenceSubgroup_le_padicK1

set_option autoImplicit false

noncomputable section

namespace LocalNewvector
export _root_.LocalNewvector (HasFiniteLevelFixed congruenceK1_le_congruenceK0 padicK0 padicK1)
open _root_.LocalNewvector

open FLT.SmoothVectors

variable (p : ℕ) [Fact p.Prime]

private theorem padicRadius_le_one (n : ℕ) : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := by
  refine zpow_le_one_of_nonpos₀ ?_ (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact_mod_cast (Fact.out : p.Prime).one_le

variable {n : ℕ}

private def principalMat {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  fun i j => ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j,
    (norm_sub_one_entry_le_one_iff p).mp ((hg.1 i j).trans (padicRadius_le_one p n))⟩

private theorem coe_principalMat_apply {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) (i j : Fin 2) :
    ((principalMat p hg i j : ℤ_[p]) : ℚ_[p])
      = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j :=
  rfl

private theorem mapMatrix_principalMat {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) :
    (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (principalMat p hg)
      = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) :=
  Matrix.ext fun i j => (PadicInt.algebraMap_apply _).trans (coe_principalMat_apply p hg i j)

private theorem mapMatrix_injective_padic :
    Function.Injective
      ((algebraMap ℤ_[p] ℚ_[p]).mapMatrix : Matrix (Fin 2) (Fin 2) ℤ_[p] → _) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h i) j
  exact Subtype.coe_injective this

private def principalPreimage {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) : GL (Fin 2) ℤ_[p] :=
  ⟨principalMat p hg, principalMat p (inv_mem hg),
    mapMatrix_injective_padic p (by
      rw [map_mul, mapMatrix_principalMat, mapMatrix_principalMat, map_one,
        ← Units.val_mul, mul_inv_cancel, Units.val_one]),
    mapMatrix_injective_padic p (by
      rw [map_mul, mapMatrix_principalMat, mapMatrix_principalMat, map_one,
        ← Units.val_mul, inv_mul_cancel, Units.val_one])⟩

private theorem coe_principalPreimage_apply {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) (i j : Fin 2) :
    ((principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) i j : ℚ_[p])
      = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j :=
  rfl

private theorem map_principalPreimage {g : GL (Fin 2) ℚ_[p]}
    (hg : g ∈ gl2CongruenceSubgroup p n) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p])
      (principalPreimage p hg) = g :=
  Units.ext (mapMatrix_principalMat p hg)

/--
@isnad1 id=le.0h2v.s8.fd4361e955b2 from=translated src=- shape=762e5517 vocab=8b6f925d
-/
theorem gl2CongruenceSubgroup_le_padicK1_impl (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ padicK1 p n := by
  intro g hg
  refine ⟨principalPreimage p hg, map_principalPreimage p hg, ?_, ?_⟩
  · rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    have h10 : ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 0
        = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0 := by
      simp [Matrix.sub_apply]
    have hnorm : ‖((principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 : ℚ_[p])‖
        = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ :=
      congrArg _ (coe_principalPreimage_apply p hg 1 0)
    calc ‖(principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0‖
        = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ := hnorm
      _ = ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 0‖ := by rw [h10]
      _ ≤ (p : ℝ) ^ (-(n : ℤ)) := hg.1 1 0
  · rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    have h11 : ((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 1
        = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1 := by
      simp [Matrix.sub_apply]
    have hnorm :
        ‖((principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1 - 1 : ℤ_[p])‖
          = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one,
        coe_principalPreimage_apply p hg 1 1]
    calc ‖(principalPreimage p hg : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1 - 1‖
        = ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1‖ := hnorm
      _ = ‖((g : Matrix (Fin 2) (Fin 2) ℚ_[p]) - 1) 1 1‖ := by rw [h11]
      _ ≤ (p : ℝ) ^ (-(n : ℤ)) := hg.1 1 1

end LocalNewvector

/--
@isnad1 id=le.0h2v.s8.fd4361e955b2 from=translated src=- shape=762e5517 vocab=8b6f925d
-/
theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FLT.SmoothVectors.gl2CongruenceSubgroup p n ≤ LocalNewvector.padicK1 p n :=
  LocalNewvector.gl2CongruenceSubgroup_le_padicK1_impl (p := p) n
