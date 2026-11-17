import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq

set_option autoImplicit false

open _root_.LT.LatticeTree
open scoped Matrix

namespace LT
export _root_.LT (LatticeTree.Vertex.IsWithin LatticeTree.Vertex LatticeTree.stdVertex LatticeTree.Vertex.act LatticeTree.unitOfNeZero)
namespace LatticeTree
export _root_.LT.LatticeTree (Vertex.IsWithin stdLattice latticeMap latticeMap_mul latticeMap_mono isFullLattice_stdLattice latticeMap_le_stdLattice_of_isInteger scalarGL scalarGL_coe scalarGL_mul scalarGL_mul_comm Vertex stdVertex Vertex.act unitOfNeZero unitOfNeZero_coe isInteger_neg latticeMap_scalarGL_eq_self_of_isUnit)
namespace CartanEasy
open _root_.LT.LatticeTree open _root_.LT

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/--
@isnad1 id=eq.0h2v.s9.59904b15f2e5 from=translated src=- shape=cdf49509 vocab=8095c81f
-/
theorem coe_scalarGL_det_mul_inv (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((scalarGL (Matrix.GeneralLinearGroup.det g) * g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = (g : Matrix (Fin 2) (Fin 2) K).adjugate := by
  have hdet : ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = (g : Matrix (Fin 2) (Fin 2) K).det := by
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hunit : IsUnit (g : Matrix (Fin 2) (Fin 2) K).det := by
    rw [← hdet]; exact Units.isUnit _
  rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.coe_units_inv, Matrix.inv_def,
    smul_smul, hdet, Ring.mul_inverse_cancel _ hunit, one_smul]

/--
@isnad1 id=isintege.1h5v.s7.536025551d4c from=translated src=- shape=fcf26f30 vocab=d3a4722f
-/
theorem isInteger_adjugate {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j)) (i j : Fin 2) :
    IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K).adjugate i j) := by
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · exact hint 1 1
  · exact isInteger_neg (hint 0 1)
  · exact isInteger_neg (hint 1 0)
  · exact hint 0 0

/--
@isnad1 id=le.1h3v.s9.4936432f3c2b from=translated src=- shape=9f6fb301 vocab=0fa66914
-/
theorem latticeMap_scalarGL_det_le (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j)) :
    latticeMap (scalarGL (Matrix.GeneralLinearGroup.det g)) (stdLattice R K) ≤ latticeMap g (stdLattice R K) := by
  have hadj : latticeMap (scalarGL (Matrix.GeneralLinearGroup.det g) * g⁻¹) (stdLattice R K) ≤ stdLattice R K := by
    apply latticeMap_le_stdLattice_of_isInteger
    intro i j
    rw [coe_scalarGL_det_mul_inv]
    exact isInteger_adjugate hint i j
  have := latticeMap_mono (R := R) g hadj
  rwa [← latticeMap_mul, ← mul_assoc, ← scalarGL_mul_comm, mul_assoc, mul_inv_cancel, mul_one] at this

variable [IsFractionRing R K]

/--
@isnad1 id=iswithin.3h6v.s8.6fdf31dd3bdc from=translated src=- shape=665dbf18 vocab=23c4a6e6
-/
theorem isWithin_stdVertex_act {ϖ : R} (hϖ0 : ϖ ≠ 0) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ) (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    Vertex.IsWithin (unitOfNeZero (K := K) hϖ0) k (stdVertex R K) (Vertex.act g (stdVertex R K)) := by

  let uK : Kˣ := Units.map (algebraMap R K : R →* K) u
  have hsplit : Matrix.GeneralLinearGroup.det g = uK * unitOfNeZero (K := K) hϖ0 ^ k := by
    ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, unitOfNeZero_coe]
    show ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = algebraMap R K u * algebraMap R K ϖ ^ k
    rw [← hdet]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ0 ^ k)) (stdLattice R K) ≤ latticeMap g (stdLattice R K) := by
    have h := latticeMap_scalarGL_det_le (R := R) g hint
    rwa [hsplit, scalarGL_mul, latticeMap_mul, latticeMap_scalarGL_eq_self_of_isUnit u.isUnit rfl] at h
  exact ⟨stdLattice R K, latticeMap g (stdLattice R K), isFullLattice_stdLattice, isFullLattice_stdLattice.map g,
    rfl, rfl, hlow, latticeMap_le_stdLattice_of_isInteger hint⟩

end LT.LatticeTree.CartanEasy

open _root_.LT.LatticeTree open _root_.P2MW.S_LT_LatticeTree_Vertex_isWithin_stdVertex_act_of_isInteger_of_det_eq.LT.LatticeTree

/--
@isnad1 id=iswithin.3h6v.s8.7e09f39141e6 from=translated src=- shape=90c1f5d9 vocab=78d0de2e
-/
theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hint : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j))
    (k : ℕ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) k
      (LT.LatticeTree.stdVertex R K) (LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K)) :=
  LT.LatticeTree.CartanEasy.isWithin_stdVertex_act hϖ.ne_zero g hint k u hdet
