import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.Seed.Algebra.Module.Lattice
import Tengoku.Seed.LinearAlgebra.Matrix.Basis
import Tengoku.Seed.LinearAlgebra.FreeModule.PID

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LT_LatticeTree_exists_act_stdVertex_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LT_LatticeTree_exists_act_stdVertex_eq

set_option autoImplicit false

namespace LatticeTransitivity

open LT.LatticeTree Module
open scoped Matrix

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

variable (R K) in

private theorem isTorsionFree_of_isFractionRing [IsDomain R] [IsFractionRing R K] : Module.IsTorsionFree R K :=
  Module.isTorsionFree_iff_smul_eq_zero.2 fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h0 => (map_eq_zero_iff _ (IsFractionRing.injective R K)).1 h0) id

private theorem exists_latticeMap_stdLattice_eq [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K, latticeMap g (stdLattice R K) = L := by
  classical
  haveI : Module.IsTorsionFree R K := isTorsionFree_of_isFractionRing R K
  haveI : Submodule.IsLattice K L := ⟨hL.1, hL.2⟩
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R L) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Submodule.IsLattice.finrank_of_pi K L, Fintype.card_fin]
  let b : Basis (Fin 2) R L := (Module.Free.chooseBasis R L).reindex (Fintype.equivFinOfCardEq hcard)
  let bK : Basis (Fin 2) K (Fin 2 → K) := b.extendOfIsLattice K
  let e : Basis (Fin 2) K (Fin 2 → K) := Pi.basisFun K (Fin 2)
  refine ⟨⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK, bK.toMatrix_mul_toMatrix_flip e⟩,
    ?_⟩
  have hcol : ∀ j : Fin 2, (e.toMatrix bK) *ᵥ (Pi.single j 1 : Fin 2 → K) = (b j : Fin 2 → K) := by
    intro j
    ext i
    rw [Matrix.mulVec_single_one]
    change e.toMatrix bK i j = _
    simp only [e, bK, Basis.toMatrix_apply, Pi.basisFun_repr, Basis.extendOfIsLattice_apply]
  have himg : (mulVecLinR (R := R) (⟨e.toMatrix bK, bK.toMatrix e, e.toMatrix_mul_toMatrix_flip bK,
      bK.toMatrix_mul_toMatrix_flip e⟩ : Matrix.GeneralLinearGroup (Fin 2) K)) ''
        Set.range (fun j : Fin 2 => (Pi.single j 1 : Fin 2 → K)) =
      L.subtype '' Set.range b := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext j
    exact hcol j
  rw [latticeMap, stdLattice_eq_span, Submodule.map_span, himg, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

end LatticeTransitivity

open LT LT.LatticeTree in

/--
@isnad1 id=ex.0h3v.s7.c880406a3b91 from=translated src=- shape=62899c3f vocab=81adecf1
-/
theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : LT.LatticeTree.Vertex R K) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) K,
      LT.LatticeTree.Vertex.act g (LT.LatticeTree.stdVertex R K) = v := by
  induction v using Quotient.inductionOn with
  | h L =>
    obtain ⟨g, hg⟩ := LatticeTransitivity.exists_latticeMap_stdLattice_eq L.2
    refine ⟨g, ?_⟩
    change LT.LatticeTree.Vertex.mk R K (LT.LatticeTree.latticeMap g (LT.LatticeTree.stdLattice R K)) _ =
      LT.LatticeTree.Vertex.mk R K L.1 L.2
    rw [LT.LatticeTree.Vertex.mk_eq_mk_iff, hg]
    exact LT.LatticeTree.Homothetic.refl L.1
