import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_minpoly_adjoin_simple_eq_map_of_natDegree_le_finrank.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_minpoly_adjoin_simple_eq_map_of_natDegree_le_finrank
set_option autoImplicit false

open _root_.Polynomial open _root_.IntermediateField

namespace MinpolyOfConjugates

end MinpolyOfConjugates

namespace IntermediateField export _root_.IntermediateField (toAlgebra val AdjoinSimple.gen algHomAdjoinIntegralEquiv_symm_apply_gen ext algHomAdjoinIntegralEquiv equivOfEq adjoin.finrank adjoin adjoin_simple_adjoin_simple map_map restrictScalars mem_adjoin_simple_self subset_adjoin map) end IntermediateField
open scoped _root_.IntermediateField in

/--
@isnad1 id=eq.3h5v.s11.26a8e92af57d from=translated src=- shape=ad7aa941 vocab=50b556bb
-/
theorem solution
    {L F : Type*} [Field L] [Field F] [Algebra L F]
    (x y : F) (P : Polynomial (Polynomial ℤ)) (hP : P.Monic)
    (hxy : P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) x) y = 0)
    (hdeg : P.natDegree ≤ Module.finrank (↥(IntermediateField.adjoin L ({x} : Set F)))
      (↥(IntermediateField.adjoin (↥(IntermediateField.adjoin L ({x} : Set F))) ({y} : Set F)))) :
    minpoly (↥(IntermediateField.adjoin L ({x} : Set F))) y =
      P.map (Polynomial.eval₂RingHom (Int.castRingHom (↥(IntermediateField.adjoin L ({x} : Set F))))
        ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩) := by
  set K := IntermediateField.adjoin L ({x} : Set F)
  set xK : K := ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩
  have hmonic : (P.map (Polynomial.eval₂RingHom (Int.castRingHom K) xK)).Monic := hP.map _
  have hcomp : (algebraMap K F).comp (Polynomial.eval₂RingHom (Int.castRingHom K) xK) =
      Polynomial.eval₂RingHom (Int.castRingHom F) x := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl
  have haeval : Polynomial.aeval y (P.map (Polynomial.eval₂RingHom (Int.castRingHom K) xK)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
    exact hxy
  have hint : IsIntegral K y := ⟨_, hmonic, by rwa [← Polynomial.aeval_def]⟩
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic (minpoly.dvd K y haeval) ?_
  rw [hP.natDegree_map, ← IntermediateField.adjoin.finrank hint]
  exact hdeg
