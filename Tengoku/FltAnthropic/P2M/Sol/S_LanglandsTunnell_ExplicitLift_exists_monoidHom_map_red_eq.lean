import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_ExplicitLift_map_red_injOn_closure
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace LanglandsTunnell
export _root_.LanglandsTunnell (ExplicitLift.map_red_injOn_closure ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero)
namespace ExplicitLift
export _root_.LanglandsTunnell.ExplicitLift (map_red_injOn_closure exists_mem_closure_map_red_eq_of_det_ne_zero)
namespace SEC
open _root_.LanglandsTunnell.ExplicitLift open _root_.LanglandsTunnell

open FLT.ExplicitLift

abbrev G48 : Submonoid (Matrix (Fin 2) (Fin 2) (ℤ√(-2))) :=
  Submonoid.closure ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))

noncomputable def lift (g : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) :=
  (LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (g.det_ne_zero)).choose

/--
@isnad1 id=mem.0h1v.s8.2a32a7057b4d from=translated src=- shape=7082daea vocab=1c9d4062
-/
theorem lift_mem (g : GL (Fin 2) (ZMod 3)) : lift g ∈ G48 :=
  (LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (g.det_ne_zero)).choose_spec.1

/--
@isnad1 id=eq.0h1v.s8.97c0985134fa from=translated src=- shape=f3b4fc01 vocab=e48dc882
-/
theorem lift_map (g : GL (Fin 2) (ZMod 3)) :
    (lift g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  (LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (g.det_ne_zero)).choose_spec.2

/--
@isnad1 id=eq.0h2v.s9.22e8e46c664c from=translated src=- shape=6da1db62 vocab=457f01a9
-/
theorem map_mul_red (A B : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) :
    (A * B).map red = A.map red * B.map red := Matrix.map_mul

/--
@isnad1 id=eq.0h0v.s8.3a449907f2ce from=translated src=- shape=27d6b6e9 vocab=ca6ea429
-/
theorem lift_one : lift 1 = 1 := by
  apply LanglandsTunnell.ExplicitLift.map_red_injOn_closure (lift_mem 1) (Submonoid.one_mem _)
  show (lift 1).map red = (1 : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).map red
  rw [lift_map, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]

/--
@isnad1 id=eq.0h2v.s9.b99702443055 from=translated src=- shape=f25289d7 vocab=24be6cba
-/
theorem lift_mul (g h : GL (Fin 2) (ZMod 3)) : lift (g * h) = lift g * lift h := by
  apply LanglandsTunnell.ExplicitLift.map_red_injOn_closure (lift_mem (g * h))
    (Submonoid.mul_mem _ (lift_mem g) (lift_mem h))
  show (lift (g * h)).map red = (lift g * lift h).map red
  rw [map_mul_red, lift_map, lift_map, lift_map, Units.val_mul]

noncomputable def liftUnit (g : GL (Fin 2) (ZMod 3)) : GL (Fin 2) (ℤ√(-2)) where
  val := lift g
  inv := lift g⁻¹
  val_inv := by rw [← lift_mul, mul_inv_cancel, lift_one]
  inv_val := by rw [← lift_mul, inv_mul_cancel, lift_one]

noncomputable def psi : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)) where
  toFun := liftUnit
  map_one' := Units.ext lift_one
  map_mul' g h := Units.ext (lift_mul g h)

/--
@isnad1 id=eq.0h1v.s10.91b78b7ef0dd from=translated src=- shape=36d2bbd5 vocab=8f00f272
-/
theorem map_red_psi (g : GL (Fin 2) (ZMod 3)) : Matrix.GeneralLinearGroup.map red (psi g) = g := by
  apply Units.ext
  change red.mapMatrix (lift g) = (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
  rw [RingHom.mapMatrix_apply, lift_map]

/--
@isnad1 id=mem.0h1v.s10.8cfa43a8c153 from=translated src=- shape=5af27968 vocab=ca43de92
-/
theorem psi_mem (g : GL (Fin 2) (ZMod 3)) : ((psi g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) ∈ G48 :=
  lift_mem g

end LanglandsTunnell.ExplicitLift.SEC

open LanglandsTunnell.ExplicitLift.SEC in
/--
@isnad1 id=ex.0h0v.s12.1971e6d58984 from=translated src=- shape=b89047c8 vocab=665ac07f
-/
theorem solution :
    ∃ Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)),
      (∀ g : GL (Fin 2) (ZMod 3), Matrix.GeneralLinearGroup.map FLT.ExplicitLift.red (Ψ g) = g) ∧
      (∀ g : GL (Fin 2) (ZMod 3), ((Ψ g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) ∈
        Submonoid.closure
          ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) :=
  ⟨psi, map_red_psi, psi_mem⟩

end
