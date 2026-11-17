import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_wittHom_nsmul_eq_zero_of_forall_convPow_eq_one

set_option autoImplicit false

open _root_.Function open _root_.Deformation open _root_.Deformation.TruncWitt

universe u v

namespace Deformation
export _root_.Deformation (TruncWitt.map_id wittHom map_convMul_of_mem_wittHom map_counit_of_mem_wittHom)
namespace WittHomExponent
open _root_.Deformation

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A]

/--
@isnad1 id=eq.0h5v.s9.d7f0d445681c from=translated src=- shape=cd3f19b6 vocab=22300169
-/
theorem map_convOne (x : wittHom R p n A) :
    map (1 : WithConv (A →ₐ[R] A)).ofConv.toRingHom (x : TruncatedWittVector p n A) = 0 := by
  have hfac : (1 : WithConv (A →ₐ[R] A)).ofConv.toRingHom =
      (algebraMap R A).comp (Bialgebra.counitAlgHom R A).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp [AlgHom.convOne_apply]
  rw [hfac, ← map_map, map_counit_of_mem_wittHom x.2, map_zero]

/--
@isnad1 id=eq.0h6v.s9.2d9049725d63 from=translated src=- shape=54a9c5da vocab=830ae0a7
-/
theorem map_convPow_id (x : wittHom R p n A) (k : ℕ) :
    map ((WithConv.toConv (AlgHom.id R A)) ^ k).ofConv.toRingHom (x : TruncatedWittVector p n A) =
      k • (x : TruncatedWittVector p n A) := by
  induction k with
  | zero => rw [pow_zero, zero_smul, map_convOne]
  | succ k ih =>
    rw [pow_succ, map_convMul_of_mem_wittHom x.2, ih, add_smul, one_smul]
    congr 1
    exact TruncWitt.map_id _

/--
@isnad1 id=eq.1h6v.s10.a8f0c8524711 from=translated src=- shape=92121737 vocab=ee188c32
-/
theorem main (m : ℕ)
    (hA : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (A →ₐ[R] T)), f ^ m = 1)
    (x : wittHom R p n A) : m • x = 0 := by
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, ← map_convPow_id x m,
    hA A (WithConv.toConv (AlgHom.id R A)), map_convOne]

end Deformation.WittHomExponent

/--
@isnad1 id=eq.1h6v.s10.a8f0c8524711 from=translated src=- shape=92121737 vocab=ee188c32
-/
theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] (m : ℕ)
    (hA : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (A →ₐ[R] T)), f ^ m = 1)
    (x : Deformation.wittHom R p n A) : m • x = 0 :=
  Deformation.WittHomExponent.main m hA x
