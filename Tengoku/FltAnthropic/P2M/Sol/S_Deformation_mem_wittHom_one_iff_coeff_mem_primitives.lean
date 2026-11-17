import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_ModpRealization
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_mem_wittHom_one_iff_coeff_mem_primitives.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_mem_wittHom_one_iff_coeff_mem_primitives

set_option autoImplicit false

open _root_.Function open _root_.Deformation open _root_.Deformation.TruncWitt
open scoped TensorProduct

universe u v

namespace Deformation
export _root_.Deformation (wittHom mem_wittHom_iff)
namespace WittHomLevelOne
open _root_.Deformation

variable {p : ℕ} [Fact p.Prime]

/--
@isnad1 id=eq.0h4v.s7.31bac3c04915 from=translated src=- shape=c25f7f92 vocab=048cfc75
-/
theorem coeff_zero_add {S : Type v} [CommRing S] (a b : TruncatedWittVector p 1 S) :
    (a + b).coeff 0 = a.coeff 0 + b.coeff 0 := by
  obtain ⟨a, rfl⟩ := WittVector.truncate_surjective p 1 S a
  obtain ⟨b, rfl⟩ := WittVector.truncate_surjective p 1 S b
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero a b

omit [Fact p.Prime] in
theorem eq_iff_coeff_zero {S : Type v} [CommRing S] (a b : TruncatedWittVector p 1 S) :
    a = b ↔ a.coeff 0 = b.coeff 0 := by
  refine ⟨fun h => h ▸ rfl, fun h => TruncatedWittVector.ext fun i => ?_⟩
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  exact h

/--
@isnad1 id=iff.0h4v.s8.da34d1d35e73 from=translated src=- shape=677e795f vocab=dd563698
-/
theorem main (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] (x : TruncatedWittVector p 1 A) :
    x ∈ wittHom k p 1 A ↔ x.coeff 0 ∈ primitives k A := by
  rw [mem_wittHom_iff, eq_iff_coeff_zero, coeff_zero_add, coeff_map, coeff_map, coeff_map,
    primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub,
    sub_eq_zero]
  change Coalgebra.comul (R := k) (x.coeff 0) = x.coeff 0 ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] x.coeff 0 ↔
    Coalgebra.comul (R := k) (x.coeff 0) = x.coeff 0 ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] x.coeff 0
  exact Iff.rfl

end Deformation.WittHomLevelOne

/--
@isnad1 id=iff.0h4v.s8.da34d1d35e73 from=translated src=- shape=677e795f vocab=dd563698
-/
theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] (x : TruncatedWittVector p 1 A) :
    x ∈ Deformation.wittHom k p 1 A ↔ x.coeff 0 ∈ primitives k A :=
  Deformation.WittHomLevelOne.main k p A x
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
