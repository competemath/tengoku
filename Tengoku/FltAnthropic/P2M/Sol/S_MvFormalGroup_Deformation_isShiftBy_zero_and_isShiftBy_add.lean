import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_IsShiftBy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvFormalGroup_Deformation_isShiftBy_zero_and_isShiftBy_add

set_option autoImplicit false

open IsLocalRing Tengoku.FltAnthropic.MvFormalGroup

/--
@isnad1 id=and.3h11v.s16.ee99ec809f85 from=translated src=- shape=aecc7134 vocab=f087e91a
-/
theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w w' : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' G'' : Deformation (F.map (algebraMap B B₁)) B) :
    Deformation.IsShiftBy V ι F 0 G G ∧
      (Deformation.IsShiftBy V ι F w G G' → Deformation.IsShiftBy V ι F w' G' G'' →
        Deformation.IsShiftBy V ι F (w + w') G G'') := by
  classical
  refine ⟨?_, ?_⟩
  ·
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro ξ; simp
    · intro l; simp
  · rintro ⟨n, v, z, zl, hzl, hw, hG⟩ ⟨m, v', z', zl', hzl', hw', hG'⟩
    refine ⟨n + m, Fin.append v v', Fin.append z z', Fin.append zl zl', ?_, ?_, ?_⟩
    · intro i l
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hzl i l
      · simpa only [Fin.append_right] using hzl' j l
    · intro ξ
      rw [LinearMap.add_apply, hw ξ, hw' ξ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    · intro l
      rw [hG' l, hG l, Fin.sum_univ_add, add_assoc]
      simp only [Fin.append_left, Fin.append_right]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
