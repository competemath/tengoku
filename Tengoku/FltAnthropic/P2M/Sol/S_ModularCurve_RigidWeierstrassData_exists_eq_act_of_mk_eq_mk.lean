import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk

set_option autoImplicit false

open ModularCurve

/--
@isnad1 id=ex.1h5v.s6.5df3fab8b07c from=translated src=- shape=5686f1f3 vocab=dca93018
-/
theorem solution
    {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] (x y : R.Raw T)
    (h : (Quot.mk _ x : R.Pt T) = Quot.mk _ y) :
    ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x := by
  have hequiv : Equivalence (R.Rel (T := T)) :=
    { refl := fun a => ModularCurve.RigidWeierstrassData.Rel.refl R a
      symm := by
        rintro a b ⟨C, rfl⟩
        refine ⟨C⁻¹, ?_⟩
        rw [← R.act_mul, inv_mul_cancel, R.act_one]
      trans := fun h₁ h₂ => ModularCurve.RigidWeierstrassData.Rel.trans R h₁ h₂ }
  have h' : Relation.EqvGen (R.Rel (T := T)) x y := Quot.eqvGen_exact h
  exact (hequiv.eqvGen_iff).mp h'
