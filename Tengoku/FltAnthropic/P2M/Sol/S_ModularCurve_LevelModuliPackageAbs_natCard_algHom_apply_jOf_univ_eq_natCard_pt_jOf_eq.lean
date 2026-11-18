import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackage
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LevelModuliPackageAbs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq

set_option autoImplicit false

universe u

open ModularCurve

/--
@isnad1 id=eq.0h5v.s8.1fdbcf9d9197 from=translated src=- shape=5e3a3a19 vocab=e2b68997
-/
theorem solution
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P₀ : LevelModuliPackageAbs A D)
    (T : Type u) [CommRing T] [Algebra A T] (t : T) :
    Nat.card {φ : P₀.B₀ →ₐ[A] T // φ (D.jOf P₀.univ) = t} = Nat.card {x : D.Pt T // D.jOf x = t} := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun φ => ⟨D.map φ.1 P₀.univ, by rw [D.jOf_map]; exact φ.2⟩
      invFun := fun x => ⟨P₀.classify x.1, by rw [← D.jOf_map, P₀.map_classify]; exact x.2⟩
      left_inv := fun φ => ?_
      right_inv := fun x => ?_ }
  · apply Subtype.ext
    exact (P₀.classify_unique _ φ.1 rfl).symm
  · apply Subtype.ext
    exact P₀.map_classify x.1
