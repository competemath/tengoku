import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CharacterLatticePairings

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const

set_option autoImplicit false

open ModularCurve ModularCurve.CharacterLattice Finset

namespace DZLTorusAux

variable {S : Type*} [Fintype S] [DecidableEq S]

def dzlE (s₀ s : S) : characterLattice S :=
  ⟨Pi.single s 1 - Pi.single s₀ 1, single_sub_single_mem s s₀⟩

/--
@isnad1 id=eq.0h3v.s7.10985aa78159 from=translated src=- shape=8af80b78 vocab=769d0e20
-/
@[scoped simp]
theorem coe_dzlE (s₀ s : S) : (dzlE s₀ s : S → ℤ) = Pi.single s 1 - Pi.single s₀ 1 := rfl

/--
@isnad1 id=eq.0h3v.s9.c1b197795a20 from=translated src=- shape=c84182cf vocab=9ca99930
-/
theorem sum_smul_dzlE (s₀ : S) (a : characterLattice S) :
    ∑ s, (a : S → ℤ) s • dzlE s₀ s = a := by
  have ha : ∑ s, (a : S → ℤ) s = 0 := mem_characterLattice.1 a.2
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  funext t
  simp only [Finset.sum_apply, Submodule.coe_smul_of_tower, coe_dzlE, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases ht : t = s₀ <;> simp [ht, ha]

variable {G : Type*} [CommGroup G]

/--
@isnad1 id=eq.0h5v.s6.4168bd60e868 from=translated src=- shape=d1c939c5 vocab=02b39f2d
-/
theorem prod_zpow_single (s : S) (n : ℤ) (w : S → G) :
    ∏ t, w t ^ (Pi.single s n : S → ℤ) t = w s ^ n := by
  rw [Fintype.prod_eq_single s fun t ht => by rw [Pi.single_eq_of_ne ht, zpow_zero], Pi.single_eq_same]

/--
@isnad1 id=eq.0h5v.s7.e46eadc137c8 from=translated src=- shape=f57dbe9a vocab=84d21a1e
-/
theorem evalHom_dzlE (s₀ s : S) (w : S → G) : evalHom (dzlE s₀ s) w = w s * (w s₀)⁻¹ := by
  show zpowProd (Pi.single s (1 : ℤ) - Pi.single s₀ 1) w = _
  rw [sub_eq_add_neg, zpowProd_add, zpowProd_neg, zpowProd_def, zpowProd_def, prod_zpow_single,
    prod_zpow_single, zpow_one, zpow_one]

end DZLTorusAux
open scoped _root_.P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.DZLTorusAux

open DZLTorusAux in
/--
@isnad1 id=and.0h2v.s11.f9a9997112f3 from=translated src=- shape=be501231 vocab=9bb6afe7
-/
theorem solution
    (S : Type*) [Fintype S] [Nonempty S] (G : Type*) [CommGroup G] :
    (∀ χ : ModularCurve.characterLattice S →+ Additive G,
        ∃ w : S → G, ∀ a, Additive.toMul (χ a) = ModularCurve.CharacterLattice.evalHom a w) ∧
    (∀ w : S → G, (∀ a : ModularCurve.characterLattice S, ModularCurve.CharacterLattice.evalHom a w = 1) ↔
        ∃ c : G, w = fun _ => c) := by
  classical
  obtain ⟨s₀⟩ := ‹Nonempty S›
  refine ⟨fun χ => ?_, fun w => ⟨fun h => ⟨w s₀, funext fun s => ?_⟩, ?_⟩⟩
  · refine ⟨fun s => Additive.toMul (χ (dzlE s₀ s)), fun a => ?_⟩
    rw [evalHom_apply]
    conv_lhs => rw [← sum_smul_dzlE s₀ a, map_sum, toMul_sum]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zsmul, toMul_zsmul]
  · have hs := h (dzlE s₀ s)
    rw [evalHom_dzlE] at hs
    exact mul_inv_eq_one.mp hs
  · rintro ⟨c, rfl⟩ a
    exact evalHom_const a c
