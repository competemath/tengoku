import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_characterLattice_free_and_finrank_eq.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_characterLattice_free_and_finrank_eq

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (degreeOn degreeOn_apply characterLattice)
open _root_.ModularCurve

theorem dzl_degreeOn_single {S : Type*} [Fintype S] [DecidableEq S] (s : S) (n : ℤ) :
    degreeOn S (Pi.single s n) = n := by
  simp [degreeOn_apply]

theorem dzl_degreeOn_surjective {S : Type*} [Fintype S] (s₀ : S) :
    Function.Surjective (degreeOn S) := by
  classical
  intro n
  exact ⟨Pi.single s₀ n, dzl_degreeOn_single s₀ n⟩

theorem dzl_finrank_eq_of_nonempty {S : Type*} [Fintype S] (s₀ : S) :
    Module.finrank ℤ (characterLattice S) = Fintype.card S - 1 := by

  have hq : Module.finrank ℤ ((S → ℤ) ⧸ characterLattice S) + Module.finrank ℤ (characterLattice S) =
      Module.finrank ℤ (S → ℤ) :=
    Submodule.finrank_quotient_add_finrank (characterLattice S)
  have h1 : Module.finrank ℤ ((S → ℤ) ⧸ characterLattice S) = Module.finrank ℤ ℤ :=
    LinearEquiv.finrank_eq ((degreeOn S).quotKerEquivOfSurjective (dzl_degreeOn_surjective s₀))
  rw [h1, Module.finrank_self, Module.finrank_pi] at hq
  omega

end ModularCurve

theorem solution (S : Type*) [Fintype S] :
    Module.Free ℤ (ModularCurve.characterLattice S) ∧
      Module.finrank ℤ (ModularCurve.characterLattice S) = Fintype.card S - 1 := by
  refine ⟨inferInstance, ?_⟩
  cases isEmpty_or_nonempty S with
  | inl h =>
    haveI : Subsingleton (ModularCurve.characterLattice S) := inferInstance
    rw [Fintype.card_eq_zero, Module.finrank_zero_of_subsingleton]
  | inr h =>
    obtain ⟨s₀⟩ := h
    exact ModularCurve.dzl_finrank_eq_of_nonempty s₀

