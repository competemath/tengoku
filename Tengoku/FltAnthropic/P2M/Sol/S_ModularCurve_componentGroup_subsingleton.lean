import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_componentGroup_subsingleton.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_componentGroup_subsingleton

open ModularCurve Finset

private theorem aux_charLat_subsingleton {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 1) :
    Subsingleton (characterLattice ι) := by
  constructor
  rintro ⟨D, hD⟩ ⟨D', hD'⟩
  rw [mem_characterLattice] at hD hD'
  ext x
  have hx : ∀ y : ι, y = x := fun y => Fintype.card_le_one_iff.mp hι y x
  have hsum : ∀ E : ι → ℤ, ∑ y : ι, E y = E x := fun E => by
    rw [Finset.sum_eq_single x (fun y _ hy => absurd (hx y) hy)
        (fun h => absurd (Finset.mem_univ x) h)]
  simp only [hsum] at hD hD'
  simp [hD, hD']

theorem solution {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 1) (e : ι → ℕ) :
    Subsingleton (componentGroup e) := by
  have h𝒳 := aux_charLat_subsingleton (ι := ι) hι
  have hdual : Subsingleton (Module.Dual ℤ (characterLattice ι)) :=
    ⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact Quotient.instSubsingletonQuotient _
