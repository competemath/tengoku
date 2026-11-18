import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_Order
import Tengoku.FltAnthropic.Theorems.Thm_QuaternionAlgebra_IsOrder_finrank_eq_four

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_QuaternionAlgebra_IsOrder_exists_basis_span_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_basis_span_eq

set_option autoImplicit false

open scoped Quaternion

/--
@isnad1 id=ex.1h3v.s9.99f74119139a from=translated src=- shape=0191eec5 vocab=6df6e10c
-/
theorem solution {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) :
    ∃ B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b], (∀ i, B i ∈ Λ) ∧ Submodule.span ℤ (Set.range B) = Λ := by
  haveI : Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩
  haveI : Module.Free ℤ Λ := Submodule.IsLattice.free ℚ Λ
  haveI : Module.Finite ℤ Λ := Submodule.IsLattice.finite ℚ Λ
  let Bz : Module.Basis (Fin 4) ℤ Λ := (Module.finBasis ℤ Λ).reindex (finCongr hΛ.finrank_eq_four)
  refine ⟨Bz.extendOfIsLattice ℚ, fun i => ?_, ?_⟩
  · rw [Module.Basis.extendOfIsLattice_apply]; exact (Bz i).2
  · have hrng : Set.range (Bz.extendOfIsLattice ℚ) = Λ.subtype '' Set.range Bz := by
      ext y
      simp only [Set.mem_range, Set.mem_image, Module.Basis.extendOfIsLattice_apply]
      exact ⟨fun ⟨i, hi⟩ => ⟨Bz i, ⟨i, rfl⟩, hi⟩, fun ⟨z, ⟨i, hi⟩, hz⟩ => ⟨i, hi ▸ hz⟩⟩
    rw [hrng, ← Submodule.map_span, Bz.span_eq, Submodule.map_top, Submodule.range_subtype]
