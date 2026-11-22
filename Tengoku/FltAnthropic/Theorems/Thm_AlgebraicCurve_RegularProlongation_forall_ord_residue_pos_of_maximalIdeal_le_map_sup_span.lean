import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RegularProlongation
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

/--
@isnad1 id=and.8h10v.s12.b7f6a8328ed4 from=translated src=- shape=9c6f4d42 vocab=983efcd4
-/
theorem AlgebraicCurve.RegularProlongation.forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : Place (ResidueField A) Fbar)
    (N₀ N₁ : Subring F) [IsLocalRing ↥N₀] [IsLocalRing ↥N₁] (h01 : N₀ ≤ N₁)
    (hN₁ : ∀ f : F, f ∈ N₁ → f ∈ R.integers)
    (hreg₀ : ∀ (f : ↥N₀) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < x.ord (R.residue ⟨f, h⟩)))
    (hreg₁ : ∀ (f : ↥N₁) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩))
    (w : F) (hw : w ∈ N₁) (hwres : ∀ h : w ∈ R.integers, R.residue ⟨w, h⟩ = 0)
    (hmax : maximalIdeal ↥N₁ ≤ (maximalIdeal ↥N₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨w, hw⟩}) :
    ∀ (f : ↥N₁) (h : (f : F) ∈ R.integers), 0 ≤ x.ord (R.residue ⟨f, h⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h⟩ ≠ 0 → 0 < x.ord (R.residue ⟨f, h⟩)) := by exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_forall_ord_residue_pos_of_maximalIdeal_le_map_sup_span.solution L _ A F _ _ Fbar _ _ R x N₀ N₁ _ _ h01 hN₁ hreg₀ hreg₁ w hw hwres hmax
