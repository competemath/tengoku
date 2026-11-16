import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_ConstantReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_ConstantReduction_placeMap_surjective.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_ConstantReduction_placeMap_surjective

open _root_.AlgebraicCurve open _root_.IsLocalRing

namespace AlgebraicCurve
export _root_.AlgebraicCurve (ConstantReduction Place HasPrincipalDivisors HasPrincipalDivisors.exists_divisor)
namespace ConstantReduction
export _root_.AlgebraicCurve.ConstantReduction (placeMap residue residue_surjective mapDomain_placeMap)
namespace W7B2A
open _root_.AlgebraicCurve.ConstantReduction open _root_.AlgebraicCurve

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_not_mem_place {K E : Type*} [Field K] [Field E] [Algebra K E] (Q : Place K E) :
    ∃ u : E, u ∉ Q.toValuationSubring := by
  by_contra h
  exact Q.ne_top' (eq_top_iff.mpr fun x _ => by_contra fun hx => h ⟨x, hx⟩)

theorem ord_ne_zero_of_not_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    {f : E} (hf : f ∉ v.toValuationSubring) : v.ord f ≠ 0 := by
  intro h0
  have hf0 : f ≠ 0 := fun h => hf (h ▸ v.toValuationSubring.zero_mem)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h0, zpow_zero, mul_one] at hu
  exact hf (hu ▸ (u : v.toValuationSubring).2)

theorem placeMap_surjective' (R : ConstantReduction A F Fbar) [HasPrincipalDivisors L F] :
    Function.Surjective R.placeMap := by
  classical
  intro Q
  obtain ⟨u, hu⟩ := exists_not_mem_place Q
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Q.toValuationSubring.zero_mem)
  obtain ⟨f, hf⟩ := R.residue_surjective u
  have hres : R.residue f ≠ 0 := by rw [hf]; exact hu0
  have hf0 : (f : F) ≠ 0 := by
    intro h
    apply hres
    rw [show f = 0 from Subtype.ext h, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (f : F) hf0
  have key := R.mapDomain_placeMap f hres D hD Q
  have hne : Finsupp.mapDomain R.placeMap D Q ≠ 0 := by
    rw [key, hf]; exact ord_ne_zero_of_not_mem Q hu
  have hmem : Q ∈ (Finsupp.mapDomain R.placeMap D).support := Finsupp.mem_support_iff.mpr hne
  obtain ⟨P, -, hP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  exact ⟨P, hP⟩

end AlgebraicCurve.ConstantReduction.W7B2A

open AlgebraicCurve.ConstantReduction.W7B2A in
theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [HasPrincipalDivisors L F] :
    Function.Surjective R.placeMap :=
  placeMap_surjective' R
