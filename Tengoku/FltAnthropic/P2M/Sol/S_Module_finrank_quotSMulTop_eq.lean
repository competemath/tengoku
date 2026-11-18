import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.FltAnthropic.Theorems.Thm_QuotSMulTop_exists_basis_lift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_finrank_quotSMulTop_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_finrank_quotSMulTop_eq

open scoped Pointwise

/--
@isnad1 id=eq.3h3v.s9.d4f1c6e78d78 from=translated src=- shape=26cbee0f vocab=ba99a407
-/
theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.finrank (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = Module.finrank R M := by
  haveI := hfree
  haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx) :
          Ideal.span {x} ≤ IsLocalRing.maximalIdeal R)))
  haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
    Module.Finite.of_restrictScalars_finite R _ _
  haveI : Fintype (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
    Module.Free.ChooseBasisIndex.fintype _ _
  obtain ⟨b', -⟩ := QuotSMulTop.exists_basis_lift x hx hreg
    (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
  rw [Module.finrank_eq_card_basis b',
    Module.finrank_eq_card_basis
      (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))]
