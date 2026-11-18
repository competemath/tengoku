import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.FltAnthropic.Theorems.Thm_QuotSMulTop_exists_basis_lift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_free_of_quotSMulTop_free.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_free_of_quotSMulTop_free

open scoped Pointwise

/--
@isnad1 id=free.3h3v.s9.3831d96f009d from=translated src=- shape=ea513e22 vocab=9c26f410
-/
theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Free R M := by
  haveI := hfree
  haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
    Module.Finite.of_restrictScalars_finite R _ _
  haveI : Fintype (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
    Module.Free.ChooseBasisIndex.fintype _ _
  obtain ⟨b', -⟩ := QuotSMulTop.exists_basis_lift x hx hreg
    (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
  exact Module.Free.of_basis b'
