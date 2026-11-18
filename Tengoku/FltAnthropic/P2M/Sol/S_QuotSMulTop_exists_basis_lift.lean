import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
import Tengoku.Seed.RingTheory.Regular.RegularSequence
import Tengoku.FltAnthropic.Theorems.Thm_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top
import Tengoku.FltAnthropic.Theorems.Thm_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_QuotSMulTop_exists_basis_lift.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_QuotSMulTop_exists_basis_lift

open scoped Pointwise

/--
@isnad1 id=ex.2h5v.s10.0ef3dfd34b53 from=translated src=- shape=54f0c551 vocab=ef94da79
-/
theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (b : Module.Basis ι (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    ∃ b' : Module.Basis ι R M,
      ∀ i, (Submodule.Quotient.mk (b' i) : QuotSMulTop x M) = b i := by
  choose m hm using fun i =>
    Submodule.Quotient.mk_surjective (x • ⊤ : Submodule R M) (b i)
  have hmk_eq : (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⇑b := funext hm
  have hli : LinearIndependent (R ⧸ Ideal.span {x})
      (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) := by
    rw [hmk_eq]; exact b.linearIndependent
  have hspan : Submodule.span (R ⧸ Ideal.span {x})
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤ := by
    rw [hmk_eq]; exact b.span_eq
  have hli' : LinearIndependent R m :=
    QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent x hx hreg m hli
  have hspan' : Submodule.span R (Set.range m) = ⊤ :=
    QuotSMulTop.span_eq_top_of_span_quotientMk_eq_top x hx m hspan
  refine ⟨Module.Basis.mk hli' hspan'.ge, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact hm i
