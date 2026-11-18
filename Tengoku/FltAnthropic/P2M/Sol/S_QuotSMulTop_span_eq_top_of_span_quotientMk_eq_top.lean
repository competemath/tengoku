import Tengoku.Seed.RingTheory.LocalRing.Module
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.RingTheory.Regular.IsSMulRegular
import Tengoku.Seed.RingTheory.Regular.RegularSequence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top

open scoped Pointwise

theorem solution {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [Module.Finite R M] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) {ι : Type*} (m : ι → M) (hspan : Submodule.span (R ⧸ Ideal.span {x}) (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
    Submodule.span R (Set.range m) = ⊤ := by
  have h1 : Submodule.span R
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective,
      hspan, Submodule.restrictScalars_top]
  have h2 : (Submodule.span R (Set.range m)).map
      (Submodule.mkQ (x • ⊤ : Submodule R M)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h1
  rw [Submodule.map_mkQ_eq_top] at h2
  have hjac : Ideal.span {x} ≤ Ideal.jacobson ⊥ :=
    le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac ?_)
  rw [Submodule.ideal_span_singleton_smul, sup_comm, h2]
