import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed

set_option autoImplicit false

universe u

open scoped TensorProduct

/--
@isnad1 id=iff.0h5v.s9.cb6812edcf2a from=translated src=- shape=7769ab4e vocab=859ee980
-/
theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime] :
    Algebra.IsUnramifiedAt A P ↔
      ¬ ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L) ≤ P) := by

  haveI : (P.under A).IsPrime := Ideal.IsPrime.under A P
  let q : PrimeSpectrum ((P.under A).Fiber B) :=
    PrimeSpectrum.preimageEquivFiber A B ⟨P.under A, inferInstance⟩
      ⟨⟨P, inferInstance⟩, rfl⟩
  have hq : P = q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom := by
    have h := (PrimeSpectrum.preimageEquivFiber A B ⟨P.under A, inferInstance⟩).symm_apply_apply
      ⟨⟨P, inferInstance⟩, rfl⟩
    have h' := congrArg (fun x => x.1.asIdeal) h
    exact h'.symm
  rw [Algebra.isUnramifiedAt_iff_isUnramifiedAt_fiber (P.under A) P q.asIdeal hq,
    Algebra.isUnramifiedAt_iff_exists_notMem_forall_dual_eq_trace_of_field
      (P.under A).ResidueField ((P.under A).Fiber B) q.asIdeal,
    ← Algebra.exists_notMem_forall_dual_eq_trace_iff_fiber (P.under A) P q.asIdeal hq,
    Algebra.not_comap_one_div_traceDual_le_iff_exists_notMem_forall_dual_eq_trace A K B L P]
