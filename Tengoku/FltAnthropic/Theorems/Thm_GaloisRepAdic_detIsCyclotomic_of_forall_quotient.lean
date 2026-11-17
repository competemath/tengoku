import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRepAdic_detIsCyclotomic_of_forall_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRepAdic_detIsCyclotomic_of_forall_quotient.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/--
@isnad1 id=detiscyc.1h3v.s8.32655cb2b575 from=translated src=- shape=3b72bd74 vocab=62be0664
-/
theorem Tengoku.FltAnthropic.GaloisRepAdic.detIsCyclotomic_of_forall_quotient {A : Type} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A) {p : ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)).DetIsCyclotomic p) :
    ρ.DetIsCyclotomic p := by exact @_root_.P2MW.S_GaloisRepAdic_detIsCyclotomic_of_forall_quotient.solution A _ _ _ ρ p h
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
