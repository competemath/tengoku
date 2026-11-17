import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_quotient
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_forall_quotient
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_isFlatAt_of_forall_quotient
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_flatCondition_of_forall_quotient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_flatCondition_of_forall_quotient

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      GaloisRep.flatCondition 𝒪 p S
        (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective))) :
    GaloisRep.flatCondition 𝒪 p S ρ :=
  ⟨GaloisRepAdic.detIsCyclotomic_of_forall_quotient ρ (fun m => (h m).1),
   GaloisRepAdic.isFlatAt_of_forall_quotient ρ (fun m => (h m).2.1),
   fun q hq hqS =>
     GaloisRepAdic.isUnramifiedAt_of_forall_quotient ρ (fun m => (h m).2.2 q hq hqS)⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
