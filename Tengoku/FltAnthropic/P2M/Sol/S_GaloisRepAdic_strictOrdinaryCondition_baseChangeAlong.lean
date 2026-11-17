import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_StrictOrdinary
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_isStrictOrdinaryAt_baseChangeAlong
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_isUnramifiedAt_baseChangeAlong

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_strictOrdinaryCondition_baseChangeAlong

set_option autoImplicit false

/--
@isnad1 id=strictor.2h7v.s7.abf881e2ae02 from=translated src=- shape=07c16804 vocab=ba678ac1
-/
theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.strictOrdinaryCondition 𝒪 p S ρ) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) :=
  ⟨GaloisRepAdic.detIsCyclotomic_baseChangeAlong φ hφ ρ h.1,
    GaloisRepAdic.isStrictOrdinaryAt_baseChangeAlong φ hφ ρ h.2.1,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_baseChangeAlong φ hφ ρ (h.2.2 q hq hqS)⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
