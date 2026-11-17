import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_isFlatAt_of_isEquiv
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_isEquiv
import Tengoku.FltAnthropic.Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_isEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_flatCondition_of_isEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_flatCondition_of_isEquiv

/--
@isnad1 id=flatcond.2h6v.s6.71deb8b01340 from=translated src=- shape=8d952400 vocab=a58c7a13
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.flatCondition 𝒪 p S ρ₁) : GaloisRep.flatCondition 𝒪 p S ρ₂ :=
  ⟨GaloisRepAdic.detIsCyclotomic_of_isEquiv e h.1, GaloisRepAdic.isFlatAt_of_isEquiv e h.2.1,
    fun q hq hqS => GaloisRepAdic.isUnramifiedAt_of_isEquiv e (h.2.2 q hq hqS)⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
