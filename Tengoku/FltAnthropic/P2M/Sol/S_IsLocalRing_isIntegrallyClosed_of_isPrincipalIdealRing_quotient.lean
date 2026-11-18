import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_isIntegrallyClosed_of_isPrincipalIdealRing_quotient

/--
@isnad1 id=isintegr.0h2v.s6.3a27a2cbca2c from=translated src=- shape=32afb571 vocab=26a198c7
-/
theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    IsIntegrallyClosed A := by
  haveI := IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient t
  haveI : Nonempty (GCDMonoid A) := ⟨UniqueFactorizationMonoid.toGCDMonoid A⟩
  infer_instance
