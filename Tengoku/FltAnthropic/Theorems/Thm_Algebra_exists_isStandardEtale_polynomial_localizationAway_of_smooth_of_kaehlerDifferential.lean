import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Topology Polynomial

/--
@isnad1 id=ex.3h3v.s9.fc108748dd63 from=translated src=- shape=0c4de60c vocab=fc062254
-/
theorem Algebra.exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : S)
    (hdt : KaehlerDifferential.D ℂ S t ∉ (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S))) :
    ∃ (g : S), σ₀ g ≠ 0 ∧
      letI : Algebra (Polynomial ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (Polynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (Polynomial ℂ) (Localization.Away g) := by exact @_root_.P2MW.S_Algebra_exists_isStandardEtale_polynomial_localizationAway_of_smooth_of_kaehlerDifferential.solution S _ _ _ _ hsm hrank σ₀ t hdt
