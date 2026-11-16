import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Topology

/--
@isnad1 id=ex.3h4v.s10.57263aa03a5f from=translated src=- shape=5e061b86 vocab=4c0ebc4c
-/
theorem Algebra.exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
    (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (hsm : Algebra.Smooth ℂ S)
    {n : ℕ} (hrank : Module.rank S (KaehlerDifferential ℂ S) = n)
    (σ₀ : S →ₐ[ℂ] ℂ) (t : Fin n → S)
    (hdt : (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) ⊔
        Submodule.span S (Set.range fun i : Fin n => KaehlerDifferential.D ℂ S (t i)) = ⊤) :
    ∃ g : S, σ₀ g ≠ 0 ∧
      letI : Algebra (MvPolynomial (Fin n) ℂ) (Localization.Away g) :=
        ((algebraMap S (Localization.Away g)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
      Algebra.IsStandardEtale (MvPolynomial (Fin n) ℂ) (Localization.Away g) := by exact @_root_.P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.solution S _ _ _ _ hsm n hrank σ₀ t hdt
