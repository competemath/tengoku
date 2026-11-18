import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=uniquefa.0h2v.s7.55e61e3d4098 from=translated src=- shape=32afb571 vocab=5ea40d8e
-/
theorem IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    UniqueFactorizationMonoid A := by exact @_root_.P2MW.S_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient.solution A _ _ _ _ t _ _
