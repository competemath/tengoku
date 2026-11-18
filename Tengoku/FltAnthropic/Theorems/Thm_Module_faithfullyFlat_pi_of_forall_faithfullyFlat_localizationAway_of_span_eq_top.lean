import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=faithful.2h4v.s8.28dcfae9b651 from=translated src=- shape=c83f9981 vocab=ec03f4d1
-/
theorem Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (S' : Fin k → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra S (S' i)]
    [∀ i, Algebra (Localization.Away (r i)) (S' i)] [∀ i, IsScalarTower S (Localization.Away (r i)) (S' i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (r i)) (S' i)) :
    Module.FaithfullyFlat S (∀ i : Fin k, S' i) := by exact @_root_.P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top.solution S _ k r hr S' _ _ _ _ hff
