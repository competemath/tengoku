import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.2h5v.s10.ec481338dd25 from=translated src=- shape=d43f8826 vocab=93ab98ed
-/
theorem Localization.localRingHom_surjective_and_ker_eq_map_of_surjective
    {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (hpq : p = Ideal.comap f q) :
    Function.Surjective (Localization.localRingHom p q f hpq) ∧
      RingHom.ker (Localization.localRingHom p q f hpq) =
        Ideal.map (algebraMap A (Localization.AtPrime p)) (RingHom.ker f) := by exact @_root_.P2MW.S_Localization_localRingHom_surjective_and_ker_eq_map_of_surjective.solution A B _ _ f hf p _ q _ hpq
