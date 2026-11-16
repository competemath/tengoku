import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

universe u

/--
@isnad1 id=eq.2h3v.s10.dcd47c554b8e from=translated src=- shape=b1b80146 vocab=972ce573
-/
theorem Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
    {k P S : Type u} [Field k] [CommRing P] [CommRing S] [IsLocalRing P] [IsLocalRing S] [IsNoetherianRing P]
    [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    [Algebra.FormallySmooth k P] [Algebra.FormallySmooth k S] [Module.Finite P Ω[P⁄k]]
    (hPS : Function.Surjective (algebraMap P S))
    (hrank : Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] (S ⊗[P] Ω[P⁄k])) ≤
      Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k])) :
    RingHom.ker (algebraMap P S) = ⊥ := by exact @_root_.P2MW.S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le.solution k P S _ _ _ _ _ _ _ _ _ _ _ _ _ hPS hrank
