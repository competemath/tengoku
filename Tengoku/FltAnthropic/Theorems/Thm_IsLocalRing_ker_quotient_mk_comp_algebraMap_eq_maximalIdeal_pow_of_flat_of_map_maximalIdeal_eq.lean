import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.1h3v.s10.3715829da96c from=translated src=- shape=40c564be vocab=01254d74
-/
theorem IsLocalRing.ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S) (k : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ k)).comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R ^ k := by exact @_root_.P2MW.S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq.solution R S _ _ _ _ _ _ _ hmax k
