import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.2h4v.s9.3fa14d2c929e from=translated src=- shape=abda943b vocab=39e67917
-/
theorem Ideal.exists_map_mk_span_singleton_eq_span_of_not_mem_smul
    {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} (g : Fin (n + 1) → R)
    (x : R) (hx : x ∈ Ideal.span (Set.range g))
    (hxm : x ∉ IsLocalRing.maximalIdeal R • Ideal.span (Set.range g)) :
    ∃ g' : Fin n → R ⧸ Ideal.span ({x} : Set R),
      (Ideal.span (Set.range g)).map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = Ideal.span (Set.range g') := by exact @_root_.P2MW.S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul.solution R _ _ n g x hx hxm
