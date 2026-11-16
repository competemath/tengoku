import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem Ideal.map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul
    {P : Type u} [CommRing P] [IsNoetherianRing P] (J : Ideal P) (𝔫 : Ideal P) [𝔫.IsPrime]
    {ι : Type v} (h : ι → P) (hh : ∀ i, h i ∈ J)
    (hle : J ≤ Ideal.span (Set.range h) ⊔ 𝔫 * J) :
    Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J =
      Ideal.span (Set.range fun i => algebraMap P (Localization.AtPrime 𝔫) (h i)) := by exact @_root_.P2MW.S_Ideal_map_algebraMap_localizationAtPrime_eq_span_of_le_span_sup_mul.solution P _ _ J 𝔫 _ ι h hh hle
