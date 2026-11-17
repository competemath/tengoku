import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Ideal.exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
    {S B : Type} [CommRing S] [CommRing B] (φ : S →+* B) (𝔭 : Ideal S) [𝔭.IsPrime]
    (Bₚ : Type) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bₚ]
    (J₁ J₂ : Ideal B) (h₁ : J₁.FG) (h₂ : J₂.FG)
    (h : J₁.map (algebraMap B Bₚ) = J₂.map (algebraMap B Bₚ)) :
    ∃ g : S, g ∉ 𝔭 ∧
      ∀ (B' : Type) [CommRing B'] [Algebra B B'] [IsLocalization.Away (φ g) B'],
        J₁.map (algebraMap B B') = J₂.map (algebraMap B B') := by exact @_root_.P2MW.S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg.solution S B _ _ φ 𝔭 _ Bₚ _ _ _ J₁ J₂ h₁ h₂ h
