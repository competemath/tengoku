import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_FontaineHodge
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

/--
@isnad1 id=ex.3h6v.s9.8c01a6424778 from=translated src=- shape=a2340ad7 vocab=6195bf92
-/
theorem Deformation.TruncWitt.exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer
    {ℛ : Type u} [CommRing ℛ] (p : ℕ) [Fact p.Prime]
    {A : Type v} [CommRing A] (π : ℛ →+* A) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    {n : ℕ} {u : TruncatedWittVector p n A}
    (hu : Deformation.TruncWitt.frobeniusFun u ∈ Deformation.TruncWitt.fontaineKer p n π) :
    ∃ b : TruncatedWittVector p (n + 1) A,
      b ∈ Deformation.TruncWitt.fontaineKer p (n + 1) π ∧
      TruncatedWittVector.truncate (Nat.le_succ n) b = u := by exact @_root_.P2MW.S_Deformation_TruncWitt_exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer.solution ℛ _ p _ A _ π hπ hker n u hu
