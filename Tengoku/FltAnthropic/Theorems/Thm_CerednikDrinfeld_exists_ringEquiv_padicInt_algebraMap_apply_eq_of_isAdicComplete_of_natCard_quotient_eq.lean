import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.5h4v.s9.17d5de48d622 from=translated src=- shape=f408301f vocab=783e966b
-/
theorem CerednikDrinfeld.exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq
    (r : ℕ) [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] :
    ∃ (e𝒪 : ℤ_[r] ≃+* 𝒪) (eK : ℚ_[r] ≃+* K₀),
      ∀ x : ℤ_[r], algebraMap 𝒪 K₀ (e𝒪 x) = eK (x : ℚ_[r]) := by exact @_root_.P2MW.S_CerednikDrinfeld_exists_ringEquiv_padicInt_algebraMap_apply_eq_of_isAdicComplete_of_natCard_quotient_eq.solution r _ 𝒪 _ _ _ hdvr π hπ hcomplete hres hunr K₀ _ _ _ _
