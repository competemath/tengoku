import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_CartanDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalGL2_cartanDiag_cartanRel_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LocalGL2_cartanDiag_cartanRel_iff

open Matrix LocalGL2

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {a b a' b' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') :
    LocalGL2.CartanRel (LocalGL2.cartanDiag ϖ a b) (LocalGL2.cartanDiag ϖ a' b')
      ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have h₁ : a = a' := by
      have hI := h.entryIdeal_eq
      rw [LocalGL2.entryIdeal_cartanDiag ϖ hab, LocalGL2.entryIdeal_cartanDiag ϖ hab',
        Ideal.span_singleton_eq_span_singleton] at hI
      exact (LocalGL2.pow_irreducible_associated_iff hϖ).mp hI
    have h₂ : a + b = a' + b' := by
      have hD := h.det_associated
      rw [LocalGL2.cartanDiag_det, LocalGL2.cartanDiag_det] at hD
      exact (LocalGL2.pow_irreducible_associated_iff hϖ).mp hD
    exact ⟨h₁, by omega⟩
  · rintro ⟨rfl, rfl⟩
    exact LocalGL2.CartanRel.refl _
