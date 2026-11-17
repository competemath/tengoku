import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FiniteField_nonempty_algEquiv_of_card_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FiniteField_nonempty_algEquiv_of_card_eq

set_option autoImplicit false

/--
@isnad1 id=nonempty.1h3v.s6.721b01e97ee3 from=translated src=- shape=df40dbf6 vocab=5c184d20
-/
theorem solution
    (K : Type) [Field K] (L₁ : Type) [Field L₁] [Algebra K L₁] [Finite L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [Finite L₂]
    (h : Nat.card L₁ = Nat.card L₂) :
    Nonempty (L₁ ≃ₐ[K] L₂) := by
  classical
  haveI := Fintype.ofFinite L₁
  haveI := Fintype.ofFinite L₂
  have h' : Fintype.card L₁ = Fintype.card L₂ := by
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  haveI i₁ : Polynomial.IsSplittingField K L₁ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) :=
    FiniteField.isSplittingField_sub L₁ K
  haveI i₂ : Polynomial.IsSplittingField K L₂ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X) := by
    rw [h']; exact FiniteField.isSplittingField_sub L₂ K
  exact ⟨(Polynomial.IsSplittingField.algEquiv L₁ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).trans
    (Polynomial.IsSplittingField.algEquiv L₂ (Polynomial.X ^ Fintype.card L₁ - Polynomial.X)).symm⟩
