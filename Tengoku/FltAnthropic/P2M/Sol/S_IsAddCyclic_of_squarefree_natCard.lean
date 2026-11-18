import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsAddCyclic_of_squarefree_natCard.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsAddCyclic_of_squarefree_natCard

set_option autoImplicit false

theorem solution
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by
  haveI : Finite A := Nat.finite_of_card_ne_zero hA.ne_zero
  rw [← isCyclic_multiplicative_iff]
  have hM : Squarefree (Nat.card (Multiplicative A)) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  haveI : IsZGroup (Multiplicative A) := IsZGroup.of_squarefree hM
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card (Multiplicative A))
