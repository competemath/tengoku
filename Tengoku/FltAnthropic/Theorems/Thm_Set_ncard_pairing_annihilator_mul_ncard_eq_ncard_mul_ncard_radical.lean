import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {L : Type} [Field L] [CharZero L]
    (A : Set J) (X' : Set J') (hA : A.Finite) (hX' : X'.Finite)
    (hA0 : (0 : J) ∈ A) (hAadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) (hAneg : ∀ x ∈ A, -x ∈ A)
    (hX'0 : (0 : J') ∈ X') (hX'add : ∀ x ∈ X', ∀ y ∈ X', x + y ∈ X') (hX'neg : ∀ x ∈ X', -x ∈ X')
    (B : J → J' → L)
    (hBl : ∀ a ∈ A, ∀ a' ∈ A, ∀ y ∈ X', B (a + a') y = B a y * B a' y)
    (hBr : ∀ a ∈ A, ∀ y ∈ X', ∀ y' ∈ X', B a (y + y') = B a y * B a y') :
    Set.ncard {y : J' | y ∈ X' ∧ ∀ a ∈ A, B a y = 1} * Set.ncard A =
      Set.ncard X' * Set.ncard {a : J | a ∈ A ∧ ∀ y ∈ X', B a y = 1} := by exact @_root_.P2MW.S_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical.solution J J' _ _ L _ _ A X' hA hX' hA0 hAadd hAneg hX'0 hX'add hX'neg B hBl hBr
