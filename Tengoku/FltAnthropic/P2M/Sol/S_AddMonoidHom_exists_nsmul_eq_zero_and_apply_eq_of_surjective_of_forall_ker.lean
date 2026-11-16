import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddMonoidHom_exists_nsmul_eq_zero_and_apply_eq_of_surjective_of_forall_ker

set_option autoImplicit false

theorem solution
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f)
    (m : ℕ) (hdiv : ∀ k : A, f k = 0 → ∃ j : A, f j = 0 ∧ m • j = k)
    (b : B) (hmb : m • b = 0) :
    ∃ a : A, m • a = 0 ∧ f a = b := by
  obtain ⟨a₀, ha₀⟩ := hf b
  have hker : f (m • a₀) = 0 := by rw [map_nsmul, ha₀, hmb]
  obtain ⟨j, hjker, hmj⟩ := hdiv (m • a₀) hker
  exact ⟨a₀ - j, by rw [smul_sub, hmj, sub_self], by rw [map_sub, ha₀, hjker, sub_zero]⟩
