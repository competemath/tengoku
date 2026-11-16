import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsPushout_slice_ext_and_exists_of_flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsPushout_slice_ext_and_exists_of_flat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

universe u
theorem Algebra.IsPushout.slice_ext_and_exists_of_flat
    {B B₁ B' M N : Type u} [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M] [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N] [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (hπ : Function.Surjective (algebraMap B B₁))
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B, (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) → ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' N x) = algebraMap B M (p i x)) :
    (∀ n n' : N, (∀ i, e i n = e i n') → n = n') ∧
    (∀ m : Fin 3 → M, (∀ i j, m i - m j ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) →
      ∃ n : N, ∀ i, e i n = m i) := by exact @_root_.P2MW.S_Algebra_IsPushout_slice_ext_and_exists_of_flat.solution B B₁ B' M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hπ p hp hinj hsurj e heM heB
