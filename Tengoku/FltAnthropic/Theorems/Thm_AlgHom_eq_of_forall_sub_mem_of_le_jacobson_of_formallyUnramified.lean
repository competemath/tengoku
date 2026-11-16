import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

theorem AlgHom.eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {B : Type w} [CommRing B] [Algebra R B]
    (I : Ideal B) (hI : I ≤ Ideal.jacobson ⊥)
    (f g : A →ₐ[R] B) (hfg : ∀ a : A, f a - g a ∈ I) :
    f = g := by exact @_root_.P2MW.S_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified.solution R _ A _ _ _ _ B _ _ I hI f g hfg
