import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct

universe u v w

/--
@isnad1 id=ex.5h6v.s9.4e644ef5f48f from=translated src=- shape=78b55670 vocab=7176b3e5
-/
theorem AlgebraicGeometry.AdmissibleAlgebra.exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow
    {R : Type u} [CommRing R] {G : Type v} [Group G] [Finite G] [MulSemiringAction G R]
    (t : R) (ht : ∀ g : G, g • t = t) (ht0 : ∀ x : R, t * x = 0 → x = 0) (e : ℕ)
    (hH1 : ∀ y : G → R, (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R), ∀ g : G, t ^ k * y g = g • z - z) → ∃ z : R, ∀ g : G, t ^ e * y g = g • z - z)
    (m : ℕ) (hm : e ≤ m) (x : R) (hx : ∀ g : G, g • x - x ∈ Ideal.span {t ^ m}) :
    ∃ w : R, (∀ g : G, g • w = w) ∧ x - w ∈ Ideal.span {t ^ (m - e)} := by exact @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow.solution R _ G _ _ _ t ht ht0 e hH1 m hm x hx
