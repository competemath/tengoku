import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_of_basis_eq_D

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_of_basis_eq_D.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open KaehlerDifferential

universe u v

/--
@isnad1 id=etale.2h5v.s9.0454e89e271b from=translated src=- shape=23159edc vocab=fb71928e
-/
theorem Algebra.Etale.of_basis_eq_D
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    {ι : Type v} [Finite ι] (x : ι → S) (b : Module.Basis ι S Ω[S⁄R]) (hb : ∀ i, b i = D R S (x i))
    [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
    (hx : ∀ i, algebraMap (MvPolynomial ι R) S (MvPolynomial.X i) = x i) :
    Algebra.Etale (MvPolynomial ι R) S := by exact @_root_.P2MW.S_Algebra_Etale_of_basis_eq_D.solution R _ S _ _ _ ι _ x b hb _ _ hx
