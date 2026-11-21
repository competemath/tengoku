import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w x
/--
@isnad1 id=eq.1h5v.s8.e407c9b2a1ee from=translated src=- shape=49f4f0c9 vocab=3ca055a8
-/
theorem HopfAlgebra.natCard_algHom_eq_mul_of_isHopfGalois
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
    [Module.Finite R A] (k : Type x) [Field k] [IsAlgClosed k] [Algebra R k]
    (π : A →ₐc[R] B) (hHG : HopfAlgebra.IsHopfGalois π) :
    Nat.card (A →ₐ[R] k) = Nat.card (B →ₐ[R] k) * Nat.card (↥(HopfAlgebra.hopfKer π) →ₐ[R] k) := by exact @_root_.P2MW.S_HopfAlgebra_natCard_algHom_eq_mul_of_isHopfGalois.solution R _ A _ _ B _ _ _ k _ _ _ π hHG
