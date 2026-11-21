import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w x
/--
@isnad1 id=iff.1h7v.s10.071b8f36434b from=translated src=- shape=9784ca18 vocab=9a7ab05a
-/
theorem HopfAlgebra.algHom_comp_hopfKer_val_eq_iff {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : HopfAlgebra.IsHopfGalois π)
    {k : Type x} [CommRing k] [Algebra R k] (ψ ψ' : A →ₐ[R] k) :
    ψ.comp (HopfAlgebra.hopfKer π).val = ψ'.comp (HopfAlgebra.hopfKer π).val
      ↔ ∃! χ : B →ₐ[R] k,
          (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (HopfAlgebra.coaction π) = ψ' := by exact @_root_.P2MW.S_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff.solution R _ A _ _ B _ _ π hπ k _ _ ψ ψ'
