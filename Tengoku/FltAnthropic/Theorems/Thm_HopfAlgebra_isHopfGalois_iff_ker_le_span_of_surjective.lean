import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

/--
@isnad1 id=iff.1h4v.s10.97af6823a5ae from=translated src=- shape=f6590657 vocab=8a4f3508
-/
theorem HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [HopfAlgebra R A] [Module.Flat R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    HopfAlgebra.IsHopfGalois π ↔
      RingHom.ker (π : A →ₐ[R] B) ≤
        Ideal.span {a : A | a ∈ HopfAlgebra.hopfKer π ∧ Coalgebra.counit (R := R) a = 0} := by exact @_root_.P2MW.S_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective.solution R _ A _ _ _ B _ _ π hπ
