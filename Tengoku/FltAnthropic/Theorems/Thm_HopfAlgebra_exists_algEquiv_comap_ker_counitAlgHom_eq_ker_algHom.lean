import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.0h3v.s9.864b416a8260 from=translated src=- shape=e721e93b vocab=bddce3ce
-/
theorem HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] (χ : A →ₐ[K] K) :
    ∃ e : A ≃ₐ[K] A,
      (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap e.toRingEquiv.toRingHom
        = RingHom.ker χ.toRingHom := by exact @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.solution K _ A _ _ χ
