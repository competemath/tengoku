import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open Polynomial IsLocalRing in

theorem AdjoinRoot.exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (hfm : f.Monic) [Fact (Irreducible (f.map (residue R)))]
    [Algebra.IsSeparable (ResidueField R) (AdjoinRoot (f.map (residue R)))] :
    ∃ (_ : IsLocalRing (AdjoinRoot f)) (_ : IsLocalHom (algebraMap R (AdjoinRoot f))),
      Module.Finite R (AdjoinRoot f) ∧ Module.Free R (AdjoinRoot f) ∧ Algebra.Etale R (AdjoinRoot f) ∧
      IsAdicComplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) ∧
      Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) = maximalIdeal (AdjoinRoot f) ∧
      Nonempty (ResidueField (AdjoinRoot f) ≃ₐ[ResidueField R] AdjoinRoot (f.map (residue R))) := by exact @_root_.P2MW.S_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete.solution R _ _ _ f hfm _ _
