import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 : PrimeSpectrum R) (g : R) (hg : g ∉ 𝔭.asIdeal)
    (hproj : ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) → Module.Projective A (A ⊗[R] M)) :
    ∃ g' : R, g' ∉ 𝔭.asIdeal ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') → IsUnit (algebraMap R A g)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') →
        ∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (A ⊗[R] M) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M) := by exact @_root_.P2MW.S_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor.solution R _ _ M _ _ _ 𝔭 g hg hproj
