import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_ker_baseChange_field_of_subsingleton_H1_of_projective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

open TensorProduct

theorem Module.ker_baseChange_field_of_subsingleton_H1_of_projective
    (R : Type u) [CommRing R]
    {C0 C1 C2 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [AddCommGroup C2] [Module R C2]
    [Module.Finite R C1] [Module.Projective R C1] [Module.Finite R C2] [Module.Projective R C2]
    (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hdd : d1 ∘ₗ d0 = 0)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker (d1.baseChange K) ≤ LinearMap.range (d0.baseChange K)) :
    LinearMap.range ((LinearMap.ker d0).subtype.baseChange K) = LinearMap.ker (d0.baseChange K) ∧
      Function.Injective ((LinearMap.ker d0).subtype.baseChange K) := by exact @_root_.P2MW.S_Module_ker_baseChange_field_of_subsingleton_H1_of_projective.solution R _ C0 C1 C2 _ _ _ _ _ _ _ _ _ _ d0 d1 hdd K _ _ hH1
