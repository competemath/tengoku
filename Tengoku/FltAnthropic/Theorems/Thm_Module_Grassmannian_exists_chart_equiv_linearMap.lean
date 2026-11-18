import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Grassmannian_exists_chart_equiv_linearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Grassmannian_exists_chart_equiv_linearMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

theorem Module.Grassmannian.exists_chart_equiv_linearMap
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1},
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, (pt A N).1 m i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (ψ : {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}),
          ((pt A).symm ψ).1.toSubmodule = LinearMap.ker (ψ.1.liftBaseChange A)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            ∀ (m : M) (i : Fin k),
              (pt B ⟨Module.Grassmannian.map φ N.1, h⟩).1 m i = φ ((pt A N).1 m i)) := by exact @_root_.P2MW.S_Module_Grassmannian_exists_chart_equiv_linearMap.solution R _ M _ _ k x
