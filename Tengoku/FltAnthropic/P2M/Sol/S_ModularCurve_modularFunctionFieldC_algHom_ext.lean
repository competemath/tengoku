import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_modularFunctionFieldC_algHom_ext.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_modularFunctionFieldC_algHom_ext

set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K] (ℓ : ℕ) [NeZero ℓ] {A : Type*} [Semiring A] [Algebra K A]
    {f g : modularFunctionFieldC K ℓ →ₐ[K] A}
    (h1 : f ⟨jqModC K, jqModC_mem K ℓ⟩ = g ⟨jqModC K, jqModC_mem K ℓ⟩)
    (h2 : f ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = g ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := modularFunctionFieldC K ℓ)
    (s := ({jqModC K, jqNModC K ℓ} : Set (LaurentSeries K))) rfl (fun x hx => ?_)
  rcases hx with rfl | hx
  · exact h1
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h2

