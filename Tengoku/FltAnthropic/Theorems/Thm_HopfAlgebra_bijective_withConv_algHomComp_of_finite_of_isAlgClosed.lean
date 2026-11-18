import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=and.1h5v.s10.d48fdf2ddfaa from=translated src=- shape=e5fc1166 vocab=07ae02f5
-/
theorem HopfAlgebra.bijective_withConv_algHomComp_of_finite_of_isAlgClosed
    (K : Type) [Field K]
    (L₁ : Type) [Field L₁] [Algebra K L₁] [IsAlgClosed L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [IsAlgClosed L₂]
    (ι : L₁ →ₐ[K] L₂)
    (A : Type) [CommRing A] [HopfAlgebra K A] (hfin : Module.Finite K A) :
    Function.Bijective
      (fun f : WithConv (A →ₐ[K] L₁) => (WithConv.toConv (ι.comp f.ofConv) :
        WithConv (A →ₐ[K] L₂))) ∧
    ∀ f g : WithConv (A →ₐ[K] L₁),
      WithConv.toConv (ι.comp (f * g).ofConv)
        = WithConv.toConv (ι.comp f.ofConv) * WithConv.toConv (ι.comp g.ofConv) := by exact @_root_.P2MW.S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed.solution K _ L₁ _ _ _ L₂ _ _ _ ι A _ _ hfin
