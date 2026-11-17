import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.Definitions.Def_FiniteFlat_ClosureHopf
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.5h4v.s13.ce5720bc89f6 from=translated src=- shape=c7d003f8 vocab=21b7c1d3
-/
theorem HopfAlgebra.exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {L : Type} [Field L] [Algebra R L] [IsAlgClosed L]
    (hRL : Function.Injective (algebraMap R L))
    (G : Type) [CommRing G] [HopfAlgebra R G]
    [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
    (K : Finset (G →ₐ[R] L))
    (hKone : (Algebra.ofId R L).comp (Bialgebra.counitAlgHom R G) ∈ K)
    (hKmul : ∀ k ∈ K, ∀ k' ∈ K,
      WithConv.ofConv (WithConv.toConv k * WithConv.toConv k') ∈ K)
    (hKS : ∀ k ∈ K, ∃ k' ∈ K,
      k'.toLinearMap = k.toLinearMap ∘ₗ HopfAlgebra.antipode R)
    (hdesc : ∀ g : G, ∃ (r : R) (g' : G), r ≠ 0 ∧
      r • (∑ k ∈ K, (Algebra.TensorProduct.map k (AlgHom.id R G)).comp
        (Bialgebra.comulAlgHom R G) g) = (1 : L) ⊗ₜ[R] g') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ ι : H' →ₐc[R] G,
        Function.Surjective (fun φ : G →ₐ[R] L => φ.comp (ι : H' →ₐ[R] G)) ∧
        ∀ φ ψ : G →ₐ[R] L, φ.comp (ι : H' →ₐ[R] G) = ψ.comp (ι : H' →ₐ[R] G) ↔
          ∃ k ∈ K, ψ = WithConv.ofConv (WithConv.toConv k * WithConv.toConv φ) := by exact @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_comp_of_avg_descent.solution R _ _ _ L _ _ _ hRL G _ _ _ _ _ K hKone hKmul hKS hdesc
