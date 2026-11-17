import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.6h6v.s13.cb8fddd9cab0 from=translated src=- shape=9c607860 vocab=00ee1744
-/
theorem HopfAlgebra.exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
    (R : Type) [CommRing R] (S : Type) [CommRing S] (φ : R ≃+* S)
    [Algebra R (AlgebraicClosure ℚ)] [Algebra S (AlgebraicClosure ℚ)]
    (hφ : ∀ r, algebraMap R (AlgebraicClosure ℚ) r = algebraMap S (AlgebraicClosure ℚ) (φ r))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (H : Type) [CommRing H] [HopfAlgebra S H]
    (hHfin : Module.Finite S H) (hHflat : Module.Flat S H)
    (hHcocomm : Coalgebra.IsCocomm S H)
    (eH : WithConv (H →ₐ[S] AlgebraicClosure ℚ) ≃ N)
    (heH_add : ∀ f g, eH (f * g) = eH f + eH g)
    (heH_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[S] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ e' : WithConv (H' →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H' →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H', g h = σ (f h)) → e' g = σ • (e' f) := by exact @_root_.P2MW.S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv.solution R _ S _ φ _ _ hφ N _ _ H _ _ hHfin hHflat hHcocomm eH heH_add heH_act
