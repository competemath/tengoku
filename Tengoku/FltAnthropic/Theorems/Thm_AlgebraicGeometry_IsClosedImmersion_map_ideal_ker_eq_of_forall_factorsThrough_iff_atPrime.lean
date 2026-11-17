import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=eq.1h10v.s13.0770e919924c from=translated src=- shape=e183e0c9 vocab=1012888d
-/
theorem AlgebraicGeometry.IsClosedImmersion.map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    {Z₁ Z₂ : Scheme.{0}} (ι₁ : Z₁ ⟶ A) (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (𝔭 : PrimeSpectrum S)
    (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)))
    (V : A.affineOpens) (Bₚ : Type) [CommRing Bₚ] [Algebra Γ(A, V.1) Bₚ]
    [IsLocalization (𝔭.asIdeal.primeCompl.map
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ V.1 le_top).hom.toMonoidHom) Bₚ] :
    (ι₁.ker.ideal V).map (algebraMap Γ(A, V.1) Bₚ) = (ι₂.ker.ideal V).map (algebraMap Γ(A, V.1) Bₚ) := by exact @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_map_ideal_ker_eq_of_forall_factorsThrough_iff_atPrime.solution S _ A f Z₁ Z₂ ι₁ ι₂ _ _ 𝔭 h V Bₚ _ _ _
