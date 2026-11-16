import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsFinite_of_smoothOfRelativeDimension_zero_of_field

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension LocallyQuasiFinite IsFinite QuasiCompact LocallyOfFiniteType Spec Scheme IsLocallyArtinian HasRingHomProperty.appLE Etale HasRingHomProperty.iff_appLE Scheme.isLocallyArtinianScheme_Spec FormallyUnramified HasRingHomProperty IsFinite.of_locallyQuasiFinite Etale.iff_smoothOfRelativeDimension_zero)
namespace EtaleOverField
open _root_.AlgebraicGeometry

theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ : RingHom.FormallyUnramified (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) f inferInstance U V e
  have h₂ : RingHom.FiniteType (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  rw [RingHom.QuasiFinite]
  have : Algebra.EssFiniteType Γ(Y, U) Γ(X, V) :=
    Algebra.EssFiniteType.of_finiteType _ _
  infer_instance

theorem isFinite_of_etale {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Etale f] [QuasiCompact f] : IsFinite f := by
  have hlqf : LocallyQuasiFinite f := locallyQuasiFinite_of_formallyUnramified f
  have hArt : IsLocallyArtinian (Spec (CommRingCat.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr (inferInstanceAs (IsArtinianRing k))
  exact IsFinite.of_locallyQuasiFinite f

end AlgebraicGeometry.EtaleOverField

open AlgebraicGeometry.EtaleOverField in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 0 f] [QuasiCompact f] : IsFinite f := by
  have hEt : Etale f := (Etale.iff_smoothOfRelativeDimension_zero (f := f)).mpr inferInstance
  exact isFinite_of_etale f
