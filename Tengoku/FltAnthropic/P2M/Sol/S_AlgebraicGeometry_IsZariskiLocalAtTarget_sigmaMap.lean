import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap

set_option autoImplicit false
universe u
open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (sigmaMk_mk Scheme.Hom IsZariskiLocalAtTarget Scheme sigmaι_eq_iff IsOpenImmersion sigmaOpenCover IsZariskiLocalAtTarget.of_openCover sigmaMk IsOpenImmersion.isPullback Scheme.Hom.comp_apply)
namespace SigmaMapU4
open _root_.AlgebraicGeometry

variable {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)

theorem sigmaMap_sigmaι_apply (i : σ) (x : X i) :
    (Limits.Sigma.map f) ((Limits.Sigma.ι X i) x) = (Limits.Sigma.ι Y i) (f i x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_map]

set_option backward.isDefEq.respectTransparency false in

theorem isPullback_sigmaι_sigmaMap (j : σ) :
    IsPullback (f j) (Limits.Sigma.ι X j) (Limits.Sigma.ι Y j) (Limits.Sigma.map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
    rw [sigmaMk_mk] at hxy ⊢
    have hxy' : (Limits.Sigma.ι Y j) y = (Limits.Sigma.ι Y i) (f i x) := by
      rw [← sigmaMap_sigmaι_apply]; exact hxy
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff Y j i _ _).mp hxy')
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f j x, (sigmaMap_sigmaι_apply f j x).symm⟩

end AlgebraicGeometry.SigmaMapU4

open AlgebraicGeometry.SigmaMapU4 in
set_option backward.isDefEq.respectTransparency false in
theorem solution
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y) ?_
  intro j
  show P (Limits.pullback.snd (Limits.Sigma.map f) (Limits.Sigma.ι Y j))
  rw [← MorphismProperty.cancel_left_of_respectsIso P (isPullback_sigmaι_sigmaMap f j).flip.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  exact hf j
