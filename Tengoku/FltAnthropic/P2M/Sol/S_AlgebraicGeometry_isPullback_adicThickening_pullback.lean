import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_AdicThickening
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isPullback_adicThickening_pullback.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isPullback_adicThickening_pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/--
@isnad1 id=ispullba.4h9v.s10.940f95f7dc08 from=translated src=- shape=37032dc7 vocab=baad9545
-/
theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (prX : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hprX₁ : prX ≫ adicThickeningι f I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g)
    (hprX₂ : prX ≫ adicThickeningToBase f I n = adicThickeningToBase (pullback.fst f g ≫ f) I n)
    (prY : adicThickening (pullback.fst f g ≫ f) I n ⟶ adicThickening g I n)
    (hprY₁ : prY ≫ adicThickeningι g I n = adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g)
    (hprY₂ : prY ≫ adicThickeningToBase g I n = adicThickeningToBase (pullback.fst f g ≫ f) I n) :
    IsPullback prX prY (adicThickeningToBase f I n) (adicThickeningToBase g I n) := by

  have sqX : IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f (adicThickeningBase I n) :=
    IsPullback.of_hasPullback _ _
  have sqY : IsPullback (adicThickeningι g I n) (adicThickeningToBase g I n) g (adicThickeningBase I n) :=
    IsPullback.of_hasPullback _ _
  have sqP : IsPullback (adicThickeningι (pullback.fst f g ≫ f) I n) (adicThickeningToBase (pullback.fst f g ≫ f) I n)
      (pullback.fst f g ≫ f) (adicThickeningBase I n) := IsPullback.of_hasPullback _ _
  have sqXY : IsPullback (pullback.snd f g) (pullback.fst f g) g f := (IsPullback.of_hasPullback f g).flip

  have L2 : IsPullback prX (adicThickeningι (pullback.fst f g ≫ f) I n) (adicThickeningι f I n) (pullback.fst f g) := by
    refine IsPullback.of_right ?_ hprX₁ sqX.flip
    rw [hprX₂]
    exact sqP.flip

  have O3 : IsPullback (adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.snd f g) prX g (adicThickeningι f I n ≫ f) :=
    L2.flip.paste_horiz sqXY

  have comm : prY ≫ adicThickeningToBase g I n = prX ≫ adicThickeningToBase f I n := by rw [hprY₂, hprX₂]
  refine (IsPullback.of_right ?_ comm sqY).flip
  rw [hprY₁, ← adicThickeningι_comp]
  exact O3
