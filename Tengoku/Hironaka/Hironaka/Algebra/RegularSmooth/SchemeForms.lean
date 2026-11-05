/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Stalk
public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Defs
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Dimension
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Regular
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scheme forms of "smooth implies regular" and of the dimension of a smooth stalk

The affine reduction of `Hironaka/Algebra/RegularSmooth/SmoothAt.lean` and `Regular.lean` turns the
ring statements of this directory into statements about a scheme `X` locally of finite type over a
field `k`, `f : X ⟶ Spec k`. *Regularity* (the last sentence of [Sta, Tag 00TT]): a point `x` of
the smooth locus of `f` is a regular point, because on an affine open `U ∋ x` with prime `𝔮` of
`x`, `x ∈ f.smoothLocus` means `Γ(X, U)` is smooth at `𝔮` over `k`
(`mem_smoothLocus_iff_isSmoothAt`), `Γ(X, U)` is of finite type over `k`, so `Γ(X, U)_𝔮` is
regular (`SmoothImpliesRegular.lean`), and `Γ(X, U)_𝔮 ≅ 𝒪_{X,x}`
(`isRegularAt_iff_isRegularLocalRing_localization`). *Dimension* ([Sta, Tag 0A21, (10)]): if `f`
is smooth of relative dimension `n`, every `x` has an affine open `V ∋ x` on which `Γ(X, V)` is
standard smooth of relative dimension `n` over `k` (Mathlib's `SmoothOfRelativeDimension`, with
`Spec k` a single point so the affine open of the target is `⊤`, and the base ring `Γ(Spec k, ⊤)`
replaced by `k` along `Scheme.ΓSpecIso`); the stalk `𝒪_{X,x} ≅ Γ(X, V)_𝔮` as `k`-algebras
(`Scheme.Hom.stalkAlgebra`, the scalar tower of `Stalk.lean`), so `dim 𝒪_{X,x} + trdeg_k κ(x) = n`
and, at a closed point (where `𝔮` is maximal), `dim 𝒪_{X,x} = n` follow from the affine statements
of `Dimension.lean`. The closed-point form gives the dimension of the local rings of a smooth
variety, used for étale coordinates and normal crossings (`Hironaka/Smooth/`, `Hironaka/Snc/`).
-/

public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For `f : X ⟶ Spec k` smooth of relative dimension `n`, every point has an affine open
neighbourhood `V` on which `Γ(X, V)` is standard smooth of relative dimension `n` over `k`
(Mathlib's `SmoothOfRelativeDimension`, with the affine open of `Spec k` necessarily `⊤` and the
base ring `Γ(Spec k, ⊤)` replaced by `k` along `Scheme.ΓSpecIso`).-/
theorem Scheme.Hom.exists_affineOpen_isStandardSmoothOfRelativeDimension (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := by
  obtain ⟨U', hU', V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hU'top : U' = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro y
    rw [Subsingleton.elim (α := PrimeSpectrum k) y (f x)]
    exact e hxV
  subst hU'top
  refine ⟨V, hV, hxV, ?_⟩
  let := f.sectionsAlgebra V
  have := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).2
    (f.appLE ⊤ V e).hom (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hstd
  exact this

end AlgebraicGeometry
