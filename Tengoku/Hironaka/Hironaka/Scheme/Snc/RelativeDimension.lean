/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Scheme.Snc.SmoothDivisor
public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SmoothAt
import Tengoku.Hironaka.Hironaka.Algebra.Local.Regular
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Cotangent
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SchemeForms
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Trdeg
import Tengoku.Hironaka.Hironaka.Scheme.Smooth.AdaptedCoordinates
import Tengoku.Hironaka.Hironaka.Scheme.Smooth.SubschemeStalk
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Finite
import Tengoku.Seed.Algebra.Module.SpanRankOperations
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth divisors are smooth of relative dimension `n − 1`

The converse of `isSmoothDivisor_of_smoothOfRelativeDimension`
(`Hironaka.Scheme.Snc.SmoothDivisor`): a smooth divisor `D` of `X`, smooth of relative dimension `n`
over the perfect field `k`, is smooth of relative dimension `n − 1` over `k` — for every `n`, with
`n − 1` the truncated difference (at `n = 0` the stalks are fields and a smooth divisor is empty).
The closed subscheme `V(D)` is regular, hence smooth over `k`
(`Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv`); its relative dimension is read off at one
point of each affine chart: for a standard smooth `k`-algebra `S` the module `Ω[S⁄k]` is free, so
its rank is `dim_κ κ(𝔮) ⊗ Ω[S⁄k]` at any prime `𝔮`, which is `dim S_𝔮 + trdeg_k κ(𝔮)` (the dimension
count of `Hironaka.Algebra.RegularSmooth.Dimension`), and Mathlib's
`IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` turns the rank into the relative
dimension. At a point `z` of `V(D)` over `x ∈ X` the local ring is `𝒪_{X,x}/(a)` with `a ∈ 𝔪_x ∖
𝔪_x²`, of dimension `dim 𝒪_{X,x} − 1`, with the residue field of `x`, and `dim 𝒪_{X,x} + trdeg_k
κ(x) = n` (`ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension`). Together the
two directions are the equivalence "`D` is a smooth divisor iff `V(D)` is smooth of relative
dimension `n − 1`", which the passage to a hypersurface of maximal contact
(`Hironaka.Resolution.Algebraic.MaximalContact.GoingDown`) and the dimension bookkeeping of
`Hironaka.Stage` use. -/

public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace AlgebraicGeometry

section Ring

variable {k : Type u} [Field k] {S : Type u} [CommRing S] [Algebra k S]

end Ring

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The converse of `Scheme.Hom.exists_affineOpen_isStandardSmoothOfRelativeDimension`: a morphism
to `Spec k` such that every point has an affine neighbourhood `V` with `Γ(X, V)` standard smooth of
relative dimension `m` over `k` (the `k`-algebra structure through `f`) is smooth of relative
dimension `m`.
@isnad1 id=smoothof.1h4v.s8.fbca534fcac0 from=translated src=- shape=a79733c1 vocab=7c72c5c9
-/
theorem smoothOfRelativeDimension_of_forall_exists_affineOpen (f : X ⟶ Spec (.of k))
    (m : ℕ) (h : ∀ x : X, ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, V)) :
    SmoothOfRelativeDimension m f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨V, hV, hxV, hstd⟩ := h x
  refine ⟨⊤, isAffineOpen_top _, V, hV, hxV, le_top, ?_⟩
  let := f.sectionsAlgebra V
  have h1 : RingHom.IsStandardSmoothOfRelativeDimension m (algebraMap k Γ(X, V)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap m).mpr hstd
  exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := m)).cancel_left_isIso
    (Scheme.ΓSpecIso (.of k)).inv (f.appLE ⊤ V le_top)).mp h1

/-- A scheme smooth over `k` is covered by affine opens whose section rings are standard smooth
`k`-algebras (through `f`); the `Smooth` analogue of
`exists_affineOpen_isStandardSmoothOfRelativeDimension`.
@isnad1 id=ex.0h4v.s8.bfadfb12be5f from=translated src=- shape=11e06b72 vocab=8300150f
-/
theorem exists_affineOpen_isStandardSmooth (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V),
      letI := f.sectionsAlgebra V
      Algebra.IsStandardSmooth k Γ(X, V) := by
  obtain ⟨U', hU', V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have hU'top : U' = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro y
    rw [Subsingleton.elim (α := PrimeSpectrum k) y (f x)]
    exact e hxV
  subst hU'top
  refine ⟨V, hV, hxV, ?_⟩
  let := f.sectionsAlgebra V
  exact RingHom.isStandardSmooth_respectsIso.2 (f.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hstd

/-- Cancellation in `WithBot ℕ∞`: from `r + t = n` with `r, n` finite and `p + 1 = r`,
`p + t = n − 1`.
@isnad1 id=eq.2h4v.s6.7af1850b6c54 from=translated src=- shape=42acfb49 vocab=4d02c8d1
-/
theorem natCast_add_eq_natCast_sub_one {p r n : ℕ} {t : ℕ∞}
    (hX : ((r : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = (n : WithBot ℕ∞)) (hpr : p + 1 = r) :
    ((p : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  have ht : t ≠ ⊤ := by
    rintro rfl
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, add_top, ← WithBot.coe_natCast] at hX
    exact ENat.top_ne_natCast n (WithBot.coe_inj.mp hX)
  lift t to ℕ using ht with t' ht'
  have h1 : r + t' = n := by exact_mod_cast hX
  have h2 : p + t' = n - 1 := by omega
  rw [WithBot.coe_natCast, ← Nat.cast_add, h2]

end Scheme

end AlgebraicGeometry
