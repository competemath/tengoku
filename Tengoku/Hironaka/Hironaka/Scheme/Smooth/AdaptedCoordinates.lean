/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.Stalk
public import Tengoku.Hironaka.Hironaka.Scheme.IdealSheaf.Defs
public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs
public import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Subscheme
import Tengoku.Hironaka.Hironaka.Algebra.Local.QuotientParameters
import Tengoku.Hironaka.Hironaka.Algebra.Local.Regular
import Tengoku.Hironaka.Hironaka.Algebra.Local.RegularSystem
import Tengoku.Hironaka.Hironaka.Algebra.RegularSmooth.SchemeForms
import Tengoku.Hironaka.Hironaka.Scheme.Smooth.SubschemeStalk
import Tengoku.Seed.RingTheory.Ideal.KrullsHeightTheorem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local parameters adapted to a smooth center

`X` is a scheme over a field `k` (`f : X ⟶ Spec k`), `Z` an ideal sheaf with closed subscheme
`V(Z)`, `x ∈ V(Z)`, `Z_x = stalkIdeal Z x ⊆ 𝒪_{X,x}` the stalk of `Z`, and
`𝒪_{V(Z),x} = 𝒪_{X,x}/Z_x` (`stalkQuotientEquiv`). For `X` smooth of relative dimension `n` and
`V(Z)` smooth of relative dimension `n − r` over a perfect field, this file produces Kollár's
adapted local coordinates: a regular system of parameters of `𝒪_{X,x}` whose first `r` members
generate `Z_x` ("`Z = (z_{j_1} = ⋯ = z_{j_s} = 0)`", [Kol07, Definition 24, (4)]; the coordinates
"such that `Z = (x_1 = ⋯ = x_r = 0)`" of [Kol07, Definition 60]).

* `𝒪_{X,x}` is regular for `f` smooth ([Sta, Tag 00TT]; `Scheme.isRegularAt_of_mem_smoothLocus`
  at a point of the smooth locus, which is everything).
* `𝒪_{X,x}/Z_x ≅ 𝒪_{V(Z),x}` is regular for `V(Z)` smooth (the same for `V(Z)`); at a closed
  point of `V(Z)` smooth of relative dimension `n − r`, its dimension is `n − r`
  (`Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed` for `V(Z)`).
* At any `x ∈ V(Z)`, `dim 𝒪_{X,x}/Z_x + r = dim 𝒪_{X,x}`: the dimension formula
  `dim 𝒪 + trdeg_k κ = n` of `Hironaka/Algebra/RegularSmooth/SchemeForms.lean` for `X` and for
  `V(Z)` gives `dim 𝒪_{X,x} + t = n` and `dim 𝒪_{V(Z),x} + t' = n − r` with `t, t'` the
  transcendence degrees of the residue fields, which agree because the stalk map of the closed
  immersion induces a `k`-isomorphism of residue fields (`residueFieldStalkEquiv`, with the
  `k`-structures `Scheme.Hom.stalkAlgebra` compatible along `V(Z) ⟶ X ⟶ Spec k`).
* Adapted parameters: [Sta, Tag 00NR] in the form
  `IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt` of
  `Hironaka/Algebra/Local/QuotientParameters.lean`, applied to `R = 𝒪_{X,x}` and `I = Z_x`, gives a
  regular system of parameters `y` with `Z_x = (y_0, …, y_{c-1})`; `c = r` because `dim R/I + c =
  dim R` and `dim R/I + r = dim R`. At a closed point `dim R = n`, so `y` has `n` members
  (`exists_adaptedCoordinates`).

The differentials of these parameters form a basis of the differentials at the point
(`Hironaka/Scheme/Smooth/DifferentialBasis.lean`), which is how they are spread out to étale
coordinates adapted to the center on an affine neighbourhood
(`Hironaka/Scheme/Smooth/EtaleCoordinatesAdapted.lean`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory IsLocalRing Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

variable (Z : X.IdealSheafData)

/-- The `k`-algebra structures `Scheme.Hom.stalkAlgebra` of `𝒪_{X,ι z}` (through `f`) and of
`𝒪_{V(Z),z}` (through `ι ≫ f`) are compatible with the stalk map of `ι : V(Z) ⟶ X`.
@isnad1 id=eq.0h6v.s12.cddcb9cd9292 from=translated src=- shape=b217d09c vocab=9a84effc
-/
theorem stalkMap_subschemeι_algebraMap (f : X ⟶ Spec (.of k)) (z : Z.subscheme) (c : k) :
    letI := f.stalkAlgebra (Z.subschemeι z)
    letI := (Z.subschemeι ≫ f).stalkAlgebra z
    Z.subschemeι.stalkMap z (algebraMap k (X.presheaf.stalk (Z.subschemeι z)) c) =
      algebraMap k (Z.subscheme.presheaf.stalk z) c := by
  let := f.stalkAlgebra (Z.subschemeι z)
  let := (Z.subschemeι ≫ f).stalkAlgebra z
  have hx₁ : Z.subschemeι z ∈ f ⁻¹ᵁ ⊤ := trivial
  have hz₁ : z ∈ (Z.subschemeι ≫ f) ⁻¹ᵁ ⊤ := trivial
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
        X.presheaf.germ (f ⁻¹ᵁ ⊤) (Z.subschemeι z) hx₁ ≫ Z.subschemeι.stalkMap z =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).app ⊤ ≫
        Z.subscheme.presheaf.germ ((Z.subschemeι ≫ f) ⁻¹ᵁ ⊤) z hz₁ := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_app]
    rfl
  have h' := congrArg (fun φ : CommRingCat.of k ⟶ Z.subscheme.presheaf.stalk z => φ.hom c) h
  change (Z.subschemeι.stalkMap z).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤ ≫
    X.presheaf.germ (f ⁻¹ᵁ ⊤) (Z.subschemeι z) hx₁).hom c) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ f).app ⊤ ≫
        Z.subscheme.presheaf.germ ((Z.subschemeι ≫ f) ⁻¹ᵁ ⊤) z hz₁).hom c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h' ⊢
  exact h'

/-- The residue fields of `𝒪_{X,ι z}` and `𝒪_{V(Z),z}` have the same transcendence degree over
`k` (they are `k`-isomorphic through the stalk map of the closed immersion).
@isnad1 id=eq.0h5v.s10.5c9013b09094 from=translated src=- shape=3c3a8413 vocab=391ff710
-/
theorem trdeg_residueField_stalk_subschemeι (f : X ⟶ Spec (.of k)) (z : Z.subscheme) :
    letI := f.stalkAlgebra (Z.subschemeι z)
    letI := (Z.subschemeι ≫ f).stalkAlgebra z
    Algebra.trdeg k (ResidueField (Z.subscheme.presheaf.stalk z)) =
      Algebra.trdeg k (ResidueField (X.presheaf.stalk (Z.subschemeι z))) := by
  let := f.stalkAlgebra (Z.subschemeι z)
  let := (Z.subschemeι ≫ f).stalkAlgebra z
  let e : ResidueField (X.presheaf.stalk (Z.subschemeι z)) ≃ₐ[k]
      ResidueField (Z.subscheme.presheaf.stalk z) :=
    AlgEquiv.ofRingEquiv (f := Z.residueFieldStalkEquiv z) fun c => by
      change Z.residueFieldStalkEquiv z (IsLocalRing.residue _ (algebraMap k _ c)) =
        IsLocalRing.residue _ (algebraMap k _ c)
      rw [Z.residueFieldStalkEquiv_residue, stalkMap_subschemeι_algebraMap Z f z c]
  exact e.trdeg_eq.symm

/-- Cancellation in `WithBot ℕ∞`: from `a + t = n` and `b + t = m` with `m + r = n` (all finite
except possibly `t`, which is then finite too), `b + r = a`.
@isnad1 id=eq.3h6v.s7.f9708b37d5f4 from=translated src=- shape=7fc2efcf vocab=dd07c3d4
-/
theorem natCast_add_natCast_eq_of_add_eq {a b n m r : ℕ} {t : ℕ∞}
    (hX : ((a : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = (n : WithBot ℕ∞))
    (hZ : ((b : ℕ) : WithBot ℕ∞) + (t : WithBot ℕ∞) = (m : WithBot ℕ∞)) (hm : m + r = n) :
    ((b : ℕ) : WithBot ℕ∞) + (r : WithBot ℕ∞) = (a : WithBot ℕ∞) := by
  have ht : t ≠ ⊤ := by
    rintro rfl
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, add_top, ← WithBot.coe_natCast] at hX
    exact ENat.top_ne_natCast n (WithBot.coe_inj.mp hX)
  lift t to ℕ using ht with t' ht'
  have h1 : a + t' = n := by exact_mod_cast hX
  have h2 : b + t' = m := by exact_mod_cast hZ
  have h3 : b + r = a := by omega
  exact_mod_cast h3

end AlgebraicGeometry
