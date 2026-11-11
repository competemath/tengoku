/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Subscheme
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Finite
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Smooth
import Tengoku.Aintlib.ModularCurves.ForMathlib.FibrewiseFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A smooth chart on which a finite closed subscheme has finite fibres

Let `π : C ⟶ S` be smooth of relative dimension `n` and let `J` be an ideal sheaf whose
closed subscheme is **finite over `S`** (the situation of a relative effective Cartier
divisor). Around any point `c` of the support we produce a standard-smooth affine chart
`V₀ ⊆ C` over an affine `U₀ ⊆ S` on which `Γ(C,V₀) ⧸ J(V₀)` has **finite fibres** over
`Γ(S,U₀)` (`ModularCurves.HasFiniteFibres`).

The finiteness of `J`'s subscheme over `S` does **not** survive to a chart — a chart cuts the
subscheme down to an open piece, and an open piece of a finite scheme is finite only over the
locus where it is *clopen*, which Zariski-locally one cannot arrange (splitting a fibre point
off needs henselisation). Arranging containment in a single affine instead would need `C/S`
quasi-projective, which is not available for an abstract relative curve.

What *does* work — and is what the consumers need — is to shrink the chart so that the trace
of the subscheme on it is a **basic** open of an affine chart of the subscheme
(`exists_basicOpen_chart`). Then `Γ` of that trace is a localization away from one element of
a module-finite algebra, and `module_finite_tensor_of_localizationAway` applies fibre by
fibre.
-/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace ModularCurves

variable {C S : Scheme.{u}}

/-- The `Γ(S,U₀)`-algebra comparison `Γ(subscheme, ι⁻¹V) ≃ Γ(C,V) ⧸ J(V)` on an affine chart
`V` lying over an affine `U₀`.-/
noncomputable def subschemeChartAlgEquiv (π : C ⟶ S) (J : C.IdealSheafData) {U₀ : S.Opens}
    {V : C.Opens} (hV : IsAffineOpen V) (e : V ≤ π ⁻¹ᵁ U₀)
    (e' : J.subschemeι ⁻¹ᵁ V ≤ (J.subschemeι ≫ π) ⁻¹ᵁ U₀) :
    letI : Algebra Γ(S, U₀) Γ(C, V) := (π.appLE U₀ V e).hom.toAlgebra
    letI : Algebra Γ(S, U₀) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) :=
      ((J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e').hom.toAlgebra
    Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) ≃ₐ[Γ(S, U₀)] (Γ(C, V) ⧸ J.ideal ⟨V, hV⟩) := by
  letI : Algebra Γ(S, U₀) Γ(C, V) := (π.appLE U₀ V e).hom.toAlgebra
  letI : Algebra Γ(S, U₀) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ V) :=
    ((J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e').hom.toAlgebra
  have hcomp : (J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e' ≫
      (J.subschemeObjIso (⟨V, hV⟩ : C.affineOpens)).hom
      = π.appLE U₀ V e ≫ CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal ⟨V, hV⟩)) := by
    have h1 : (J.subschemeι ≫ π).appLE U₀ (J.subschemeι ⁻¹ᵁ V) e'
        = π.appLE U₀ V e ≫ J.subschemeι.appLE V (J.subschemeι ⁻¹ᵁ V) le_rfl := by
      rw [Scheme.Hom.appLE_comp_appLE]
    have h2 : J.subschemeι.appLE V (J.subschemeι ⁻¹ᵁ V) le_rfl = J.subschemeι.app V :=
      Scheme.Hom.appLE_eq_app _
    rw [h1, h2, J.subschemeι_app ⟨V, hV⟩, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine AlgEquiv.ofRingEquiv
    (f := Iso.commRingCatIsoToRingEquiv (J.subschemeObjIso (⟨V, hV⟩ : C.affineOpens)))
    (fun r => ?_)
  exact congrArg
    (fun w : Γ(S, U₀) ⟶ CommRingCat.of (Γ(C, V) ⧸ J.ideal ⟨V, hV⟩) => w.hom r) hcomp

end ModularCurves
