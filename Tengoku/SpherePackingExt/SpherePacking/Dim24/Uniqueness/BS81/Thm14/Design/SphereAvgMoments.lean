module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
public import Tengoku.Seed.MeasureTheory.Constructions.HaarToSphere
public import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace
public import Tengoku.Seed.Analysis.Normed.Lp.PiLp
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Invariance and second moments of `sphereAvg24`

This file develops basic properties of the spherical average `sphereAvg24` on `Ω₂₄`:
invariance under linear isometries and the explicit second coordinate moment.

## Main statements
* `sphereAvg24_comp_linearIsometryEquiv`
* `sphereAvg24_coord_sq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators Pointwise ENNReal
open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Auxiliary measurability lemma

This is the measurability fact needed to use `MeasurePreserving.measure_preimage` for the
polar-coordinate set `Ioo (0,1) • (Subtype.val '' s)`.
-/

/-!
## The induced action of a linear isometry on the unit sphere
-/

def sphereMap (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) : S23 → S23 :=
  fun x =>
    ⟨e x.1, by
      have hx : ‖x.1‖ = (1 : ℝ) :=
        mem_sphere_zero_iff_norm.mp x.2
      have : ‖e x.1‖ = (1 : ℝ) := by
        calc
          ‖e x.1‖ = ‖x.1‖ := e.norm_map x.1
          _ = (1 : ℝ) := hx
      exact mem_sphere_zero_iff_norm.mpr this⟩

@[simp] lemma sphereMap_coe (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) (x : S23) :
    (sphereMap e x : ℝ²⁴) = e (x : ℝ²⁴) := rfl

/-!
## Second coordinate moment
-/

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
