import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SORotation
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.FrameGaugeNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# General special-orthogonal frame gauges

A smooth field of special-orthogonal matrices acts on the codomain of a framed
defining map by invertible continuous linear maps.  This file packages that
action and feeds a smooth `SO(n)`-valued homotopy directly into
`DefiningMapHomotopy.ofGauge`.

Thus the analytic conversion from a smooth frame homotopy to an actual
common-fiber defining-map homotopy is completely general; only the geometric
extension of loop data to such a smooth spatial field remains separate.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace SOFrameGauge

variable {n : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "M" => Matrix (Fin n) (Fin n) ℝ

/-- The Euclidean continuous-linear action of a special-orthogonal matrix.-/
def toCLM (A : SOGroup n) : F →L[ℝ] F :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M)

/--
@isnad1 id=eq.0h3v.s12.9e6360b908b4 from=translated src=- shape=4e1411a5 vocab=6d4cd532
-/
@[simp] theorem toCLM_apply (A : SOGroup n) (x : F) :
    toCLM A x =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M) x :=
  rfl

/--
@isnad1 id=eq.0h4v.s9.8f8e0e5159a5 from=translated src=- shape=dae0ae85 vocab=9b6300ba
-/
@[simp] theorem toCLM_apply_coord (A : SOGroup n) (x : F) (i : Fin n) :
    toCLM A x i = ∑ j : Fin n, (A : M) i j * x j := by
  change (Matrix.toLpLin 2 2 (A : M) x) i = _
  rw [Matrix.toLpLin_apply]
  rfl

/--
@isnad1 id=eq.0h1v.s9.1a556bcf48ae from=translated src=- shape=8bdd72de vocab=f5aa7caf
-/
@[simp] theorem toCLM_one :
    toCLM (1 : SOGroup n) = ContinuousLinearMap.id ℝ F := by
  apply ContinuousLinearMap.ext
  intro x
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (1 : M) x = x
  simp

/--
@isnad1 id=eq.0h3v.s10.9fcc4b49e6e7 from=translated src=- shape=6cb153af vocab=9c272010
-/
theorem toCLM_inv_apply (A : SOGroup n) (x : F) :
    toCLM A⁻¹ (toCLM A x) = x := by
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) ((↑A⁻¹ : M))
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M) x) = x
  change
    (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) ((↑A⁻¹ : M))) *
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M))) x = x
  rw [← map_mul]
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
    ((↑(A⁻¹ * A) : M)) x = x
  rw [inv_mul_cancel A]
  simp

/--
@isnad1 id=eq.0h3v.s10.0b0c0628a214 from=translated src=- shape=22143f09 vocab=9c272010
-/
theorem toCLM_apply_inv (A : SOGroup n) (x : F) :
    toCLM A (toCLM A⁻¹ x) = x := by
  simpa using toCLM_inv_apply A⁻¹ x

/--
@isnad1 id=bijectiv.0h2v.s9.32dd68f7fed8 from=translated src=- shape=fe9fc0ab vocab=293c4432
-/
theorem toCLM_bijective (A : SOGroup n) : Bijective (toCLM A) := by
  constructor
  · intro x y hxy
    have h := congrArg (toCLM A⁻¹) hxy
    simpa only [toCLM_inv_apply] using h
  · intro y
    exact ⟨toCLM A⁻¹ y, toCLM_apply_inv A y⟩

/-- Coordinatewise smoothness of an `SO(n)` field implies smoothness of its
continuous-linear action.  Matrix space itself carries only the product
topology here, so the coordinatewise statement is the robust formulation.
@isnad1 id=contdiff.1h3v.s10.b936f132ded0 from=translated src=- shape=acaf8488 vocab=395940d5
-/
theorem contDiff_toCLM {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {R : P → SOGroup n}
    (hR : ∀ i j, ContDiff ℝ ∞ (fun p => ((R p : SOGroup n) : M) i j)) :
    ContDiff ℝ ∞ (fun p => toCLM (R p)) := by
  rw [contDiff_clm_apply_iff]
  intro x
  rw [contDiff_euclidean]
  intro i
  simp_rw [toCLM_apply_coord]
  exact ContDiff.sum (s := Finset.univ)
    (fun j _ => (hR i j).mul contDiff_const)

/-- A smooth `SO(n)`-valued family starting at the identity gives an actual
defining-map homotopy, with no separate invertibility assumption.-/
def homotopy (X : FramedLevelSet n)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1) :
    DefiningMapHomotopy X
      (X.gaugeTransform (fun x => toCLM (R 1 x))
        (contDiff_toCLM (fun i j =>
          (hR i j).comp (contDiff_const.prodMk contDiff_id)))
        (fun x => toCLM_bijective (R 1 x))) :=
  DefiningMapHomotopy.ofGauge X (fun s x => toCLM (R s x))
    (contDiff_toCLM hR)
    (fun x => by rw [hRzero x, toCLM_one])
    (fun s _ x => toCLM_bijective (R s x))

/--
@isnad1 id=eq.2h5v.s10.02067a20fe4d from=translated src=- shape=90eb0c8b vocab=865f9052
-/
@[simp] theorem homotopy_H (X : FramedLevelSet n)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1) (s : ℝ) (x : E) :
    (homotopy X R hR hRzero).H s x = toCLM (R s x) (X.g x) :=
  rfl

end SOFrameGauge
end Submission
