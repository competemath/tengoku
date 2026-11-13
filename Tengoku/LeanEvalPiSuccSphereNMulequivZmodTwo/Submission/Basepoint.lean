import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.HomotopyFunctor
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basepoint transport on unit spheres

Any two points of the unit sphere of a real inner product space are related by a
linear isometry of the ambient space (a hyperplane reflection), hence the homotopy
groups of the sphere at different basepoints are isomorphic.

Main declarations:

* `Submission.unitSphereHomeomorphOfLinearIsometryEquiv`: a linear isometry
  equivalence restricts to a homeomorphism of unit spheres;
* `Submission.basepointReflection b x`: the reflection of the ambient space in the
  hyperplane `(ℝ ∙ (b - x))ᗮ`, which swaps `b` and `x`;
* `Submission.rotateToBasepointHomeomorph b x`: the induced self-homeomorphism of the
  unit sphere, sending `b` to `x`;
* `Submission.basepointMulEquiv`: the induced isomorphism
  `HomotopyGroup N (UnitSphere E) b ≃* HomotopyGroup N (UnitSphere E) x`.

## Orientation warning

The basepoint transport here is implemented by a SINGLE hyperplane reflection, which
is orientation-REVERSING on the ambient space (and on the sphere, in the relevant
dimension range).  Downstream arguments valued in `ℤ/2` are insensitive to this, but
any future use tracking a `ℤ`-degree must instead compose two reflections (or
otherwise use an orientation-preserving rotation).
-/

noncomputable section

open scoped Topology unitInterval RealInnerProductSpace
open Metric

namespace Submission

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence of real inner product spaces restricts to a
homeomorphism of unit spheres.-/
def unitSphereHomeomorphOfLinearIsometryEquiv (e : E ≃ₗᵢ[ℝ] F) :
    UnitSphere E ≃ₜ UnitSphere F :=
  e.toHomeomorph.subtype fun v => by
    simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.coe_toHomeomorph,
      LinearIsometryEquiv.norm_map]

/--
@isnad1 id=eq.0h4v.s9.136ee07a9f13 from=translated src=- shape=9953985b vocab=4e5cb6e8
-/
@[simp]
theorem unitSphereHomeomorphOfLinearIsometryEquiv_apply_coe (e : E ≃ₗᵢ[ℝ] F)
    (v : UnitSphere E) :
    (unitSphereHomeomorphOfLinearIsometryEquiv e v : F) = e v :=
  rfl

/-- The reflection of the ambient space in the hyperplane `(ℝ ∙ (b - x))ᗮ`.  It is a
linear isometry equivalence swapping `b` and `x`.  In the degenerate case `b = x` the
hyperplane is the whole space and the reflection is the identity.-/
def basepointReflection (b x : UnitSphere E) : E ≃ₗᵢ[ℝ] E :=
  Submodule.reflection (ℝ ∙ ((b : E) - (x : E)))ᗮ

/-- The basepoint reflection sends the first point to the second.
@isnad1 id=eq.0h3v.s8.9660fb5f82fb from=translated src=- shape=873fc287 vocab=d132fd10
-/
theorem basepointReflection_apply_fst (b x : UnitSphere E) :
    basepointReflection b x (b : E) = (x : E) :=
  Submodule.reflection_sub (by rw [UnitSphere.norm_coe, UnitSphere.norm_coe])

/--
@isnad1 id=involuti.0h3v.s7.d16fd5e44c22 from=translated src=- shape=cbd6a44b vocab=4b0be855
-/
theorem basepointReflection_involutive (b x : UnitSphere E) :
    Function.Involutive (basepointReflection b x) :=
  Submodule.reflection_involutive _

/-- The basepoint reflection also sends the second point to the first.
@isnad1 id=eq.0h3v.s8.74e481cda588 from=translated src=- shape=eabeb8cf vocab=d132fd10
-/
theorem basepointReflection_apply_snd (b x : UnitSphere E) :
    basepointReflection b x (x : E) = (b : E) := by
  conv_lhs => rw [← basepointReflection_apply_fst b x]
  exact basepointReflection_involutive b x (b : E)

/-- The self-homeomorphism of the unit sphere induced by the reflection swapping
`b` and `x`.  WARNING: orientation-reversing; see the module docstring.-/
def rotateToBasepointHomeomorph (b x : UnitSphere E) : UnitSphere E ≃ₜ UnitSphere E :=
  unitSphereHomeomorphOfLinearIsometryEquiv (basepointReflection b x)

/--
@isnad1 id=eq.0h3v.s8.5ce5e0debb7d from=translated src=- shape=99a12c0f vocab=46b88a20
-/
theorem rotateToBasepointHomeomorph_fst (b x : UnitSphere E) :
    rotateToBasepointHomeomorph b x b = x :=
  Subtype.ext (basepointReflection_apply_fst b x)

end Submission
