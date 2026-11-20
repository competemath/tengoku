/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Literal complex nodes and the circle-valued representation

The adapters below prove that the representation does not restrict the admissible nodes,
the evaluation domain, the objective, or the meaning of global minimization and regularity.
They do not prove the full minimizer classification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- Construct a circle-valued family from any distinct complex unit-modulus nodes.-/
def NodeFamily.ofCoordinates (z : Fin n → ℂ) (hunit : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) : NodeFamily n where
  point i := ⟨z i, mem_sphere_zero_iff_norm.mpr (hunit i)⟩
  injective := fun _ _ h => hinj (congrArg (fun w : Circle => (w : ℂ)) h)

/--
@isnad1 id=eq.2h2v.s5.62ab54dc3bec from=translated src=- shape=d68b2f01 vocab=02f72ddc
-/
@[simp] lemma NodeFamily.coordinates_ofCoordinates (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    (NodeFamily.ofCoordinates z hunit hinj).coordinates = z :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.7e1078d5ef8c from=translated src=- shape=82f88364 vocab=48edaa73
-/
@[simp] lemma NodeFamily.ofCoordinates_coordinates (nodes : NodeFamily n) :
    NodeFamily.ofCoordinates nodes.coordinates nodes.norm_coordinates
      nodes.coordinates_injective = nodes := by
  cases nodes
  rfl

/-- The same literal supremum, before packaging the nodes as a `NodeFamily`.-/
def complexAmplification (z : Fin n → ℂ) : ℝ :=
  sSup (Set.range (fun w : Circle => lebesgueFunction z (w : ℂ)))

/--
@isnad1 id=eq.0h2v.s5.e40485b30332 from=translated src=- shape=97ee005e vocab=21b26ea9
-/
lemma complexAmplification_eq_sSup_image (z : Fin n → ℂ) :
    complexAmplification z = sSup (lebesgueFunction z '' {w : ℂ | ‖w‖ = 1}) := by
  unfold complexAmplification
  congr 1
  ext b
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(w : ℂ), Circle.norm_coe w, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(⟨w, mem_sphere_zero_iff_norm.mpr hw⟩ : Circle), rfl⟩

/--
@isnad1 id=eq.0h2v.s3.f6c8cdcfb900 from=translated src=- shape=bddd810f vocab=b3e4efa8
-/
lemma complexAmplification_coordinates (nodes : NodeFamily n) :
    complexAmplification nodes.coordinates = amplification nodes :=
  rfl

/--
@isnad1 id=eq.2h2v.s5.44de52cb5cf8 from=translated src=- shape=03c40810 vocab=007c8fd7
-/
lemma amplification_ofCoordinates (z : Fin n → ℂ) (hunit : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    amplification (NodeFamily.ofCoordinates z hunit hinj) = complexAmplification z :=
  rfl

/-- Minimization against every injective complex family with unit-modulus nodes.-/
def IsComplexMinimizer (z : Fin n → ℂ) : Prop :=
  ∀ other : Fin n → ℂ, (∀ i, ‖other i‖ = 1) → Function.Injective other →
    complexAmplification z ≤ complexAmplification other

/--
@isnad1 id=iff.0h2v.s3.ae02f636ac90 from=translated src=- shape=42d7f2e4 vocab=17cd0455
-/
lemma isComplexMinimizer_coordinates_iff (nodes : NodeFamily n) :
    IsComplexMinimizer nodes.coordinates ↔ IsMinimizer nodes := by
  constructor
  · intro h other
    exact h other.coordinates other.norm_coordinates other.coordinates_injective
  · intro h other hunit hinj
    exact h (NodeFamily.ofCoordinates other hunit hinj)

/--
@isnad1 id=iff.2h2v.s5.a4a35791ba37 from=translated src=- shape=ecc6c5eb vocab=fca34d36
-/
lemma isComplexMinimizer_ofCoordinates_iff (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    IsComplexMinimizer z ↔ IsMinimizer (NodeFamily.ofCoordinates z hunit hinj) :=
  by simpa only [NodeFamily.coordinates_ofCoordinates] using
    isComplexMinimizer_coordinates_iff (NodeFamily.ofCoordinates z hunit hinj)

/-- The exact complex regular-polygon statement, with scalar rotation and arbitrary enumeration.-/
def IsComplexRegularRotation (z : Fin n → ℂ) : Prop :=
  ∃ rotation : ℂ, ‖rotation‖ = 1 ∧ ∃ permutation : Equiv.Perm (Fin n),
    ∀ i, z i = rotation * (Circle.exp
      (2 * Real.pi * (((permutation i).val : ℝ) / (n : ℝ))) : ℂ)

/--
@isnad1 id=iff.0h2v.s3.4a4eb11adb56 from=translated src=- shape=42d7f2e4 vocab=633ff248
-/
lemma isComplexRegularRotation_coordinates_iff (nodes : NodeFamily n) :
    IsComplexRegularRotation nodes.coordinates ↔ IsRegularRotation nodes := by
  constructor
  · rintro ⟨rotation, hunit, permutation, h⟩
    let r : Circle := ⟨rotation, mem_sphere_zero_iff_norm.mpr hunit⟩
    refine ⟨r, permutation, ?_⟩
    intro i
    apply Circle.coe_injective
    exact h i
  · rintro ⟨rotation, permutation, h⟩
    refine ⟨(rotation : ℂ), Circle.norm_coe rotation, permutation, ?_⟩
    intro i
    exact congrArg (fun w : Circle => (w : ℂ)) (h i)

/--
@isnad1 id=iff.2h2v.s5.54f58ee9d3ac from=translated src=- shape=ecc6c5eb vocab=d51f03c8
-/
lemma isComplexRegularRotation_ofCoordinates_iff (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    IsComplexRegularRotation z ↔ IsRegularRotation (NodeFamily.ofCoordinates z hunit hinj) :=
  by simpa only [NodeFamily.coordinates_ofCoordinates] using
    isComplexRegularRotation_coordinates_iff (NodeFamily.ofCoordinates z hunit hinj)

end

end UnitCircleInterpolation
