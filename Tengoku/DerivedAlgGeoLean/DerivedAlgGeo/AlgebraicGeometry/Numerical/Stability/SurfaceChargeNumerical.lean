/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Divisorial.Coordinates
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.TwistedChern

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Surface charge coordinates from numerical variety data

This is the numerical adapter for `ChargeCoordinates`.  The pure
charge polynomial lives in `SurfaceCharge.lean`; this file supplies both the
untwisted view and the general `BField`-twisted view from
`NumericalVarietyData` and `Polarization`.
-/

open AlgebraicGeometry.Numerical

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates

noncomputable section

universe u v

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

/-- The real rank coordinate induced by a numerical surface presentation.-/
noncomputable def rankHom (V : NumericalVarietyData 2 A N) : N →+ ℝ :=
  (Int.castAddHom ℝ).comp V.rank

/-- The degree coordinate induced by a numerical surface presentation and a polarisation.-/
noncomputable def degreeHom (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) : N →+ ℝ :=
  AddMonoidHom.mk' (fun E => ((degH V P E : ℚ) : ℝ)) (by
    intro E F
    rw [degH_add]
    push_cast
    rfl)

/-- The `∫ ch₂` coordinate induced by a numerical surface presentation.-/
noncomputable def chTwoHom (V : NumericalVarietyData 2 A N) : N →+ ℝ :=
  AddMonoidHom.mk' (fun E => ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ)) (by
    intro E F
    rw [V.chComp_add, map_add]
    push_cast
    rfl)

/-- The twisted degree `∫ ch₁^B · H`, bundled additively.-/
noncomputable def degreeBHom (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) : N →+ ℝ :=
  AddMonoidHom.mk'
    (fun E => ((V.ring.degree (chBComp V B E 1 * P.cls) : ℚ) : ℝ))
    (by
      intro E F
      rw [chBComp_add, add_mul, map_add]
      push_cast
      rfl)

/-- The twisted top component `∫ ch₂^B`, bundled additively.-/
noncomputable def chTwoBHom (V : NumericalVarietyData 2 A N)
    (B : BField V.ring) : N →+ ℝ :=
  AddMonoidHom.mk'
    (fun E => ((V.ring.degree (chBComp V B E 2) : ℚ) : ℝ))
    (by
      intro E F
      rw [chBComp_add, map_add]
      push_cast
      rfl)

/-- This is the coercion step that exposes the integer rank to the charge polynomial.
@isnad1 id=eq.0h4v.s7.0d9315997a53 from=translated src=- shape=603915be vocab=4be05f54
-/
@[simp]
theorem rankHom_apply (V : NumericalVarietyData 2 A N) (E : N) :
    rankHom V E = (V.rank E : ℝ) := rfl

/-- This keeps consumers independent of the implementation of the bundled degree map.
@isnad1 id=eq.0h5v.s6.8032186e8923 from=translated src=- shape=45b25c75 vocab=e23ac491
-/
@[simp]
theorem degreeHom_apply (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    degreeHom V P E = ((degH V P E : ℚ) : ℝ) := rfl

/-- Applying `chTwoHom` is integration of the codimension-two Chern character.
@isnad1 id=eq.0h4v.s7.9cc75f16ea42 from=translated src=- shape=41d50917 vocab=b7fb2226
-/
@[simp]
theorem chTwoHom_apply (V : NumericalVarietyData 2 A N) (E : N) :
    chTwoHom V E = ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := rfl

/-- Evaluation of the bundled twisted `H`-degree.
@isnad1 id=eq.0h6v.s8.c361584247f7 from=translated src=- shape=5dc3e262 vocab=5b80db33
-/
@[simp]
theorem degreeBHom_apply (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) (E : N) :
    degreeBHom V P B E =
      ((V.ring.degree (chBComp V B E 1 * P.cls) : ℚ) : ℝ) := rfl

/-- Evaluation of the bundled integrated twisted second component.
@isnad1 id=eq.0h5v.s7.621eaa268465 from=translated src=- shape=efdd5984 vocab=1881492b
-/
@[simp]
theorem chTwoBHom_apply (V : NumericalVarietyData 2 A N)
    (B : BField V.ring) (E : N) :
    chTwoBHom V B E = ((V.ring.degree (chBComp V B E 2) : ℚ) : ℝ) := rfl

/-! ### The derived view of a numerical presentation -/

/-- The surface charge coordinates extracted from `NumericalVarietyData` and a polarisation.-/
noncomputable def ofNumericalData (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) : ChargeCoordinates N where
  rank := rankHom V
  degree := degreeHom V P
  chTwo := chTwoHom V
  hyperplaneSquare := ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ)

/-- Surface charge coordinates extracted after twisting by an arbitrary
numerical `B`-field.-/
noncomputable def ofNumericalDataB (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) : ChargeCoordinates N where
  rank := rankHom V
  degree := degreeBHom V P B
  chTwo := chTwoBHom V B
  hyperplaneSquare := ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ)

/-- The derived-view rank coordinate agrees with the variety presentation.
@isnad1 id=eq.0h5v.s7.35c382986f28 from=translated src=- shape=a6a87fef vocab=46505412
-/
@[simp]
theorem ofNumericalData_rank (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    (ofNumericalData V P).rank E = (V.rank E : ℝ) := rfl

/-- The derived-view degree coordinate agrees with `degH`.
@isnad1 id=eq.0h5v.s7.136bb1f1d727 from=translated src=- shape=22c1ab9b vocab=35ba10ae
-/
@[simp]
theorem ofNumericalData_degree (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    (ofNumericalData V P).degree E = ((degH V P E : ℚ) : ℝ) := rfl

/-- The derived-view top Chern-character coordinate is the integrated `ch₂`.
@isnad1 id=eq.0h5v.s7.3b18898b4680 from=translated src=- shape=5cedd1b3 vocab=24873a59
-/
@[simp]
theorem ofNumericalData_chTwo (V : NumericalVarietyData 2 A N) (P : Polarization V.ring)
    (E : N) :
    (ofNumericalData V P).chTwo E =
      ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := rfl

/-- The untwisted view retains the polarisation square from the numerical ring.
@isnad1 id=eq.0h4v.s7.1e9a5b133861 from=translated src=- shape=d6aaf8eb vocab=5e444d6f
-/
@[simp]
theorem ofNumericalData_hyperplaneSquare (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) :
    (ofNumericalData V P).hyperplaneSquare =
      ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ) := rfl

/-- A `B`-field twist leaves the rank component unchanged.
@isnad1 id=eq.0h6v.s7.e3a779d003d3 from=translated src=- shape=94c5739d vocab=072baa60
-/
@[simp]
theorem ofNumericalDataB_rank (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) (E : N) :
    (ofNumericalDataB V P B).rank E = (V.rank E : ℝ) := rfl

/-- The general `B`-field view exposes `∫H ch₁^B`.
@isnad1 id=eq.0h6v.s8.2993b4a82321 from=translated src=- shape=64f33707 vocab=cb2d509b
-/
@[simp]
theorem ofNumericalDataB_degree (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) (E : N) :
    (ofNumericalDataB V P B).degree E =
      ((V.ring.degree (chBComp V B E 1 * P.cls) : ℚ) : ℝ) := rfl

/-- The general `B`-field view exposes `∫ch₂^B`.
@isnad1 id=eq.0h6v.s7.81cf38d8b694 from=translated src=- shape=b4c65efe vocab=eeb2d579
-/
@[simp]
theorem ofNumericalDataB_chTwo (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) (E : N) :
    (ofNumericalDataB V P B).chTwo E =
      ((V.ring.degree (chBComp V B E 2) : ℚ) : ℝ) := rfl

/-- The general `B`-field view retains the chosen polarisation square.
@isnad1 id=eq.0h5v.s7.4ee6993e0856 from=translated src=- shape=7bccc94c vocab=f2804f56
-/
@[simp]
theorem ofNumericalDataB_hyperplaneSquare (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (B : BField V.ring) :
    (ofNumericalDataB V P B).hyperplaneSquare =
      ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ) := rfl

/-! ### Compatibility of `B` and `βH` notation -/

/-- At `B = βH`, the general twisted degree is the scalar-twist formula.
@isnad1 id=eq.0h6v.s7.ed5990dc1364 from=translated src=- shape=138f6aeb vocab=d63216f2
-/
theorem ofNumericalDataB_along_degree (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (β : ℚ) (E : N) :
    (ofNumericalDataB V P (BField.along P β)).degree E =
      ((ofNumericalData V P).twistByScalar (β : ℝ)).degree E := by
  simp only [ofNumericalDataB_degree, ChargeCoordinates.twistByScalar_degree,
    ofNumericalData_degree, ofNumericalData_rank]
  rw [chBComp_one, BField.along_cls, V.chComp_zero, sub_mul, map_sub]
  have hdeg : V.ring.degree (V.chComp E 1 * P.cls) = degH V P E := by
    simp [degH]
  rw [hdeg]
  have hscalar :
      algebraMap ℚ A (V.rank E : ℚ) * (algebraMap ℚ A β * P.cls) * P.cls =
        algebraMap ℚ A (β * (V.rank E : ℚ)) * P.cls ^ 2 := by
    rw [map_mul]
    ring
  rw [hscalar, NumericalRingData.degree_algebraMap_mul]
  push_cast
  rw [ofNumericalData_hyperplaneSquare]
  ring

/-- At `B = βH`, the general twisted second component is the scalar-twist formula.
@isnad1 id=eq.0h6v.s7.b64491c1c362 from=translated src=- shape=138f6aeb vocab=72532b3d
-/
theorem ofNumericalDataB_along_chTwo (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (β : ℚ) (E : N) :
    (ofNumericalDataB V P (BField.along P β)).chTwo E =
      ((ofNumericalData V P).twistByScalar (β : ℝ)).chTwo E := by
  simp only [ofNumericalDataB_chTwo, ChargeCoordinates.twistByScalar_chTwo,
    ofNumericalData_chTwo, ofNumericalData_degree, ofNumericalData_rank]
  rw [chBComp_two, BField.along_cls, V.chComp_zero, map_add, map_sub]
  have hlinear :
      V.chComp E 1 * (algebraMap ℚ A β * P.cls) =
        algebraMap ℚ A β * (V.chComp E 1 * P.cls) := by ring
  rw [hlinear, NumericalRingData.degree_algebraMap_mul]
  have hdeg : V.ring.degree (V.chComp E 1 * P.cls) = degH V P E := by
    simp [degH]
  rw [hdeg]
  have hquadratic :
      algebraMap ℚ A (1 / 2) * algebraMap ℚ A (V.rank E : ℚ) *
          (algebraMap ℚ A β * P.cls) ^ 2 =
        algebraMap ℚ A ((1 / 2) * (V.rank E : ℚ) * β ^ 2) * P.cls ^ 2 := by
    simp only [mul_pow, map_mul, map_pow]
    ring
  rw [hquadratic, NumericalRingData.degree_algebraMap_mul]
  push_cast
  rw [ofNumericalData_hyperplaneSquare]
  ring

/-- Switching between the general notation `ch^B` and the rank-one notation
`ch^(βH)` does not change the central charge.
@isnad1 id=eq.0h7v.s7.aeadb495f857 from=translated src=- shape=6e36baf8 vocab=313dcc1f
-/
theorem centralCharge_ofNumericalDataB_along_eq (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (a : ℝ) (β : ℚ) (E : N) :
    (ofNumericalDataB V P (BField.along P β)).centralCharge a E =
      ((ofNumericalData V P).twistByScalar (β : ℝ)).centralCharge a E := by
  simp only [ChargeCoordinates.centralCharge, AddMonoidHom.mk'_apply]
  rw [ofNumericalDataB_along_degree, ofNumericalDataB_along_chTwo]
  simp only [ofNumericalDataB_hyperplaneSquare, ofNumericalDataB_rank,
    ChargeCoordinates.twistByScalar_hyperplaneSquare,
    ChargeCoordinates.twistByScalar_rank, ofNumericalData_hyperplaneSquare,
    ofNumericalData_rank]

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates
